(*** MODULES *****************************************************************)
module St = Statistics
module S = Strategy
module C = Cache

(*** OPENS *******************************************************************)
open Yices
open Yicesx
open Rewriting
open Constraint

(*** EXCEPTIONS **************************************************************)
exception Success of (Rules.t * Rules.t)

exception Restart

(*** TYPES *******************************************************************)
type flags = {
 d        : bool ref ; (* debug mode *)
 es       : Constraint.t list ref ;
 json     : bool ref; (* output json result and statistics *)
 k        : (int -> int) ref;  (* k TRSs are chosen in an iteration *)
 n        : int ref;  (* how many equations are (at most) selected *)
 ordered_completion : bool ref;
 strategy : Strategy.t ref;
 tmp      : int ref; (* various purpose parameter *)
 output_tproof : bool ref;
 check_subsumption : bool ref;
}
(*** GLOBALS *****************************************************************)
(* k functions *)
let k_default = fun i -> if i < 3 then 6 else 2
let k2 _ = 2

(* flags *)
let flags = {
 d   = ref false;
 es = ref [] ;
 json=ref false;
 k   = ref k_default;
 n  = ref 12;
 ordered_completion = ref false;
 strategy = ref S.strategy_red;
 tmp = ref 19;
 output_tproof = ref false;
 check_subsumption = ref false
}

let last_model = ref None

(* store overlaps *)
let ht_ols : (Rule.t * Rule.t, Rule.t list) Hashtbl.t = 
 Hashtbl.create 100;;

let ht_overlaps : (int*int,Rule.t list) Hashtbl.t = Hashtbl.create 256

let debug = ref false

let interreduce = ref false

let really_new = ref [2;3;2;1;1;1];;

(* if two or more strategies used in parallel, offset for rule variables *)
let offset = 8

let iterations_after_restart = ref 0

let sizes = ref []

let all_overlap_list = ref []

let rewrite_trace = ref []

let rewrite_traces_eq = ref []


(*** FUNCTIONS ***************************************************************)
(* access functions to global parameters *)
let k i = !(flags.k) i

let termination_strategy _ = 
 match !(flags.strategy) with 
  | [] -> failwith "no termination strategy found"
  | (s,_, _) :: _ -> s
;;

let constraints _ = 
 match !(flags.strategy) with 
  | [] -> failwith "no constraints found"
  | (_,cs,_) :: _ -> cs
;;

let max_constraints _ =
 match !(flags.strategy) with
  | [] -> failwith "no max constraints found"
  | (_,_,ms) :: _ -> ms
;;

let use_maxsat _ = max_constraints () <> []

let has_comp () = List.mem S.Comp (constraints ())

let pop_strategy _ = 
 if !(flags.d) then Format.printf "pop strategy\n%!";
 match !(flags.strategy) with
  | [] -> failwith "no strategy left in pop"
  | [s] -> ()
  | _ :: ss -> flags.strategy := ss
;;

let t_strategies _ = List.map (fun (ts,_,_) -> ts) !(flags.strategy)

(* * AUXILIARY  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let (<.>) f g = fun x -> f (g x)

let sort_by f xs = List.sort (fun x y -> f x - f y) xs

let uncurry f (x,y) = f x y

(* uniform rule renaming to avoid many variant checks *)
let normalize (s,t) =
 let s',t' =  Term.rename s, Term.rename t in
 if s' < t' then
  Variant.rename_rule [] (s,t)
 else
  Variant.rename_rule [] (t,s)
;;

(* * CONSTRAINT STUFF * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let rec translate_to_smt ctx = function
  | TRS rr -> C.find_trs_var rr
  | R r -> C.find_rule r
  | NEG cn -> mk_not ctx (translate_to_smt ctx cn)
  | AND cs -> ybig_and ctx [ translate_to_smt ctx ci | ci <- cs ]
  | OR cs ->  ybig_or ctx [ translate_to_smt ctx ci | ci <- cs ]
  | BOT -> yfalse ctx
  | TOP -> ytrue ctx


let smt_constraint ctx c = Hashtbl.find C.ht_cvars c

(* translation takes virtually no time *)
(*let smt_constraint ctx = St.take_time St.t_translate (smt_constraint ctx)*)

let t ctx c = mk_not ctx (smt_constraint ctx c)

(* * CONSTRAINED EQUALITY OPERATIONS  * * * * * * * * * * * * * * * * * * * * *)
let rec satisfies rr = function 
 | TRS rr' -> C.contains rr rr'
 | R r -> List.mem r (C.trs_of_index rr)
 | NEG cn -> not (satisfies rr cn)
 | AND cs -> List.for_all (fun ci -> satisfies rr ci) cs
 | OR cs -> List.exists (fun ci -> satisfies rr ci) cs
 | BOT -> false
 | TOP -> true

let to_cc es = 
 let rec to_rs rs = big_and (List.map (fun r -> R r) rs) in
 List.map (fun (st,rs) -> (st, (*to_rs rs*) TOP)) es 

let cc_of_rr rr cc = [ st | st,ci <- cc; satisfies rr ci ]

let cc_of_rr rr = St.take_time St.t_project (cc_of_rr rr)

let rr_of_cc cc = []

let add_rewrite_trace (s,t) rls (s',t') =
 if not (List.mem ((s,t), rls, (s',t')) !rewrite_trace) then (
  rewrite_trace := ((s,t), rls, (s',t')) :: ((s',t'), rls, (s,t)) :: !rewrite_trace;
  rewrite_traces_eq := (s,t)::(s',t')::!rewrite_traces_eq
 )
;;

(* normalization with respect to TRS with index n. Returns pair (ff,cs') where ff
   are newly generated eqs and cs' \subseteq cs is set of irreducible eqs 
*)
let get_normalized n cs =
(* let ht = Hashtbl.create 256 in*)
 let rr = C.redtrs_of_index n in
 let rec cc_norm_rr (irrdcbl, news) = function
  | [] -> (irrdcbl, news)
  | ((s,t),c) :: cc ->
   (*Format.printf "cc_norm: trest %a ... %!" Rule.print (s,t);*)
   let used_s, nf_s = nf_with(*_ht ht*) rr s in
   let used_t, nf_t = nf_with(*_ht ht*) rr t in
   (*Format.printf "nfs computed\n%!";*)
   let rs' = Listx.unique (used_s@used_t) in
   let rs = List.map (fun r -> R r) rs' in
   if nf_s = nf_t then cc_norm_rr (irrdcbl, news) cc
   else 
    let c' = TOP (*if Rule.size (s,t) < 10 then TOP else big_and (c::rs)*) in
    if (nf_s = s) && (nf_t = t) then
     let irrdcbl' = ((s,t),c') :: irrdcbl in 
     cc_norm_rr (irrdcbl', news) cc (* no progress *)
    else
     let nf_s',nf_t' = normalize (nf_s,nf_t) in (
     if has_comp () then add_rewrite_trace (s,t) rs' (nf_s',nf_t');
     let news' = ((nf_s',nf_t'), c') :: news in 
     cc_norm_rr (irrdcbl, news') cc
    )
 in cc_norm_rr ([],[]) cs
;;    
   
let get_normalized rr = St.take_time St.t_norm (get_normalized rr)

let go_away lr =
 [ (st',ee) | (st, ee, st') <-  !rewrite_trace; lr = st ]
;;

(* insert constrained equality in set *)
let rec insert (st,c) = function
  | [] -> [(st,c)]
  | (uv,d) :: ls when st = uv -> (st, c <|> d) :: ls
  | (uv,d) :: ls -> (uv,d) :: (insert (st,c) ls)

let insert x = St.take_time St.t_insert (insert x)

let rec insert_all xs ys =
 match xs with
  | [] -> ys
  | x::xs -> insert_all xs (x::ys)
;;


(* union of two constrained equality sets *)
let union_cc ls = 
 let rec union1 acc = function
   | [] -> acc
   | h :: tl -> union1 (insert h acc) tl
 in union1 [] ls 

(* emptiness of projection test *)
(* test whether this is faster than emptiness of projection check *)
let joins_all rr cc = 
 List.for_all (fun ((s,t),_) -> nf rr s = (nf rr t)) cc

let joins_all rr = St.take_time St.t_project (joins_all rr)

let joins_all' rr cc =
 List.for_all (fun (s,t) -> nf rr s = (nf rr t)) cc

let is_saturated (rr,ee) cc =
 let covered s t =
  let s',t' = nf rr s, nf rr t in
  s' = t' || (List.exists (Rule.is_instance (s',t')) ee)
 in
 List.for_all (fun (s,t) -> nf rr s = (nf rr t)) cc
;;

(* rr is the current TRS, ee the respective irreducible equations *)
let success (rr,ee) cc =
 if !(flags.ordered_completion) then is_saturated (rr,ee) cc 
 else joins_all' rr cc
;;

let mirror cc = List.rev_append cc [((r,l),c) | ((l,r),c) <- cc]

(* * CRITICAL PAIRS * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let log_select ff_aa =
 Format.printf "selected: %i\n %!" (List.length ff_aa);
 Listx.print Constraint.print_ceq "\n@." ff_aa;
 Format.printf "\n%!"
;;

(* selection of small critical pairs *)
let select cc n d = 
 let small = Listx.unique (union_cc [ e,c | e,c <- cc; Rule.size e < d]) in
 let aa = sort_by (fun (x,_) -> Rule.size x) small in
 (*Format.printf "to choose from: %i\n %!" (List.length aa);
 Listx.print Constraint.print_ceq "\n@." aa;*)
 let aa,aa' = Listx.split_at_most n aa in 
 let pp = Listset.diff cc aa in 
 if !(flags.d) then log_select aa;
 (aa,pp)

let select_count i = !(flags.n)

(* obtain and normalize overlaps *)
let overlaps rr =
 let add r1 r2 =
   if Hashtbl.mem ht_ols (r1,r2) then [] else
    let os = List.map normalize (Overlap.cp [r1; r2]) in
    Hashtbl.add ht_ols (r1,r2) os;
   os
 in [ e,[r1;r2] | r1 <- rr; r2 <- rr; e <- add r1 r2]

let overlaps  = St.take_time St.t_overlap overlaps

let unique p =
 let rec unique acc = function
  | [] -> acc
  | y :: xs -> 
   let acc' = if List.for_all (fun x -> not (p x y)) xs then y::acc else acc in
   unique acc' xs 
 in unique []
;;

 (* heuristic to reduce eqs used in overlap computation *)
let use_for_overlaps (s,t) =
 let no_subterm = not (Term.is_subterm s t || Term.is_subterm t s) in
 let unorientable = not (C.was_oriented (s,t)) in
 no_subterm && unorientable
;;

let eqs_overlaps rr ee =
 let subsumed e = List.exists (fun (e',_) -> Rule.is_instance e e' && not (Rule.variant e e')) ee in
 let ee' = unique Rule.variant [ e | e,_ <- mirror ee; use_for_overlaps e; not (subsumed e) ] in
 if !(flags.d) then
  Format.printf " use eqs for overlaps:@. %a\n" Rules.print ee';
 let add r1 r2 =
   try Hashtbl.find ht_ols (r1,r2) with Not_found -> (
    let os = List.map normalize (Overlap.cp [r1; r2]) in
    Hashtbl.add ht_ols (r1,r2) os;
    all_overlap_list := List.rev_append (List.map (fun st -> (st,(r1,r2))) os) !all_overlap_list;
   os)
 in
 let os = [ e,[r1;r2] | r1 <- ee'; r2 <- rr; e <- add r1 r2] in
 os @ [ e,[r1;r2] | r1 <- rr; r2 <- ee'; e <- add r1 r2]
;;

let all_overlaps rr ee =
 let add r1 r2 =
   try Hashtbl.find ht_ols (r1,r2) with Not_found -> (
    let os = List.map normalize (Overlap.cp [r1; r2]) in
    Hashtbl.add ht_ols (r1,r2) os;
    all_overlap_list := List.rev_append (List.map (fun st -> (st,(r1,r2))) os) !all_overlap_list;
   os)
 in 
 let os = [ e,[r1;r2] | r1 <- rr; r2 <- rr; e <- add r1 r2] in
 if !(flags.ordered_completion) then eqs_overlaps rr ee @ os else os
;;

let all_overlaps rr = St.take_time St.t_overlap (all_overlaps rr)

(* * FIND TRSS  * * *  * * * * * * * * * * * * * * * *  * * * * * * * * * * * *)
(* Yices vars and assertions for new TRSs *)
let assert_trs_vars ctx =
 let add n _ ctx =
  if Hashtbl.mem C.ht_trsvars n then
   ctx
  else (
   let v = mk_fresh_bool_var ctx in
   Hashtbl.add C.ht_trsvars n v;
   let rr = List.map C.find_rule (C.trs_of_index n) in
   if rr = [] then ctx
   else
    let cr = ybig_and ctx rr in
    let _ = assert_simple ctx (mk_eq ctx v cr) in
    ctx)
 in Hashtbl.fold add C.ht_itrss ctx
;;

(* Yices vars and assertions for new constraints *)
let rec assert_constraint_vars ctx ce =
  let add (_,c) =
   if not (Hashtbl.mem C.ht_cvars c) then
    let v = mk_fresh_bool_var ctx in
    Hashtbl.add C.ht_cvars c v;
    let c' = translate_to_smt ctx c in
    assert_simple ctx (mk_eq ctx v c');
  in List.iter add ce
;;

(* update context: write conditions for new rules, TRSs, constraints 
   (these assertions are permanent, they will not be retracted) *)
let update_context ctx cc =
  let es = List.map fst cc in
  let rls = es @ [ t,s | s,t <- es ] in
  C.store_rule_vars ctx rls; (* store missing ones *)
  if has_comp () then ( 
   C.store_eq_vars ctx (rls @ !rewrite_traces_eq);
   rewrite_traces_eq := []
  )(*;
  let _ = assert_trs_vars ctx in
  assert_constraint_vars ctx cc  in *)
  (* assert termination constraints *)
  (*Strategy.assert_constraints s ctx cc*)
;;

let update_context ctx = St.take_time St.t_upd (update_context ctx)

let c_maxcomp ctx cc =
 let exp ((l,r),c) = mk_or ctx [|C.find_rule (l,r);C.find_rule (r,l) |] in
 List.iter (fun ce -> ignore (assert_weighted ctx (exp ce) 1L)) cc
;;

let c_not_oriented ctx cc =
 let exp ((l,r),c) = 
  yand ctx (ynot ctx (C.find_rule (l,r))) (ynot ctx (C.find_rule (r,l))) 
 in
 List.iter (fun ce -> ignore (assert_weighted ctx (exp ce) 1L)) cc
;;


(* case for Red *)
let redc : (int * int, bool) Hashtbl.t = Hashtbl.create 512

let reducible : (int,Yices.expr) Hashtbl.t = Hashtbl.create 512

let is_reducible ctx cc (s,t) =
(* Format.printf "check reducibility: %a\n%!" Rule.print (s,t);*)
 let j = Constraint.idx (s,t) in
 try Hashtbl.find reducible j with Not_found -> (
   let reduces_st rl =
   (*   let i = Constraint.idx rl in*)
   (*try Hashtbl.find redc (j, i) with Not_found ->*) (
     let red = Rewriting.reducible_with [rl] in
     let b = Rule.is_rule rl && (red t || red s) in
     (*Hashtbl.add redc (j, i) b;*) b)
   in
   (* let cs = [ (l,r) | (l,r),_ <- mirror cc; reduces_st (l,r) ] in*)
   let b = ybig_or ctx [ C.find_rule (l,r) | (l,r),_ <- mirror cc; reduces_st (l,r)] in
   Hashtbl.add reducible j b;
   b
   )
;;

let is_reducible ctx cc = St.take_time St.t_tmp2 (is_reducible ctx cc)

let rlred ctx cc (s,t) =
  let j = Constraint.idx (s,t) in
  let redcbl rl =
     let i = Constraint.idx rl in
     (*try Hashtbl.find redc (j, i) with Not_found ->*) (
      let red = Rewriting.reducible_with [rl] in
      let is_rule (l,r) = Rule.is_rule (l,r) && (not (Term.is_subterm l r)) in
      let b = is_rule rl && (red t || red s) in
      Hashtbl.add redc (j, i) b; b)
  in
  let reducing = [(l,r) | (l,r),_ <- mirror cc; redcbl (l,r) ] in
(*  Format.printf "to reduce %a, need one of %a\n%!" Rule.print (s,t) Rules.print reducing;*)
  let f = ybig_or ctx [ C.find_rule (l,r) | (l,r) <- reducing ] in
(*  pp_expr f;*)
  f
;;

let c_red ctx cc =
  let red ((s,t),_) = ignore (assert_simple ctx (rlred ctx cc (s,t))) in
  List.iter red cc
;;

(*let c_red ctx = St.take_time St.t_tmp1 (c_red ctx)*)

let c_max_red ctx cc =
  let red ((s,t),_) = ignore (assert_weighted ctx (rlred ctx cc (s,t)) 1L) in
  List.iter red cc
;;
let c_max_red ctx = St.take_time St.t_tmp1 (c_max_red ctx)

(* case for CPred *)
let c_cpred ctx cc =
 Hashtbl.clear reducible;
 let mcc = mirror cc in
 let r_c = [ rl | rl,_ <- mcc; Rule.is_rule rl ] in
 let rule, red = C.find_rule, is_reducible ctx cc in
 let both rl rl' = yand ctx (rule rl) (rule rl') in
 let mcc = List.map fst mcc in
 let c2 = [ yimp ctx (both rl rl') (red st) | (st,(rl,rl')) <- !all_overlap_list] in
 List.iter (fun c -> ignore (assert_weighted ctx c 2L)) c2;
;;
let c_cpred ctx = St.take_time St.t_tmp1 (c_cpred ctx)


(* case for Comp2 *)
let c_comp ctx cc =
 let cc = List.map fst cc in
 let all_eqs ee = ybig_and ctx (List.map C.find_eq ee) in
 let dec e ee =
  let x = C.find_eq_weight e in
  let gts = [mk_gt ctx x (C.find_eq_weight (normalize e')) | e' <- ee] in
  ybig_and ctx gts
 in
 let red (s,t) =
  let es = go_away (s,t) in
  if es  = [] then yfalse ctx
  else ybig_or ctx [ ybig_and ctx [C.find_eq e; all_eqs ee; dec e ee] | (e, ee) <- es ] 
 in
 let considered (s,t) =
  if s <> t then (
   let c = ybig_or ctx [C.find_rule (s,t); C.find_rule (t,s); red (s,t)] in
   assert_simple ctx (yimp ctx (C.find_eq (s,t)) c);
  )
 in
 assert_simple ctx (all_eqs (List.map fst !(flags.es)));
 List.iter considered cc;
;;

let c_comp ctx = St.take_time St.t_tmp1 (c_comp ctx)

(* Weighted assertions for maxsat. 
 Note that these assertions will be retracted before the next iteration! 
*)

let trs_constraints ctx cc =
 let assert_c = function
   | S.Red -> c_red ctx cc
   | S.Empty -> ()
   | S.Comp -> (*c_red ctx cc;*) c_comp ctx cc
 in List.iter assert_c (constraints ());
 let assert_mc = function
   | S.Oriented -> c_maxcomp ctx cc
   | S.NotOriented -> c_not_oriented ctx cc
   | S.MaxRed -> c_max_red ctx cc
   | S.CPsRed -> c_cpred ctx cc
   | S.MaxEmpty -> ()
 in List.iter assert_mc (max_constraints ())
;;

let check_trs ctx =
 let rs, th = Read.read_trs "z22.trs" in
 let es = Rules.rpl_spcl_char rs in
 push ctx;
 let b = List.fold_left (fun b rl -> 
  try assert_simple ctx (C.find_rule rl); b
   with _ -> false) true es in
 (match Yices.check ctx with
  | True -> if b then Format.printf "check TRS: SAT\n%!"
  | False -> Format.printf "check TRS: UNSAT\n%!");
 pop ctx 
;;

(* block list of previously obtained TRSs *)
let rec block_trss ctx rrs cc = 
 let not_r rr = mk_not ctx (ybig_and ctx [ C.find_rule r | r <- rr ]) in
 ybig_and ctx [ not_r rr | rr,_ <- rrs; rr <> [] ]

(* find k maximal TRSs *)
let max_k ctx cc k =
 if !(flags.d) then Format.printf "K = %i\n%!" k;
   let rec max_k acc ctx cc n =
    if n = 0 then List.rev acc,ctx else (
     assert_simple ctx (block_trss ctx acc cc);
     let sat_call = if use_maxsat () then Yices.max_sat else Yices.check in
     match St.take_time St.t_sat sat_call ctx with
      | True -> 
       let m = get_model ctx in
       last_model := Some m;
       let c = if use_maxsat () then Int64.to_int (get_cost m) else 0 in
       (*Format.printf "Model %i has cost %i\n%!" n (Int64.to_int c);
       display_model m;*)
       let is_rl rl x = evaluate_in_model m x = True && (not (Rule.is_dp rl)) in
       let rr = [rl | rl,_ <- mirror cc; is_rl rl (C.find_rule rl)] in
       max_k ((rr,c)::acc) ctx cc (n-1)
      | _ -> (
        if !(flags.d) then Format.printf "no further TRS found\n%!"; 
        if (n = k && List.length !(flags.strategy) > 1) then raise Restart;
        (*if !(St.iterations) > 2 then pop_strategy (); *)
        (acc, ctx))
    )
   in
   update_context ctx cc;
   let s = termination_strategy () in
   if !(flags.d) then Format.printf "Strategy: %s\n%!" (Strategy.term_to_string s);
   St.take_time St.t_orient_constr (Strategy.assert_constraints s 0 ctx) cc;
   push ctx; (* backtrack point for Yices *)
   assert_simple ctx (Strategy.bootstrap_constraint 0 ctx cc);
   (*Format.printf "before trs constraints\n%!";
   check_trs ctx;*)
   trs_constraints ctx cc;
   (*Format.printf "after trs constraints\n%!";
   check_trs ctx;*)
   let res,ctx = max_k [] ctx cc k in
   pop ctx; (* backtrack: get rid of all assertions added since push *)
   res
;;

let max_k ctx cc = St.take_time St.t_maxk (max_k ctx cc)

(* some logging functions *)
let log_iteration i aa =
 Format.printf "Iteration %i\n%!" i;
 Format.printf "CC: %i\n %!" (List.length aa);
 Listx.print Constraint.print_ceq "\n@." aa;
 Format.printf "\n%!"
;;

let log_max_trs i j rr c =
 Format.printf "TRS %i - %i: cost %i\n %a\n@." i j c Rules.print (Variant.rename_rules rr)(*;
 Format.printf "cost %i, reduced: %a\n@." c
      Rules.print (Variant.rename_rules (Variant.right_reduce rr))*)
;;


let is_subsumed (l,r) ((s,t),_) =
 let lr,rl,st = Term.F(0,[l;r]),Term.F(0,[r;l]), Term.F(0,[s;t]) in
 if Subst.is_instance_of lr st || Subst.is_instance_of rl st then
   ((*Format.printf "%a is instance of \n %a\n%!" 
     Rule.print (l,r) Rule.print (s,t);*) true) else false
;;

let remove_subsumed cc =
 let rec remove acc = function
  | [] -> acc
  | (lr,c) :: aa ->
   try 
    let (lr',c') = List.find (is_subsumed lr) acc in
    let acc' = (lr', TOP) :: (Listx.remove (lr',c') acc) in
    remove acc' aa
   with Not_found ->
    try
     let (lr',c') = List.find (is_subsumed lr) aa in
     let aa' = (lr', TOP) :: (Listx.remove (lr',c') aa) in
     remove acc aa'
    with Not_found -> remove ((lr,c)::acc) aa
 in 
 let cc = List.sort (fun (a,_) (b,_) -> compare (Constraint.idx b) (Constraint.idx a)) cc in
 remove [] cc
;;

let remove_subsumed_in ff aa =
 let rec remove (ff_acc,aa) (lr,c) = 
  try
   let (lr',c') = List.find (is_subsumed lr) aa in
    let aa' = (lr', OR[c;c']) :: (Listx.remove (lr',c') aa) in
    (ff_acc, aa')
   with Not_found -> ((lr,c)::ff_acc,aa)
 in List.fold_left remove ([],aa) ff
;;


let remove_subsumed = St.take_time St.t_tmp1 remove_subsumed 

(* predicate to check whether run is degenerated, hence restart desired *)
let degenerated cc =
 (List.length !sizes > 10) && (List.for_all (fun x -> x > 16) (Listx.take 6 !sizes))
;;

(* main control loop *)

let init_phi aa =
  let i = !St.iterations in
  St.iterations := i + 1;
  iterations_after_restart := !iterations_after_restart + 1;
  let s = S.to_string !(flags.strategy) in
  if !(flags.d) then (
   Format.printf "iteration %i\n%!" !St.iterations;
   Format.printf "%s\n%!" (Yojson.Basic.pretty_to_string 
    (Statistics.json s (k i) (select_count i))));
  St.ces := List.length aa
;;

(* to debug termination encodings the following function can be used *)
let check_termination fs trs =
 let ce = [ st, TOP | st <- trs ] in
 let ctx = Yices.mk_context () in
 let s = termination_strategy () in
 Strategy.init s 0 ctx ce;
 update_context ctx ce;
 Strategy.assert_constraints s 0 ctx ce;
 let c = Strategy.bootstrap_constraint 0 ctx ce in
 assert_simple ctx c;
 assert_simple ctx (ybig_and ctx [ C.find_rule st | st <- trs ]);
(* dump_context ctx;*)
 match Yices.check ctx with
  | Yices.True -> (
   let m = get_model ctx in
   if not !(flags.json) then Strategy.decode 0 m s;
   true)
  | _ -> false
;;


let rec phi ctx aa =
 init_phi aa;
 let i = !St.iterations in
 let rrs = max_k ctx aa (k i) in
  let process (j,ff_all) (rr,c) =
    if !(flags.d) then log_max_trs i j rr c;
    let rr' = Variant.right_reduce rr in
    let n = C.store_trs rr in
    (*C.store_redtrs (Variant.reduce rr) n;*) (* for rewriting, use only rules with lhs in nf (?) *)
    C.store_redtrs rr' n;
    C.store_rule_vars ctx rr'; (* otherwise problems in norm *)
    if has_comp () then C.store_eq_vars ctx rr';
    let aa',ff' = get_normalized n aa in (* normalize eqs wrt rr *)
    let ff =  union_cc (uncurry (@) (get_normalized n (to_cc (all_overlaps rr aa')))) in
    let ff_aa, _ = select (union_cc ((Listset.diff ff aa) @ ff')) (select_count i) 200 in
    let ff_all = union_cc (ff_aa @ ff_all) in
    let m = List.fold_left (fun m (lr,_) -> min m (Rule.size lr)) 20 ff_all in
    sizes := m::!sizes;
(*    if joins_all' rr (List.map fst !(flags.es) @ (Overlap.cp rr)) *)
    if success (rr,List.map fst aa') (List.map fst !(flags.es) @ (Overlap.cp rr))
     then raise (Success (rr,List.map fst aa')) else (j+1,ff_all)
   in
   try
    let (_,ff) = List.fold_left process (0,[]) rrs in
    let aa' = union_cc (ff @ aa) in
    if degenerated aa' then raise Restart;
    phi ctx aa'
   with Success (trs,ee) -> (trs,ee)
;;

let set_flags fs es = 
 flags.d := !(fs.d);
 flags.n := !(fs.n);
 flags.strategy := !(fs.strategy);
 flags.tmp := !(fs.tmp);
 flags.es := [ st, TOP | st <- es ]
;;

(* main ckb function *)
let rec ckb fs es =
 let ctx = mk_context () in
 let es' = List.map normalize es in
 try
  set_flags fs es';
  let ce = [ st, TOP | st <- es' ] in
  let ctx = mk_context () in
  List.iter (fun s -> Strategy.init s 0 ctx ce) (Listx.unique (t_strategies ()));
  let (trs,ee) = phi ctx ce in
  let s = termination_strategy () in
  (if !(fs.output_tproof) then 
   try Format.printf "TERMINATION PROOF:\n"; assert (check_termination fs trs) 
   with _ -> Format.printf "(proof output for termination strategy not supported)\n%!");
  del_context ctx;
  (trs, ee)
 with Restart -> (
(*  Format.printf "restart\n%!";*)
  pop_strategy ();
  Strategy.clear ();
  Cache.clear ();
  Hashtbl.clear ht_ols;
  St.restarts := !St.restarts + 1;
  all_overlap_list := [];
  rewrite_trace := [];
  rewrite_traces_eq := [];
  del_context ctx;
  ckb fs (List.map normalize es'))
