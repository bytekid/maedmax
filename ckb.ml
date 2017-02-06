(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module L = List
module O = Overlap
module R = Rule
module St = Statistics
module S = Strategy

(*** OPENS *******************************************************************)
open Prelude
open Yicesx
open Settings
open Node

(*** MODULES *****************************************************************)
module N = Equation
module NS = Nodes.Make(N)

(*** EXCEPTIONS **************************************************************)
exception Success of (Rules.t * Rules.t)
exception Restart
exception Fail

(*** GLOBALS *****************************************************************)
let settings = Settings.default

let sizes = ref [] (* to check degeneration *)

(* caching for search strategies*)
let redc : (int * int, bool) Hashtbl.t = Hashtbl.create 512;;
let reducible : (int, Yicesx.t) Hashtbl.t = Hashtbl.create 512;;
let rl_index : (Rule.t, int) Hashtbl.t = Hashtbl.create 128;;

(* hash values of states *)
let hash_initial = ref 0;;
let hash_iteration = ref 0;;

(* map equation s=t to list of (rs, s'=t') where rewriting s=t with rs yields
   s'=t' *)
let rewrite_trace : (Rule.t, (Rules.t * Rule.t) list) Hashtbl.t =
  Hashtbl.create 512;;

(*** FUNCTIONS ***************************************************************)
let termination_strategy _ = 
 match !(settings.strategy) with 
  | [] -> failwith "no termination strategy found"
  | (s,_, _) :: _ -> s
;;

let constraints _ = 
 match !(settings.strategy) with 
  | [] -> failwith "no constraints found"
  | (_,cs,_) :: _ -> cs
;;

let max_constraints _ =
 match !(settings.strategy) with
  | [] -> failwith "no max constraints found"
  | (_,_,ms) :: _ -> ms
;;

let use_maxsat _ = max_constraints () <> []

let has_comp () = L.mem S.Comp (constraints ())

let pop_strategy _ = 
 if !(settings.d) then F.printf "pop strategy\n%!";
 match !(settings.strategy) with
  | [] -> failwith "no strategy left in pop"
  | [s] -> ()
  | _ :: ss -> settings.strategy := ss
;;

let t_strategies _ = L.map (fun (ts,_,_) -> ts) !(settings.strategy)

(* * REWRITING * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let add_rewrite_trace st rls st' =
  if has_comp () then
    begin
    let reducts = try Hashtbl.find rewrite_trace st with Not_found -> [] in
    Hashtbl.replace rewrite_trace st ((rls, st') :: reducts)(*;
    Format.printf "%a reduces to %a\n" Rule.print st Rule.print st'*)
    end
;;

(* normalization of cs with TRS with index n. Returns pair (cs',ff) where ff
   are newly generated eqs and cs' \subseteq cs is set of irreducible eqs *)
let rewrite n cs =
 let rr = C.redtrs_of_index n in
 let rec rewrite (irrdcbl, news) = function
  | [] -> (irrdcbl, news)
  | n :: cc ->
   match N.nf_with rr n with
    | None -> rewrite (n :: irrdcbl, news) cc (* no progress here *)
    (* n' is leftover of n (only relevant with constraints *)
    | Some (n', nnew, rs) -> (* if terms got equal, nnew is empty *)
        let nnew' = NS.normalize nnew in (
        if nnew <> [] then add_rewrite_trace n rs (L.hd nnew');
        rewrite (n' @ irrdcbl, nnew' @ news) cc
    )
 in rewrite ([],[]) cs
;;  
   
let rewrite rr = St.take_time St.t_rewrite (rewrite rr)

let reduced rr ns =
  let (irred, news) = rewrite rr ns in NS.unique (irred @ news)
;;

(* * SUCCESS CHECKS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let saturated ctx (rr,ee) cc =
 let covered n =
  let s,t = N.rule n in
  let s',t' = Rewriting.nf rr s, Rewriting.nf rr t in
  if not !(settings.unfailing) then s' = t'
  else
    let str = termination_strategy () in
    let d = !(settings.d) in
    s' = t' || Ground.joinable ctx str (rr, ee, !(settings.ac_syms)) (s',t') d
 in L.for_all covered cc
;;

let succeeds ctx (rr,ee) cc gs =
  let joinable (s,t) = Rewriting.nf rr s = (Rewriting.nf rr t) in
  if gs <> [] then (
    if List.exists joinable gs then (
      if !(settings.d) then Format.printf "joined goal\n";
      true)
    else false)
  else saturated ctx (rr,ee) cc
;;

(* * SELECTION * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let log_select cc = F.printf "selected: %i\n%a\n%!" (L.length cc) NS.print cc

let select_count i = !(settings.n)

(* selection of small new nodes *)
let select cc thresh = 
 let aa = NS.sort_smaller_than thresh cc in
 let aa,aa' = Listx.split_at_most (select_count !(St.iterations)) aa in 
 let pp = Listset.diff cc aa in 
 if !(settings.d) then log_select aa;
 (* remember smallest terms for divergence estimate *)
 let m = L.fold_left (fun m n -> min m (R.size (N.rule n))) 20 aa in
 sizes := m :: !sizes;
 (aa,pp)
;;

(* * CRITICAL PAIRS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let eqs_for_overlaps ee =
  let use_for_overlaps n = let (s,t) = N.rule n in not (Term.is_subterm s t) in
  let ee' = [ e | e <- NS.symmetric ee; use_for_overlaps e ] in
  (* FIXME: check for variants? *)
  Listx.unique ee'
;;

(* get overlaps for rules rr and active nodes cc *)
let overlaps rr aa =
 let cc = if !(settings.unfailing) then eqs_for_overlaps aa @ rr else rr in
 NS.map N.normalize (NS.cps cc)
;;

 (* FIXME: no caching yet *)
let overlaps rr = St.take_time St.t_overlap (overlaps rr)

(* * FIND TRSS  * * *  * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* logical vars for new TRSs *)
let store_trss ctx =
  let store n _ =
    if not (Hashtbl.mem C.ht_trsvars n) then
      let rr = L.map C.find_rule (C.trs_of_index n) in
      if rr <> [] then (
        let v = mk_fresh_bool_var ctx in
        Hashtbl.add C.ht_trsvars n v;
        require (v <=> (big_and1 rr))
      )
 in Hashtbl.iter store C.ht_itrss
;;

let c_maxcomp ctx cc =
 let oriented (l,r) = C.find_rule (l,r) <|> (C.find_rule (r,l)) in
 L.iter (fun n -> assert_weighted (oriented (N.rule n)) 1) cc
;;

let c_not_oriented ctx cc =
 let exp (l,r) = (!! (C.find_rule (l,r))) <&> (!! (C.find_rule (r,l))) in
 L.iter (fun n -> assert_weighted (exp (N.rule n)) 1) cc
;;

let idx r = 
  try Hashtbl.find rl_index r
  with Not_found -> 
    let i = Hashtbl.length rl_index in Hashtbl.add rl_index r i; i
;;

let is_reducible ctx cc (s,t) =
  let j = idx (s,t) in
  try Hashtbl.find reducible j with Not_found -> (
    let reduces_st rl = (
      let red = Rewriting.reducible_with [rl] in
      Rule.is_rule rl && (red t || red s))
    in
    let b = big_or ctx [ C.find_rule (N.rule rl) | rl <- NS.symmetric cc;
                                                   reduces_st (N.rule rl)] in
    Hashtbl.add reducible j b;
    b
  )
;;

let is_reducible ctx cc = St.take_time St.t_tmp2 (is_reducible ctx cc)

let rlred ctx cc (s,t) =
  let j = idx (s,t) in
  let redcbl rl =
    let i = idx rl in (
    let red = Rewriting.reducible_with [rl] in
    let is_rule (l,r) = Rule.is_rule (l,r) && (not (Term.is_subterm l r)) in
    let b = is_rule rl && (red t || red s) in
    Hashtbl.add redc (j, i) b; b)
  in big_or ctx [ C.find_rule rl | rl <- NS.symmetric cc; redcbl (N.rule rl) ]
;;

let c_red ctx cc =
  L.iter (fun rl -> require (rlred ctx cc (N.rule rl))) cc
;;

let c_red ctx = St.take_time St.t_cred (c_red ctx)

let c_cpred ctx cc =
  Hashtbl.clear reducible;
  let rs = [ N.rule n | n <- NS.symmetric cc; Rule.is_rule (N.rule n) ] in
  let rule, red = C.find_rule, is_reducible ctx cc in
  let c2 = [ rule rl <&> (rule rl') <=>> (red st) | rl <- rs; rl' <- rs;
                                             st <- O.nontrivial_cps rl rl' ] in
  L.iter (fun c -> ignore (assert_weighted c 2)) c2;
;;

let c_cpred ctx = St.take_time St.t_ccpred (c_cpred ctx)

let c_max_red ctx cc =
  L.iter (fun rl -> assert_weighted (rlred ctx cc (N.rule rl)) 1) cc
;;

let c_comp ctx ns =
 let rule_var, weight_var = C.find_rule, C.find_eq_weight in
 let all_eqs ee = big_and ctx (L.map C.find_eq ee) in
 (* induce order: decrease from e to equations in ee *)
 let dec e ee = big_and ctx [ weight_var e <>> (weight_var e') | e' <- ee] in
 (* encode reducibility of equation st *)
 let red st =
  let es = try Hashtbl.find rewrite_trace st with Not_found -> [] in
  big_or ctx [ C.find_eq e <&> all_eqs ee <&> dec e ee | (ee,e) <- es ] 
 in
 let considered ((s,t) as st) =
   require (C.find_eq st <=>> (big_or1 [rule_var st; rule_var (t,s); red st]));
 in
 (* initial equations have to be considered *)
 require (all_eqs !(settings.es));
 L.iter considered [ n | n <- ns; not (N.is_trivial n)];
;;

let c_comp ctx = St.take_time St.t_ccomp (c_comp ctx)

(* constraints to guide search; those get all retracted *)
let search_constraints ctx cc =
 let assert_c = function
   | S.Red -> c_red ctx cc
   | S.Empty -> ()
   | S.Comp -> c_comp ctx cc
 in L.iter assert_c (constraints ());
 let assert_mc = function
   | S.Oriented -> c_maxcomp ctx cc
   | S.NotOriented -> c_not_oriented ctx cc
   | S.MaxRed -> c_max_red ctx cc
   | S.CPsRed -> c_cpred ctx cc
   | S.MaxEmpty -> ()
 in L.iter assert_mc (max_constraints ())
;;

(* block list of previously obtained TRSs *)
let rec block_trss ctx rrs cc = 
  let not_r rr = !! (big_and ctx [ C.find_rule r | r <- rr ]) in
  big_and ctx [ not_r rr | rr,_ <- rrs; rr <> [] ]
;;

(* find k maximal TRSs *)
let max_k ctx cc =
  let k = !(settings.k) !(St.iterations) in
  let cc_symm = NS.symmetric cc in 
  if !(settings.d) then F.printf "K = %i\n%!" k;
  let rec max_k acc ctx cc n =
    if n = 0 then List.rev acc (* return TRSs in sequence of generation *)
    else (
      require (block_trss ctx acc cc);
      let sat_call = if use_maxsat () then max_sat else check in
      if St.take_time St.t_sat sat_call ctx then (
        let m = get_model ctx in
        let c = if use_maxsat () then get_cost m else 0 in
        let is_rl n = 
          let rl = N.rule n in eval m (C.find_rule rl) && (not (Rule.is_dp rl))
        in
        let rr = [ n | n <- cc_symm; is_rl n ] in
        max_k ((rr, c) :: acc) ctx cc (n-1))
     else (
       if !(settings.d) then F.printf "no further TRS found\n%!"; 
       if (n = k && L.length !(settings.strategy) > 1) then raise Restart;
       acc))
   in
   C.store_rule_vars ctx (NS.terms cc_symm);
   if has_comp () then C.store_eq_vars ctx cc;
   let s = termination_strategy () in
   (* FIXME: restrict to actual rules?! *)
   St.take_time St.t_orient_constr (S.assert_constraints s 0 ctx) cc_symm;
   push ctx; (* backtrack point for Yices *)
   require (S.bootstrap_constraints 0 ctx cc_symm);
   search_constraints ctx cc;
   let trss = max_k [] ctx cc k in
   pop ctx; (* backtrack: get rid of all assertions added since push *)
   trss
;;

let max_k ctx = St.take_time St.t_maxk (max_k ctx)

(* some logging functions *)
let log_iteration i aa =
 F.printf "Iteration %i\n%!" i;
 F.printf "CC: %i\n%a%!" (L.length aa) NS.print aa;
 F.printf "\n%!"
;;

let log_max_trs j rr rr' c =
 F.printf "TRS %i - %i: cost %i\n %a\n\n reduced: %a\n@." !St.iterations j c 
   Rules.print (Variant.rename_rules rr)
   Rules.print (Variant.rename_rules rr')
;;


(* heuristic predicate checking degeneration of run, used to trigger restart *)
let degenerated cc =
 (L.length !sizes > 10) &&
 (L.for_all (fun x -> x > 16) (Listx.take 6 !sizes))
;;

(* main control loop *)
let repeated_iteration_state es gs =
 let h = Hashtbl.hash (List.length es, es, gs) in
 let r = (h = !hash_iteration) in
 hash_iteration := h;
 if r && !(settings.d) then F.printf "repeated iteration state";
 r
;;

let set_iteration_stats aa =
  let i = !St.iterations in
  St.iterations := i + 1;
  let s = S.to_string !(settings.strategy) in
  if !(settings.d) then (
   F.printf "Start iteration %i with %a equations\n%!"
     !St.iterations Rules.print aa;
   F.printf "%s\n%!" (Yojson.Basic.pretty_to_string 
    (Statistics.json s (!(settings.k) i) (select_count i))));
  St.ces := L.length aa
;;

let store_trs ctx j rr c =
  let rr_index = C.store_trs rr in
  (* for rewriting actually reduced TRS is used; have to store *)
  let rr_reduced = NS.reduce rr in
  C.store_redtrs rr_reduced rr_index;
  C.store_rule_vars ctx rr_reduced; (* otherwise problems in norm *)
  if has_comp () then C.store_eq_vars ctx rr_reduced;
  if !(settings.d) then log_max_trs j rr rr_reduced c;
  rr_index
;;

let non_gjoinable ctx ns rr =
  let ac_syms = !(settings.ac_syms) in
  let keep n =
    (* to-subterm rules can always be oriented, no need for complicated join *)
    let is_to_sub (l,r) = Term.is_subterm r l in 
    let sys = rr,[],ac_syms in
    let s = termination_strategy () in
    let d = !(settings.d) in
    is_to_sub n || is_to_sub (Rule.flip n) || Ground.non_joinable ctx s sys n d
  in
  let ns' = NS.unq_filter keep ns in
  NS.unique_subsumed ns'
;;

let rec phi ctx aa gs =
  if repeated_iteration_state aa gs then
    raise Restart;
  set_iteration_stats aa;
  let process (j,acc) (rr,c) =
    let trs_n = store_trs ctx j rr c in
    let irred, red = rewrite trs_n aa in (* rewrite eqs wrt new TRS *)
    let cps = reduced trs_n (overlaps rr irred) in (* rewrite CPs *)
    let nn = Listset.diff (NS.union cps red) aa in
    let nn = if !(settings.unfailing) then non_gjoinable ctx nn rr else nn in
    let sel, rest = select nn 200 in
    (* FIXME where to move this variable registration stuff? *)
    if has_comp () then C.store_eq_vars ctx rest;
    let rr,ee = NS.terms rr, NS.terms irred in
    if succeeds ctx (rr, ee) (NS.of_rules ctx !(settings.es) @ cps) gs
      then raise (Success (rr, ee))
    else
      j+1, NS.union sel acc
  in
  try
    let rrs = max_k ctx aa in
    let _, acc = L.fold_left process (0,[]) rrs in
    let aa' = acc @ aa in
    if degenerated aa' then raise Restart;
    phi ctx aa' gs
  with Success (trs,ee) -> (trs, Ground.add_ac ee !(settings.ac_syms))
;;

let set_settings fs es =
 settings.ac_syms := Ground.ac_symbols es;
 settings.d := !(fs.d);
 settings.n := !(fs.n);
 settings.strategy := !(fs.strategy);
 settings.tmp := !(fs.tmp);
 settings.es := es
;;

let remember_state es gs =
 let h = Hashtbl.hash (termination_strategy (), es,gs) in
 if h = !hash_initial then raise Fail;
 hash_initial := h
;;

(* main ckb function *)
let rec ckb fs es gs =
 (* store initial state to capture*)
 remember_state es gs;
 (* init state *)
 let ctx = mk_context () in
 let es' = L.map N.normalize es in
 try
  set_settings fs es';
  let ctx = mk_context () in
  L.iter (fun s -> Strategy.init s 0 ctx es') (Listx.unique (t_strategies ()));
  let (trs,ee) = phi ctx es' gs in
  let s = termination_strategy () in
  (if !(fs.output_tproof) then 
   try
     F.printf "TERMINATION PROOF:\n";
     assert (Termination.check s trs !(settings.json)) 
   with _ -> F.printf "(sorry, no proof output for termination strategy)\n%!");
  del_context ctx;
  (trs, ee)
 with Restart -> (
  if !(settings.d) then Format.printf "restart\n%!";
  pop_strategy ();
  Strategy.clear ();
  Cache.clear ();
  St.restarts := !St.restarts + 1;
  Hashtbl.reset rewrite_trace;
  del_context ctx;
  ckb fs (L.map N.normalize es') gs)
