(*** MODULES *****************************************************************)
module St = Statistics

(*** OPENS *******************************************************************)
open Yices
open Rewriting
include Ckb

(*** TYPES *******************************************************************)
(* constraints *)
type c =
 TRS of int | NEG of c | AND of c list | OR of c list |
 BOT | TOP | R of Rule.t

type t = Rule.t * c

(* ordering environment *)
type rpo_env = {
 funs: (Signature.sym * int) list;
 prec_vars: (Signature.sym * Yices.expr) list;
 stat_vars: (Signature.sym * Yices.expr) list
}

type environment = RPOEnv of rpo_env | NoEnv 

(*** EXCEPTIONS **************************************************************)
exception Success of Rules.t

(*** GLOBALS *****************************************************************)
let ac = ref []
(* count number of TRSs considered so far *)
let trscount = ref 0
(* associate index with TRS and vice versa *)
let ht_itrss : (int, Rules.t) Hashtbl.t = Hashtbl.create 40;;
let ht_trssi : (Rules.t,int) Hashtbl.t = Hashtbl.create 40;;
(* tuples ((n,m),b) to remember whether TRS n contains TRS m *)
let ht_contains : (int * int, bool) Hashtbl.t = Hashtbl.create 200;;
(* Yices variable for each TRS *)
let ht_trsvars : (int, Yices.expr) Hashtbl.t = Hashtbl.create 40;;
(* Yices variable for each rule *)
let rule_vars : (Rule.t * Yices.expr) list ref = ref [];;
(* Yices variable for each constraint encountered at some point *)
let ht_cvars : (c, Yices.expr) Hashtbl.t = Hashtbl.create 100;;
(* remember whether termination constraint was already added to context *)
let ht_rlycs : (Rule.t, bool) Hashtbl.t = Hashtbl.create 100;;
(* store overlaps *)
let ht_ols : (Rule.t * Rule.t, Rule.t list) Hashtbl.t =
 Hashtbl.create 100;;
(* ordering environment *)
let env = ref NoEnv

(*** FUNCTIONS ***************************************************************)
(* * OUTPUT  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let rec printc ppf = function
 | TRS rs -> Format.fprintf ppf "%i" rs
 | R r -> Rule.print ppf r
 | NEG cn -> Format.fprintf ppf "(NOT %a)" printc cn
 | AND cs -> Format.fprintf ppf "(%a)" (Formatx.print_list printc " AND ") cs
 | OR cs -> Format.fprintf ppf "(%a)" (Formatx.print_list printc " OR ") cs
 | BOT -> Format.fprintf ppf "F"
 | TOP -> Format.fprintf ppf "T"

let print_ceq ppf (st,c) =
 Format.fprintf ppf "@[%a | %a@]" Rule.print st printc c

let print ppf c_rules =
  Format.fprintf ppf "@[<v 0>%a@]" (Formatx.print_list print_ceq "@ ") c_rules

(* * HASHING FUNCTIONS * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let trs_of_index n =
 try Hashtbl.find ht_itrss n
 with Not_found -> failwith ("trs_of_index failed")
;;

let trs_of_index = St.take_time St.t_cache trs_of_index

let contains n m =
 try Hashtbl.find ht_contains (n,m)
 with Not_found ->
  let rn = trs_of_index n in
  let rm = trs_of_index m in
  let c = Listset.subset rm rn in
  Hashtbl.add ht_contains (n,m) c;
  c
;;

let contains n = St.take_time St.t_cache (contains n)

let find_rule lr =
 snd (List.find (fun (st,_) -> Rule.variant st lr) !rule_vars)
;;

let rec store_rule_vars ctx rls =
 let add lr =
   if not (List.exists (fun (st,_) -> Rule.variant st lr) !rule_vars) then
    let v = mk_fresh_bool_var ctx in
    rule_vars :=  (lr, v) :: !rule_vars
 in List.iter add rls
;;

let find_trs_var n =
 try Hashtbl.find ht_trsvars n
 with Not_found -> failwith ("trsvar "^(string_of_int n)^" not found")
;;

let find_trs_var = St.take_time St.t_cache find_trs_var

let store_trs trs =
 trscount := !trscount+1;
 let n = !trscount in
 Hashtbl.add ht_itrss n trs;
 Hashtbl.add ht_trssi trs n;
 n
;;

let store_trs = St.take_time St.t_cache store_trs

(* * AUXILIARY  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let (<.>) f g = fun x -> f (g x)

let sort_by f xs = List.sort (fun x y -> f x - f y) xs

let is_ac f = List.mem f !ac

let flatten t = Term.flatten !ac t

(* uniform rule renaming to avoid many variant checks *)
let normalize (s,t) =
 let s,t = Term.flatten !ac s, Term.flatten !ac t in
 let s',t' =  Term.rename s, Term.rename t in
 if s' < t' then
  Variant.rename_rule [] (s,t)
 else
  Variant.rename_rule [] (t,s)

(* * CONSTRAINT STUFF * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let and_ = function
  | TOP, y -> y
  | x,TOP -> x
  | BOT, _
  |_,BOT -> BOT
  | TRS x, TRS x' when x = x' -> TRS x
  | TRS r, NEG (TRS r') when r=r' -> BOT
  | NEG (TRS r), TRS r' when r=r' -> BOT
  | x,y -> (AND [x;y])
;;

let or_ = function
  | TOP, _
  | _,TOP -> TOP
  | BOT, x -> x
  | x,BOT -> x
  | TRS r, TRS r' when r=r' -> TRS r
  | TRS x, TRS x' when x = x' -> TRS x
  | x, AND [y;x'] when (x=x') -> x
  | x, AND [x';y] when (x=x') -> x
  | AND [x;y], AND [x';NEG y'] when ((x=x') && (y=y')) -> x
  | x,y -> (OR [x;y])
;;

let rec translate_to_smt ctx = function
  | TRS rr -> find_trs_var rr
  | R r -> find_rule r
  | NEG cn -> mk_not ctx (translate_to_smt ctx cn)
  | AND cs -> mk_and ctx (Array.of_list [ translate_to_smt ctx ci | ci <- cs ])
  | OR cs ->  mk_or ctx (Array.of_list [ translate_to_smt ctx ci | ci <- cs ])
  | BOT -> mk_false ctx
  | TOP -> mk_true ctx


let smt_constraint ctx c = Hashtbl.find ht_cvars c

let smt_constraint ctx = St.take_time St.t_translate (smt_constraint ctx)

let t ctx c = mk_not ctx (smt_constraint ctx c)

(* * REDUCTION ORDERS  * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

let name = Signature.get_fun_name 

let make_constr ctx f ce =
 let consider ((l,r),_) =
  if not (Hashtbl.mem ht_rlycs (l,r)) then
   let c (s,t)= mk_or ctx [| mk_not ctx (find_rule (s,t)); f ctx s t |] in
   assert_simple ctx (c (l,r));
   assert_simple ctx (c (r,l));
   Hashtbl.add ht_rlycs (l,r) true;
 in List.iter consider ce

let rpo_env = function
 | RPOEnv e -> (e.funs, e.prec_vars, e.stat_vars)
 | _ -> failwith "not an rpo environment"

let init_rpo ctx ce =
 let fs = Rules.signature (List.map fst ce) in
 (* create precedence variables *)
 let ty  = mk_type ctx "int" in
 let var (f,_) = (f, mk_var_from_decl ctx (mk_var_decl ctx (name f^"l") ty)) in
 let pvars = List.map var fs in
 let bnd_0 = mk_num ctx 0 in
 let bnd_n = mk_num ctx (List.length fs) in
 let f cs (_, x) = (mk_ge ctx x bnd_0) :: (mk_ge ctx bnd_n x) :: cs in
 let c_bnds = mk_and ctx (Array.of_list (List.fold_left f [] pvars)) in
 (* status variables *)
 let fs' = [ f | f,a <- fs; a > 1; not (is_ac f) ] in
 let svars = [ f, mk_fresh_bool_var ctx | f <- fs'] in
 (* set environment, assert precedence bounds *)
 env := RPOEnv {funs=fs; prec_vars=pvars; stat_vars = svars}; 
 assert_simple ctx c_bnds
;;

let make_rpo_constr ctx ce =
 let fs, ps, ss = rpo_env !env in
 let f ctx s t = Ac_orders.yacrpo ctx !ac (ps,ss) s t in
 make_constr ctx f ce
;;

(* * CONSTRAINED EQUALITY OPERATIONS  * * * * * * * * * * * * * * * * * * * * *)
let rec satisfies rr = function
 | TRS rr' -> contains rr rr'
 | R r -> List.mem r (trs_of_index rr)
 | NEG cn -> not (satisfies rr cn)
 | AND cs -> List.for_all (fun ci -> satisfies rr ci) cs
 | OR cs -> List.exists (fun ci -> satisfies rr ci) cs
 | BOT -> false
 | TOP -> true

let to_cc n es =
 let rec to_rs rs = AND (List.map (fun r -> R r) rs) in
 List.map (fun (st,rs) -> (st, TRS n(*to_rs rsi*))) es

let cc_of_rr rr cc = [ st | st,ci <- cc; satisfies rr ci ]

let cc_of_rr rr = St.take_time St.t_project (cc_of_rr rr)

let rr_of_cc cc = []

let cc_minus_rr rr cc = [ st, and_ (c,NEG (TRS rr)) | st,c <- cc ]

let size =
 List.fold_left (fun s ((l,r),_) -> s + (Term.size l) + (Term.size r)) 0

(* normalization with respect to TRS with index n*)
let cc_norm_rr n cs =
 let k = size cs in
 let rr = trs_of_index n in
 let rec cc_norm_rr = function
  | [] -> []
  | ((s,t),c) :: cc ->
   let c = if Rule.size (s,t) < (if k > 100 then 10 else 9) then TOP else c in
   (*let used_s, nf_s = nf_with rr s in
   let used_t, nf_t = nf_with rr t in
   let rs = List.map (fun r -> R r) (Listx.unique (used_s@used_t)) in
   let c' = if Rule.size (s,t) < 10 then TOP else AND (c::rs) in*)
   let nf_s = Ac_rewriting.nf !ac rr s in
   let nf_t = Ac_rewriting.nf !ac rr t in
   (*let c' = if Rule.size (s,t) < 10 then TOP else and_ (c,TRS n) in*)
   let nf_s,nf_t = normalize (nf_s,nf_t) in
   if nf_s <> nf_t then ((nf_s,nf_t), and_ (c, TRS n)) :: (cc_norm_rr cc)
   else cc_norm_rr cc
 in cc_norm_rr cs
;;

(* insert constrained equality in set *)
let rec insert (st,c) = function
  | [] -> [(st,c)]
  | (uv,d) :: ls when st = uv -> (st, or_ (c,d)) :: ls
  | (uv,d) :: ls -> (uv,d) :: (insert (st,c) ls)

let insert x = St.take_time St.t_insert (insert x)

(* union of two constrained equality sets *)
let union_cc ls =
 let rec union1 acc = function
   | [] -> acc
   | h :: tl -> union1 (insert h acc) tl
 in union1 [] ls

let joins_all rr = 
 let nf = Ac_rewriting.nf !ac in
 List.for_all (fun ((s,t),_) -> nf rr s = (nf rr t))
;;

let joins_all rr = St.take_time St.t_project (joins_all rr)

(* * CRITICAL PAIRS * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let extend (l,r) =
 match l with
  | Term.F(f,ts) when List.mem f !ac ->
   let x = Term.V (Signature.fresh_var ()) in 
   let l', r' = flatten (Term.F(f,[x;l])), flatten (Term.F(f,[x;r])) in 
   [l,r; l',r']
  | _ -> [l,r]
;;

(* selection of small critical pairs *)
let select cc n d =
 let small = [ e,c | e,c <- cc; Rule.size e < d] in
 let aa = Listx.take_at_most n (sort_by (fun (x,_) -> Rule.size x) small) in
 let pp = Listset.diff cc aa in (aa,pp)

(* obtain and normalize overlaps *)
let overlaps rr =
 let add r1 r2 =
  try Hashtbl.find ht_ols (r1,r2)
  with Not_found ->
   let r1e,r2e = extend r1, extend r2 in
   (*Format.printf "Extending %a yields %a, extending %a yields %a \n%!"
    Rule.print r1 Rules.print r1e Rule.print r2 Rules.print r2e;*)
   let os = 
    if r1 = r2 then List.map normalize (Ac_overlap.cp2 !ac [r1] r2e)
    else List.map normalize (Ac_overlap.cp2 !ac [r1] r2e @
    (Ac_overlap.cp2 !ac r1e [r2])) 
   in
   Hashtbl.add ht_ols (r1,r2) os;
   (*Format.printf "Overlaps between %a and %a are %a \n%!"
    Rule.print r1 Rule.print r2 Rules.print os;*)
   os
 in [ e,[r1;r2] | r1 <- rr; r2 <- rr; e <- add r1 r2]

let overlaps  = St.take_time St.t_overlap
(* (fun rr -> List.map (fun (r,rs) -> normalize r, rs) (Overlap.cp_rules rr))*)
 overlaps

(* * FILTERING OUT UNSATSFIABLE CONSTRAINED EQUALITIES  * * * * * * * * * * * *)
(* assert implications between TRSs *)
let assert_trs_containment ctx =
 let add n v (ctx,ass) =
  let add_for n' v' (ctx',ass') =
   if (n <> n') && (contains n n') then
     let c = mk_or ctx [| mk_not ctx v; v' |] in
     let a = assert_retractable ctx c in
     (ctx',a::ass')
   else (ctx',ass')
  in Hashtbl.fold add_for ht_trsvars (ctx,ass)
 in Hashtbl.fold add ht_trsvars (ctx,[])
;;

(* filter out unsatisfiable constrained equalities *)
let filter_sat ctx cc =
 let check ctx c =
  let e = smt_constraint ctx (snd c) in
  let a_c = assert_retractable ctx e in
  let ctx,as_trs = assert_trs_containment ctx in
  let a = ((check ctx) = True) in
  List.iter (retract ctx) (a_c::as_trs);
  a
 in List.filter (check ctx) cc
;;

let filter_sat = St.take_time St.t_gc filter_sat

(* * FIND MAXIMAL TRS  * * * * * * * * * * * * * * * *  * * * * * * * * * * * *)
(* Yices vars and assertions for new TRSs *)
let assert_trs_vars ctx =
 let add n _ ctx =
  if Hashtbl.mem ht_trsvars n then
   ctx
  else (
   let v = mk_fresh_bool_var ctx in
   Hashtbl.add ht_trsvars n v;
   let rr = List.map find_rule (trs_of_index n) in
   if rr = [] then ctx
   else
    let cr = mk_and ctx (Array.of_list rr) in
    let _ = assert_simple ctx (mk_eq ctx v cr) in
    ctx)
 in Hashtbl.fold add ht_itrss ctx
;;

(* Yices vars and assertions for new constraints *)
let rec assert_constraint_vars ctx ce =
  let add (_,c) =
   if not (Hashtbl.mem ht_cvars c) then
    let v = mk_fresh_bool_var ctx in
    Hashtbl.add ht_cvars c v;
    let c' = translate_to_smt ctx c in
    assert_simple ctx (mk_eq ctx v c');
  in List.iter add ce
;;


(* update context: write conditions for new rules, TRSs, constraints 
   (these assertions are permanent, they will not be retracted) *)
let update_context ctx ord cc =
  let es = List.map fst cc in
  let rls = es @ [ t,s | s,t <- es ] in
  let _ = store_rule_vars ctx rls in (* store missing ones *)
  let _ = assert_trs_vars ctx in
  let _ = assert_constraint_vars ctx cc in
  make_rpo_constr ctx cc;
  ctx

let update_context ctx ord = St.take_time St.t_upd (update_context ctx ord)

(* weighted assertions for maxsat. Note that these assertions will be
   retracted before the next iteration! *)
let problem_constraint ctx cc =
(*  let exp ((l,r),c) = mk_or ctx [|find_rule (l,r);find_rule (r,l);t ctx c|] in
  let _ = List.map (fun ce -> assert_weighted ctx (exp ce) 1L) cc in*)
  (* prefer orientation to constraint satisfaction: *)
  let exp ((l,r),c) = mk_or ctx [|find_rule (l,r);find_rule (r,l)|] in
  let _ = List.map (fun ce -> assert_weighted ctx (exp ce) 1L) cc in
  ctx
;;


(* block list of previously obtained TRSs *)
let rec block_trss ctx = function
  | [] -> mk_true ctx
  | rr::rrr ->
      mk_and ctx [|
      mk_not ctx (
      mk_and ctx
      (Array.of_list (List.map snd
        [ (List.find (fun (x,y) -> x = r) !rule_vars) | r <- rr ]))
      ); block_trss ctx rrr |]


(* find k maximal TRSs *)
let max_k ctx cc ord k =
 let rec max_k acc ctx cc n =
  if n = 0 then acc,ctx
  else
   let _ = assert_retractable ctx (block_trss ctx acc) in
   match St.take_time St.t_sat max_sat ctx with
    | True ->
     let m = get_model ctx in
     let rr = [rl | rl,ci <- !rule_vars;evaluate_in_model m ci = Yices.True] in
     max_k (rr::acc) ctx cc (n-1)
    | _ -> acc, ctx
 in
 let ctx = update_context ctx ord cc in
 push ctx; (* backtrack point for Yices *)
 let ctx = problem_constraint ctx cc in
 let res,ctx = max_k [] ctx cc k in
 pop ctx; (* get rid of all assertions added since push *)
 res,ctx

(* main control function *)
let rec phi ctx ord k (aa,pp) =
  St.iterations := !St.iterations + 1;
  let i = !St.iterations in
  (*Format.printf "Iteration %i\n%!" i;*)
  match max_k ctx aa ord k with
  | [],_ -> failwith "no TRS found"
  | rrs,ctx ->
  let aa = if i mod 5 = 0 then filter_sat ctx aa else aa in
   let process (aa,pp,j,k) rr =
   let _ = Format.printf "TRS %i - %i: %a@." i j 
     Rules.print (Variant.rename_rules rr) in 
   let n = store_trs rr in
   (*let _ = Format.printf "C: %a@." print (aa@pp) in*)
    let ff =  Listx.unique (to_cc n (overlaps rr)) in
    (*let _ = Format.printf "F: %a@." print ff in*)
    let ff =  cc_norm_rr n ff in
    (*let _ = Format.printf "F norm: %a@." print ff in*)
    let ff_aa, ff_pp = select ff 9 23 in
    (*Format.printf "CPs: %i\n%!" (List.length ff_aa);*)
    let k = if (List.length ff_aa < 9) then 2 else 1 in
    (*if i mod 2 = 0 then St.print ();*)
    let aa1 = union_cc ((cc_minus_rr n aa) @ (cc_norm_rr n aa) @ ff_aa) in
    let pp1 = union_cc ((cc_minus_rr n pp) @ (cc_norm_rr n pp) @ ff_pp) in
    if joins_all rr (aa1@pp1) then raise (Success rr) else (aa1,pp1,j+1,k)
   in
   try
    let (aa',pp',_,k) = List.fold_left process (aa,pp,0,k) rrs in
    phi ctx ord k (aa',pp')
   with Success trs -> Variant.rename_rules trs
;;


(* * MAIN * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let ckb ac' ord es =
(* Format.printf "AC %s\n%!" (List.fold_left (^) "" ac');*)
 ac := ac';
 let ce = [ normalize st, TOP | st <- es ] in
 let ctx = mk_context () in
 init_rpo ctx ce;
 let trs = phi ctx ord 1 (ce,[]) in
 del_context ctx;
 trs
