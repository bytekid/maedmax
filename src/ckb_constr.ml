(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module L = List
module O = Overlap
module R = Rule
module A = Analytics
module S = Settings
module St = Strategy
module Logic = Settings.Logic
module T = Term
module Expr = Constrained.Expr
module Lit = Constrained.Literal
module Lits = Constrained.Literals
module CEq = Constrained.Equality

(*** OPENS *******************************************************************)
open Prelude
open Settings

(*** TYPES *******************************************************************)
type state = {
  context : Logic.context;
  equations : Lit.t list;
  settings  : Settings.t;
  heuristic : Settings.heuristic
}

(*** EXCEPTIONS **************************************************************)
exception Success of Rules.t

(*** GLOBALS *****************************************************************)
(*** FUNCTIONS ***************************************************************)
let make_state c es s h = {
  context = c;
  equations = es;
  settings = s;
  heuristic = h
}

let update_state s es = { s with
  equations = es;
}

let debug s d = s.settings.debug >= d

let constraints s =
  match s.heuristic.strategy with
  | [] -> failwith "no constraints found"
  | (_, cs, _, _, _) :: _ -> cs
;;

let max_constraints s =
 match s.heuristic.strategy with
  | [] -> failwith "no max constraints found"
  | (_, _, ms, _, _) :: _ -> ms
;;

(* shorthands for settings *)
let termination_strategy s = 
  match s.heuristic.strategy with 
  | [] -> failwith "no termination strategy found"
  | (s, _, _, _, _) :: _ -> s
;;

let flatten t = Term.flatten (Signature.ac_symbols ()) t
let unflatten t = Term.flatten (Signature.ac_symbols ()) t

let normalize (s,t) =
  let s',t' = flatten s, flatten t in
  let s', t' = Variant.normalize_rule (s', t') in
  let uv = unflatten s', unflatten t' in
  uv
;;

let print_list = Formatx.print_list (fun f n -> Lit.print f n) "\n "

let set_iteration_stats s =
  let aa = s.equations in
  let i = !A.iterations in
  A.iterations := i + 1;
  A.equalities := List.length aa;
  A.set_time_mem ();
  A.eq_counts := !A.equalities :: !(A.eq_counts);
  if debug s 1 then
    F.printf "Start iteration %i with %i equations:\n %a\n%!"
      !A.iterations !A.equalities print_list aa
;;

(* OVERLAPS *)
let overlaps s rr =
  let cps1 = [Lit.overlaps_on rl1 rl2 | rl1 <- rr; rl2 <- rr] in
  let cps2 = [Lit.overlaps_on_below_root rl2 rl1 | rl1 <- rr; rl2 <- rr] in
  let cps = List.flatten (cps1 @ cps2) in
  if debug s 2 then
    Format.printf "CPs:\n%a\n" print_list cps;
  cps
;;

let overlaps s = A.take_time A.t_overlap (overlaps s)

(* find k maximal TRSs *)
let (<|>) = Logic.(<|>)
let (!!) = Logic.(!!)

let c_maxcomp k ctx cc =
  let oriented ((l,r),v) = v <|> (C.find_rule (r,l)) in
  L.iter (fun ((l,r),v) ->
    if l > r then Logic.assert_weighted (oriented ((l,r),v)) k) cc
;;

let search_constraints s (ccl, ccsymlvs) =
  let assert_c = function
    | S.Empty -> ()
    | _ -> Format.printf "unsupported search_constraints\n%!"
  in L.iter assert_c (constraints s);
  let assert_mc = function
    | S.Oriented -> c_maxcomp 1 s ccsymlvs
    | _ -> Format.printf "unsupported max search_constraints\n%!"
  in L.iter assert_mc (max_constraints s)
 ;;


let max_k s =
  let ctx, cc = s.context, s.equations in
  let k = s.heuristic.k !(A.iterations) in
  let cc_eq = [ Lit.terms n | n <- cc ] in
  let cc_symm = [n | n <- Lits.symmetric cc] in 
  let cc_symml = [Lit.terms c | c <- cc_symm] in
  L.iter (fun n -> ignore (C.store_rule_var ctx n)) cc_symml;
  let cc_symm_vars = [n, C.find_rule (Lit.terms n) | n <- cc_symm] in
  let cc_symml_vars = [Lit.terms n,v | n,v <- cc_symm_vars] in
  if debug s 2 then F.printf "K = %i\n%!" k;
  let strat = termination_strategy s in
  let rec max_k acc ctx n =
    if debug s 2 then F.printf " ... n = %i\n%!" n;
    if n = 0 then L.rev acc (* return TRSs in sequence of generation *)
    else
      if A.take_time A.t_sat Logic.max_sat ctx then (
        let m = Logic.get_model ctx in
        let c = Logic.get_cost ctx m in
        let add_rule (n,v) rls = if Logic.eval m v then (n,v) :: rls else rls in
        let rr = L.fold_right add_rule cc_symm_vars []  in
        let order = St.decode 0 m strat in
        if !Settings.do_assertions then (
          let ord n =
            let l, r = Lit.terms n in order#gt l r && not (order#gt r l)
          in
          assert (L.for_all ord (L.map fst rr)));
        Logic.require (!! (Logic.big_and ctx [ v | _,v <- rr ]));
        max_k ((L.map fst rr, c, order) :: acc) ctx (n-1))
      else acc
   in
   A.take_time A.t_orient_constr (St.assert_constraints strat 0 ctx) cc_symml;
   Logic.push ctx;
   Logic.require (St.bootstrap_constraints 0 ctx cc_symml_vars);
   search_constraints s (cc_eq, cc_symml_vars);
   let trss = max_k [] ctx k in
   Logic.pop ctx;
   trss
;;

let rec phi s =
  set_iteration_stats s;
  let i = !A.iterations in
  
  let process (j, s, aa_new) (rr, c, order) =
    let rr = List.map Lit.terms rr in
    if debug s 2 then (
      Format.printf "process TRS %i-%i: %a\n%!" i j Rules.print rr; order#print ());
    let aa = s.equations in
    (*let irred, red = rewrite rr aa in *)
    let cps_all = overlaps s rr in
    (*let cps = reduced rr cps in
    if debug s 2 then
      Format.printf "%d reduced CPs:\n%a" (List.length cps) Lits.print cps;
    let nn = NS.diff (NS.add_all cps red) aa in (* new equations *)
    let sel, rest = select s aa nn in
    if succeeds s rr cps_all then
      raise (Success rr)
    else
       let s' = update_state s (NS.add_list sel aa) in
       (j+1, s', sel @ aa_new)*)
    raise (Success [])
  in
  try
    let rrs = max_k s in
    let _, s', aa_new = L.fold_left process (0, s, []) rrs in
    phi s'
  with Success rr -> (SAT, Completion rr)
;;

let check_sat state ces =
  let check_sat l =
    let c, cl = Lit.constr l, Lit.log_constr l in
    let ctx = state.context in
    Logic.push ctx;
    Logic.require cl;
    assert (Logic.check ctx);
    Logic.pop ctx
  in
  List.iter check_sat ces
;;


let complete (settings, heuristic) ces =
  let ctx = Logic.mk_context () in
  let ces = [Constrained.Literal.of_equation ctx (normalize e, c) | e, c <- ces] in
  let start = Unix.gettimeofday () in
  let s = make_state ctx ces settings heuristic in
  check_sat s ces;
  let ss = L.map (fun (ts,_,_,_,_) -> ts) heuristic.strategy in
  L.iter (fun s -> St.init s 0 ctx [ Lit.terms n | n <- ces ]) ss;
  let res = phi s in
  A.t_process := !(A.t_process) +. (Unix.gettimeofday () -. start);
  Logic.del_context ctx;
  res
;;