(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module L = List
module O = Overlap
module R = Rule
module A = Analytics
module S = Settings
module St = Strategy
module Ac = Theory.Ac
module Commutativity = Theory.Commutativity
module Lit = Literal
module NS = Nodes
module Logic = Settings.Logic
module T = Term
module ACR = Acrewriting

(*** OPENS *******************************************************************)
open Prelude
open Settings

(*** TYPES *******************************************************************)
type state = {
  context : Logic.context;
  equations : NS.t;
  new_nodes : Lit.t list;
  settings  : Settings.t;
  heuristic : Settings.heuristic
}

(*** EXCEPTIONS **************************************************************)
exception Success of Rules.t

(*** GLOBALS *****************************************************************)
(*** FUNCTIONS ***************************************************************)
let make_state c es s h = {
  context = c;
  equations = NS.of_list es;
  new_nodes = es;
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

let set_iteration_stats s =
  let aa = s.equations in
  let i = !A.iterations in
  A.iterations := i + 1;
  A.equalities := NS.size aa;
  A.set_time_mem ();
  A.eq_counts := NS.size aa :: !(A.eq_counts);
  if debug s 1 then
    F.printf "Start iteration %i with %i equations:\n %a\n%!"
      !A.iterations (NS.size aa) NS.print aa
;;

let select s all ss =
  let ssl = L.sort Lit.compare_size (NS.to_list ss) in
  let k = 2 in
  if debug s 2 then
    Format.printf "select %d out of %d:\n%a\n" k (NS.size ss) NS.print ss;
  let sel, rest = Listx.split_at_most k ssl in
  sel, NS.of_list rest
;;

let rewrite rr aa =
  let nf u = ACR.find_normalform u rr in
  let rew_nf (ls_old, ls_new) l =
    let s, t = Lit.terms l in
    let s', t' = nf s, nf t in
    (*Format.printf "simplify %a to %a\n%!" Rule.print (s,t) Rule.print (s',t');*)
    if s = s' && t = t' then (NS.add l ls_old, ls_new)
    else if ACR.ac_equivalent s' t' then (ls_old, ls_new)
    else
      let st' = normalize (s', t') in
      (ls_old, NS.add (Lit.make_axiom st') ls_new)
  in
  L.fold_left rew_nf (NS.empty (), NS.empty ()) (NS.to_list aa)
;;

let reduced rr aa = 
 let ls_old, ls_new = rewrite rr (NS.of_list aa) in NS.add_all ls_new ls_old
;;

let overlaps s rr =
  let ss = List.map Lit.terms s.settings.norm in (* normalized *)
  let rr = Listset.diff rr [Lit.terms l | l <- s.settings.norm] in
  let cps = [(s,t) | s,t <- ACR.cps rr; not (ACR.ac_equivalent s t)] in
  let cps_ss = [(s,t) | s,t <- ACR.cps2 rr ss; not (ACR.ac_equivalent s t)] in
  let cps = [Lit.make_axiom (normalize (s,t)) | s,t <- cps_ss @ cps] in
  if debug s 2 then
    Format.printf "CPs:\n%a\n" NS.print (NS.of_list cps);
  cps
;;

let overlaps s = A.take_time A.t_overlap (overlaps s)

let filter_small s cps =
  let eq_bound = s.heuristic.hard_bound_equations in
  L.partition (fun cp -> Lit.size cp < eq_bound) cps
;;

let succeeds s rr cps =
  let all_joinable ee =
    L.for_all (fun l -> let s,t = Lit.terms l in ACR.are_joinable rr s t) ee
  in
  (*let wcr = ACR.is_wcr rr in*)
  let wcr = all_joinable cps in
  let e0 = s.settings.axioms in
  if debug s 2 && wcr then Format.printf "WCR\n%!";
  wcr && all_joinable e0
;;

let succeeds s rr =
  A.take_time A.t_success_check (succeeds s rr)
;;

let (<|>) = Logic.(<|>)
let (!!) = Logic.(!!)

let c_maxcomp k ctx cc =
  let oriented ((l,r),v) = v <|> (C.find_rule (r,l)) in
  L.iter (fun ((l,r),v) ->
    if l > r then Logic.assert_weighted (oriented ((l,r),v)) k) cc
;;

let rlred state st ccsym_vs =
  let enc s l = try Subst.enc s l with _ -> false in
  let reducible rl s = ACR.is_reducible_rule s rl || enc s (fst rl) in (* FIXME *)
  let reduces rl (s, t) = reducible rl s || reducible rl t in
  if debug state 2 then
    Format.printf "rule %a is reducible by %a\n%!"
      Rule.print st Rules.print [ rl | rl,v <- ccsym_vs; reduces rl st];
  Logic.big_or state.context [ v | rl,v <- ccsym_vs; reduces rl st]
;;

let c_max_red s ccl ccsym_vs =
  let emb l r = try Term.is_embedded l r with _ -> false in
  let not_inc (l,r) = not (Term.is_subterm l r) && not (emb l r) in
  let ccsym_vs = [rl,v | rl,v <- ccsym_vs; Rule.is_rule rl && not_inc rl] in
  L.iter (fun rl -> Logic.assert_weighted (rlred s rl ccsym_vs) 2) ccl
;;

let search_constraints s (ccl, ccsymlvs) =
  let assert_c = function
    | S.Empty -> ()
    | _ -> Format.printf "unknown search_constraints\n%!"
  in L.iter assert_c (constraints s);
  let assert_mc = function
    | S.Oriented -> c_maxcomp 1 s ccsymlvs
    | S.MaxRed -> c_max_red s ccl ccsymlvs
    | S.MaxEmpty -> ()
    | _ -> Format.printf "unknown max search_constraints\n%!"
  in L.iter assert_mc (max_constraints s)
 ;;

(* find k maximal TRSs *)
let max_k s =
  let ctx, cc = s.context, s.equations in
  let k = s.heuristic.k !(A.iterations) in
  let cc_eq = [ Lit.terms n | n <- NS.to_list cc ] in
  let cc_symm = [n | n <- NS.to_list (NS.symmetric cc)] in 
  let cc_symml = [Lit.terms c | c <- cc_symm] in
  L.iter (fun n -> ignore (C.store_rule_var ctx n)) cc_symml;
  (* lookup is not for free: get these variables only once *)
  let is_rule n = Rule.is_rule (Lit.terms n) in
  let cc_symm_vars = [n, C.find_rule (Lit.terms n) | n <- cc_symm; is_rule n] in
  let cc_symml_vars = [Lit.terms n,v | n,v <- cc_symm_vars] in
  if debug s 2 then F.printf "K = %i\n%!" k;
  let strat = termination_strategy s in
  let rec max_k acc ctx n =
    if n = 0 then L.rev acc (* return TRSs in sequence of generation *)
    else (
      A.smt_checks := !A.smt_checks + 1;
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
      else (
        if n != k && debug s 2 then F.printf "no further TRS found\n%!";
        acc)
    )
   in
   (* FIXME: restrict to actual rules?! *)
   A.take_time A.t_orient_constr (St.assert_constraints strat 0 ctx) cc_symml;
   Logic.push ctx; (* backtrack point for Yices *)
   Logic.require (St.bootstrap_constraints 0 ctx cc_symml_vars);
   search_constraints s (cc_eq, cc_symml_vars);
   let trss = max_k [] ctx k in
   Logic.pop ctx; (* backtrack: get rid of all assertions added since push *)
   trss
;;

let rec phi s =
  set_iteration_stats s;
  let i = !A.iterations in
  (**)
  let process (j, s, aa_new) (rr, c, order) =
    let rr = List.map Lit.terms rr in
    if debug s 2 then (
      Format.printf "process TRS %i-%i: %a\n%!" i j Rules.print rr; order#print ());
    let aa = s.equations in
    let irred, red = rewrite rr aa in (* rewrite eqs wrt new TRS *)
    let cps_all = overlaps s rr in
    let cps, cps_large = filter_small s cps_all in
    let cps = reduced rr cps in
    if debug s 2 then
      Format.printf "%d reduced CPs:\n%a" (NS.size cps) NS.print cps;
    let nn = NS.diff (NS.add_all cps red) aa in (* new equations *)
    let sel, rest = select s aa nn in
    if succeeds s rr cps_all then
      raise (Success rr)
    else
       let s' = update_state s (NS.add_list sel aa) in
       (j+1, s', sel @ aa_new)
  in
  try
    let rrs = max_k s in
    let _, s', aa_new = L.fold_left process (0, s, []) rrs in
    phi {s' with new_nodes = aa_new}
  with Success rr -> (SAT, Completion rr)
;;

let preorient state es =
  let es = [ Variant.normalize_rule_dir (Lit.terms e) | e <- es ] in
  let es' = [ if d then e else R.flip e | e,d <- es ] in
  let oriented = [ C.rule_var state.context r | r <- es' ] in
  let keep = Logic.big_and state.context oriented in
  Logic.require keep
;;

let complete (settings, heuristic) es =
  let es = [Lit.make_axiom (normalize (Lit.terms e)) | e <- es] in
  let ctx = Logic.mk_context () in
  let ss = L.map (fun (ts,_,_,_,_) -> ts) heuristic.strategy in
  let es_all = settings.norm @ es in
  let settings = {settings with axioms = es} in
  L.iter (fun strat -> St.init settings strat 0 ctx) ss;
  let start = Unix.gettimeofday () in
  let s = make_state ctx es_all settings heuristic in
  if settings.norm <> [] then
    preorient s settings.norm;
  let res = phi s in
  A.t_process := !(A.t_process) +. (Unix.gettimeofday () -. start);
  Logic.del_context ctx;
  res
;;