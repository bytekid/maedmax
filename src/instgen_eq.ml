
(*** MODULES ******************************************************************)
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
module Sig = Signature

(*** OPENS ********************************************************************)
open Settings
open Ckb

(*** FUNCTIONS ****************************************************************)

let init_settings (settings_flags, heuristic_flags) axs gs =
  A.restart ();
  A.iterations := 0;
  let axs_eqs = [ Lit.terms a | a <- axs ] in
  let acs = Ac.symbols axs_eqs in
  let cs = Commutativity.symbols axs_eqs in
  let s =
    { !settings with
      ac_syms = acs;
      auto = settings_flags.auto;
      axioms = axs;
      debug = settings_flags.debug;
      gs = gs;
      only_c_syms = Listset.diff cs acs;
      signature = Rules.signature (axs_eqs @ gs);
      tmp = settings_flags.tmp;
      unfailing = settings_flags.unfailing
    }
  in
  let h = { !heuristic with n = heuristic_flags.n } in
  set_settings s;
  set_heuristic h;
  (* initialize trace, needed to get instances *)
  Trace.add_initials axs_eqs;
  Trace.add_initial_goal gs
;;

let rec phi s =
  set_iteration_stats s;
  Select.reset ();
  let aa, gs = s.equations, s.goals in
  (**)
  (* TODO: update redcount cp_count etc? *)
  let process (j, s, aa_new) ((rr, c, order) as sys) =
    let aa, gs = s.equations, s.goals in
    let rew = get_rewriter s.context j sys in
    let irred, red = rewrite rew aa in (* rewrite eqs wrt new TRS *)

    let gs_red', gs_big = reduced_goals rew gs in
    let gs = NS.add_all gs_red' gs in

    let aa_for_ols = equations_for_overlaps irred aa in
    let cps',_ = overlaps s rr aa_for_ols in
    let eq_bound = !heuristic.hard_bound_equations in
    let cps = NS.filter (fun cp -> Lit.size cp < eq_bound) cps' in
    let cps_large = NS.filter (fun cp -> Lit.size cp >= eq_bound) cps' in
    let cps = reduced rew cps in
    let nn = NS.diff (NS.add_all cps red) aa in (* new equations *)
    let sel, rest = Select.select (aa,rew) nn in

    let go = overlaps_on rr aa_for_ols gs in
    let go = NS.filter (fun g -> Lit.size g < !heuristic.hard_bound_goals) go in
    let gcps, gcps' = reduced_goals rew go in
    let gs' = NS.diff (NS.add_all gs_big (NS.add_all gcps' gcps)) gs in
    let gg, grest = Select.select_goals (aa,rew) !heuristic.n_goals gs' in

    if !(Settings.track_equations) <> [] then
      A.update_proof_track (sel @ gg) (NS.to_list rest @ (NS.to_list grest));
    store_remaining_nodes s.context rest grest;
    let ieqs = NS.to_rules (NS.filter Lit.is_inequality aa) in
    let cc = (!settings.axioms, cps, cps_large) in
    let irr = NS.filter Lit.not_increasing (NS.symmetric irred) in

    let gs' = NS.add_list gg gs in
    match succeeds s (rr, irr) rew cc ieqs gs' with
    | Some r -> raise (Success r)
    | None ->
       let s' = update_state s (NS.add_list sel aa) gs' in
       (j+1, s', sel @ aa_new)
  in
  try
    let s = update_state s aa gs in
    let _, s', aa_new = L.fold_left process (0, s, []) (max_k s) in
    phi {s' with new_nodes = aa_new}
  with Success r -> r
;;

(* FIXME: no trivial equations should be passed *)
let check ctx flags lits =
  Format.printf "--- start equational reasoning ----------------------------\n";
  set_settings (fst flags);
  set_heuristic (snd flags);
  Trace.clear ();
  let (es, gs) as input = L.partition Lit.is_equality lits in
  if not (L.for_all (fun e -> Lit.is_equality e || Lit.is_ground e) es) then
    raise Fail; (* TODO: why? *)
  let es0 = L.sort Pervasives.compare (L.map Lit.normalize es) in
  let gs0 = L.map Lit.normalize gs in
  Select.init es0 gs0;
  init_settings flags es0 [ Lit.terms g | g <- gs0 ];
  (* TODO: support restarts, eg. remember state *)
  let cas = [ Ac.cassociativity f | f <- !settings.ac_syms ] in
  let es0 = [ Lit.make_axiom (Variant.normalize_rule r) | r <- cas ] @ es0 in
  let ans, proof = phi (make_state ctx es0 (NS.of_list gs0)) in
  Format.printf "--- end equational reasoning ------------------------------\n";
  ans, Trace.proof_literal_instances input proof
;; 