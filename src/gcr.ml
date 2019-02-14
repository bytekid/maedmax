module Logic = Settings.Logic
module C = Cache
module Strategy = Strategy

let extended_cps trs order =
  let ols = Overlap.overlaps trs in
  let check_overlap_to_cp cps ((l1, r1), p, (l2, r2), mu) =
    let rl1 = Rule.substitute mu (l1, r1) in
    let rl2 = Rule.substitute mu (l2, r2) in
    if order#gt (snd rl1) (fst rl1) || order#gt (snd rl2) (fst rl2) then
      cps
    else
      (Term.substitute mu (Term.replace l2 r1 p), Term.substitute mu r2) :: cps
  in
  List.fold_left check_overlap_to_cp [] ols
;;

let check settings heuristic s ls =
  let trs = List.map Literal.terms ls in
  let ctx = Logic.mk_context () in
  Strategy.init s 0 ctx trs;
  C.store_rule_vars ctx (trs @ [ t,s | s,t <- trs ]); 
  Strategy.assert_constraints s 0 ctx trs;
  let trs_vs = [ r, C.find_rule r | r <- trs] in
  Logic.require (Strategy.bootstrap_constraints 0 ctx trs_vs);
  List.iter (fun (_, v) -> Logic.assert_weighted v 1) trs_vs;
  if Logic.check ctx then (
    let m = Logic.get_model ctx in
    let rls, es = List.partition (fun (_, v) -> Logic.eval m v) trs_vs in
    let rls, es = List.map fst rls, List.map fst es in
    let order = Strategy.decode 0 m s in
    let cps = extended_cps trs order in
    let rew = new Rewriter.rewriter heuristic rls [] order in
    rew#add es;
    let non_joinable (s,t) = fst (rew#nf s) <> fst (rew#nf t) in
    let cps' = List.filter non_joinable cps in
    Format.printf "%i critical critical pairs: %a\n%!" (List.length cps')
      Rules.print cps';
    Ground.all_joinable settings ctx s (trs, es, order) cps' <> None
 ) else false
;;