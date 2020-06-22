module Logic = Settings.Logic
module C = Cache
module Strategy = Strategy

let check strat ls is_json =
  let trs = List.map Literal.terms ls in
  let ctx = Logic.mk_context () in
  Strategy.init {Settings.default with axioms = ls} strat 0 ctx;
  C.store_rule_vars ctx trs; 
  Strategy.assert_constraints strat 0 ctx trs;
  let trs_vs = [ r, C.find_rule r | r <- trs] in
  Logic.require (Strategy.bootstrap_constraints 0 ctx trs_vs);
  Logic.require (Logic.big_and ctx [ v | _,v <- trs_vs ]);
  let res = if Logic.check ctx then (
    if not is_json then Strategy.decode_print 0 (Logic.get_model ctx) strat;
    (*let cps = Overlap.cps trs in
    let rew = new Rewriter.rewriter trs [] Order.default in
    let joinable (s,t) = fst (rew#nf s) = fst (rew#nf t) in
    let j = List.for_all joinable cps in
    Format.printf "complete: %d\n%!" (if j then 1 else 0);*)
    true)
  else false in
  Logic.del_context ctx;
  res
;;