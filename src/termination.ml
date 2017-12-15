open Yicesx

let check s ls is_json =
 let trs = List.map Literal.terms ls in
 let ctx = Yices.mk_context () in
 Strategy.init s 0 ctx trs;
 Cache.store_rule_vars ctx (trs @ [ t,s | s,t <- trs ]); 
 Strategy.assert_constraints s 0 ctx trs;
 require (Strategy.bootstrap_constraints 0 ctx trs);
 require (big_and ctx [ Cache.find_rule st | st <- trs ]);
 if check ctx then (
   if not is_json then Strategy.decode_print 0 (get_model ctx) s;
   (*let cps = Overlap.cps trs in
   let rew = new Rewriter.rewriter trs [] Order.default in
   let joinable (s,t) = fst (rew#nf s) = fst (rew#nf t) in
   let j = List.for_all joinable cps in
   Format.printf "complete: %d\n%!" (if j then 1 else 0);*)
   true)
 else false
;;