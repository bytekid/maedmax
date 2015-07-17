(*** MODULES *****************************************************************)
module St = Statistics
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yices

(*** FUNCTIONS ***************************************************************)
let make_constr ctx f ce =
 let assert_constr (l,r) =
  let c (s,t) = mk_or ctx [| mk_not ctx (C.find_rule (s,t)); f ctx s t |] in
  assert_simple ctx (c (l,r));
  assert_simple ctx (c (r,l))
 in
 let consider (lr,_) = C.assert_rule lr assert_constr in
 List.iter consider ce
;;
