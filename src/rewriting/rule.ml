open Prelude
open Format

module Sub = Term.Sub
module Sig = Signature
module T = Term

type t = T.t * T.t

let print ppf (l, r) =
  fprintf ppf "%a -> %a" T.print l T.print r

let print_with sep ppf (l, r) =
  fprintf ppf "%a %s %a" T.print l sep T.print r

let to_string = flush_str_formatter <.> print str_formatter

let equal = (=)

let hash = Hashtbl.hash 

let compare = Pervasives.compare 

let variables (l, r) =
  Listx.unique (T.variables l @ T.variables r)

let functions (l, r) =
  Listx.unique (T.functions l @ T.functions r)

let signature (l, r) =
  Listx.unique (T.signature l @ T.signature r)

let is_rule = function
 | T.V x, _ -> false
 | l, r -> Listset.subset (T.variables r) (T.variables l)


let is_non_erasing (l, r) =
  Listset.subset (T.variables l) (T.variables r)

let is_duplicating (l, r) =
  let p x = T.count_variable x r > T.count_variable x l in
  List.exists p (variables (l, r))

let is_non_duplicating (l, r) =
  let p x = T.count_variable x l >= T.count_variable x r in
  List.for_all p (variables (l, r))

let variable_condition (l, r) =
  Listset.subset (T.variables r) (T.variables l)

let flip (l,r) = (r,l)

let renaming_for (l, r) =
  let vs = T.variables (T.F(0, [l; r])) in
  List.fold_left (fun s x -> Sub.add x (T.V (Sig.fresh_var ())) s) Sub.empty vs
  (*[ x, T.V (Signature.fresh_var ()) | x <- T.variables u ]*)
;;

let rename (l, r) =
  let s = renaming_for (l, r) in
  (T.substitute s l, T.substitute s r)
;;

let rename_canonical ?(from=100) (l, r) =
  let u = Term.F(0,[l;r]) in
  let var i = T.V (from + i) in
  let vs = Listx.ix (T.variables u) in
  let s = List.fold_left (fun s (i,x) -> Sub.add x (var i) s) Sub.empty vs in
  (*let s = [ x, var i | i, x <- Listx.ix (T.variables u) ] in*)
  (T.substitute s l, T.substitute s r)
;;

let left_linear (l, r) = T.linear l 

let right_linear (l, r) = T.linear r

let linear (l, r) = T.linear l && T.linear r

(*instantiate rule1 to rule2 *)
let instantiate_to (l1, r1) (l2, r2) =
  let lr1 = T.F (100, [l1; r1]) and lr2 = T.F (100, [l2; r2]) in
  Subst.pattern_match lr1 lr2
;;

let is_instance (l1, r1) (l2, r2) =
  let (l2, r2) = rename (l2, r2) in
  let lr1 = T.F (100, [l1; r1]) and lr2 = T.F (100, [l2; r2]) in
  Subst.is_instance_of lr1 lr2
;;

let variant (l1, r1) (l2, r2) =
  let lr1 = T.F (100, [l1; r1]) 
  and lr2 = T.F (100, [l2; r2]) in
  Subst.is_instance_of lr1 lr2 &&
  Subst.is_instance_of lr2 lr1
;;

let equation_variant rl (l,r) = variant rl (l,r) || variant rl (r,l)

let is_proper_instance (l1, r1) (l2, r2) =
  let (l2, r2) = rename (l2, r2) in
  let lr1 = T.F (100, [l1; r1]) and lr2 = T.F (100, [l2; r2]) in
  Subst.is_instance_of lr1 lr2 && not (Subst.is_instance_of lr2 lr1)
;;

let rec remove rules rl =
 match rules with
  | [] -> []
  | st :: stt -> 
           if variant rl st 
           then remove stt rl
           else st :: (remove stt rl)

let size (s,t) = T.size s + T.size t

let is_dp (l,r) = (T.is_sharped l) && (T.is_sharped r)

let is_ground (l,r) = variables (l,r) = []

let map f (l,r) = (f l, f r)

let substitute sigma = map (T.substitute sigma)

let substitute_uniform t = map (T.substitute_uniform t)

let to_xml (l,r) =
  let lhs = Xml.Element("lhs", [], [T.to_xml l]) in
  let rhs = Xml.Element("rhs", [], [T.to_xml r]) in
  Xml.Element("rule", [], [lhs; rhs])
;;

let to_tptp (l,r) =
  let ls,rs = T.to_tptp l, T.to_tptp r in
  "cnf(name, axiom,\n    ( " ^ ls ^ " = " ^ rs ^ " ))."
;;
