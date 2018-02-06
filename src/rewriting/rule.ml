open Prelude
open Format

type t = Term.t * Term.t

let print ppf (l, r) =
  fprintf ppf "%a -> %a" Term.print l Term.print r

let print_with sep ppf (l, r) =
  fprintf ppf "@[<2>%a %s %a@]" Term.print l sep Term.print r

let to_string = flush_str_formatter <.> print str_formatter

let equal = (=)

let hash = Hashtbl.hash 

let compare = Pervasives.compare 

let variables (l, r) =
  Listx.unique (Term.variables l @ Term.variables r)

let functions (l, r) =
  Listx.unique (Term.functions l @ Term.functions r)

let signature (l, r) =
  Listx.unique (Term.signature l @ Term.signature r)

let is_rule = function
 | Term.V x, _ -> false
 | l, r -> Listset.subset (Term.variables r) (Term.variables l)


let is_non_erasing (l, r) =
  Listset.subset (Term.variables l) (Term.variables r)

let is_duplicating (l, r) =
  let p x = Term.count_variable x r > Term.count_variable x l in
  List.exists p (variables (l, r))

let is_non_duplicating (l, r) =
  let p x = Term.count_variable x l >= Term.count_variable x r in
  List.for_all p (variables (l, r))

let variable_condition (l, r) =
  Listset.subset (Term.variables r) (Term.variables l)

let flip (l,r) = (r,l)

let rename (l, r) =
  let u = Term.F(0,[l;r]) in
  let s = [ x, Term.V (Signature.fresh_var ()) | x <- Term.variables u ] in
  (Term.substitute s l, Term.substitute s r)

let left_linear (l, r) = Term.linear l 

let right_linear (l, r) = Term.linear r

let linear (l, r) = Term.linear l && Term.linear r

(*instantiate rule1 to rule2 *)
let instantiate_to (l1, r1) (l2, r2) =
  let lr1 = Term.F (100, [l1; r1]) and lr2 = Term.F (100, [l2; r2]) in
  Subst.pattern_match lr1 lr2
;;

let is_instance (l1, r1) (l2, r2) =
  let (l2, r2) = rename (l2, r2) in
  let lr1 = Term.F (100, [l1; r1]) and lr2 = Term.F (100, [l2; r2]) in
  Subst.is_instance_of lr1 lr2
;;

let variant (l1, r1) (l2, r2) =
  let lr1 = Term.F (100, [l1; r1]) 
  and lr2 = Term.F (100, [l2; r2]) in
  Subst.is_instance_of lr1 lr2 &&
  Subst.is_instance_of lr2 lr1
;;

let is_proper_instance (l1, r1) (l2, r2) =
  let (l2, r2) = rename (l2, r2) in
  let lr1 = Term.F (100, [l1; r1]) and lr2 = Term.F (100, [l2; r2]) in
  Subst.is_instance_of lr1 lr2 && not (Subst.is_instance_of lr2 lr1)
;;

let rec remove rules rl =
 match rules with
  | [] -> []
  | st :: stt -> 
           if variant rl st 
           then remove stt rl
           else st :: (remove stt rl)

let size (s,t) = Term.size s + Term.size t

let is_dp (l,r) = (Term.is_sharped l) && (Term.is_sharped r)

let is_ground (l,r) = variables (l,r) = []

let map f (l,r) = (f l, f r)

let substitute sigma = map (Term.substitute sigma)

let to_xml (l,r) =
  let lhs = Xml.Element("lhs", [], [Term.to_xml l]) in
  let rhs = Xml.Element("rhs", [], [Term.to_xml r]) in
  Xml.Element("rule", [], [lhs; rhs])
;;

let to_tptp (l,r) =
  let ls,rs = Term.to_tptp l, Term.to_tptp r in
  "cnf(name, axiom,\n    ( " ^ ls ^ " = " ^ rs ^ " ))."
;;
