open Term
open Subst
open Format

type t = Rule.t * int list * Rule.t * Subst.t

let rename = Rule.rename

let mgu' s t = try Some (mgu s t) with Not_unifiable -> None

let overlaps_between rule1 rule2 =
  let l1,r1 = rename rule1 and l2, r2 = rename rule2 in
  let add acc p =
   if (p = [] && (Rule.variant (l1, r1) (l2, r2))) then acc
   else
    match mgu' (subterm_at p l2) l1 with
     | None -> acc
     | Some sigma -> ((l1, r1), p, (l2, r2), sigma) :: acc
  in   
  List.fold_left add [] (function_positions l2)
;;

let overlap2 rules1 rules2 = 
  Listset.unique [ x | r1 <- rules1;r2 <- rules2; x <- overlaps_between r1 r2 ]

let overlaps rules = overlap2 rules rules

let cp_of_overlap ((l1, r1), p, (l2, r2), mu) =
  (Term.substitute mu (replace l2 r1 p), Term.substitute mu r2)

let cp2 rules1 rules2 = 
  [ cp_of_overlap o | o <- overlap2 rules1 rules2 ]

let cps rules = cp2 rules rules

let cp_rules rs = 
 let rules (rl1, _,rl2,_) = Listx.unique [rl1;rl2] in
 [ cp_of_overlap o, rules o | o <- overlap2 rs rs]

let nontrivial_cps r1 r2 =
  let cps = [ cp_of_overlap x | x <- overlaps_between r1 r2 ] in
  Listset.unique [ s,t | s,t <- cps; not (s = t)]
;;

let is_overlap rule1 p rule2 =
  let l1, r1 = rename rule1 
  and l2, r2 = rename rule2 in
  unifiable l1 (subterm_at p l2) && 
  (p <> [] || not (Rule.variant (l1, r1) (l2, r2)))
