open Term
open Subst
open Format

type t = Rule.t * int list * Rule.t * Subst.t

let rename = Rule.rename

let rename_can (l,r) =
 let s = [ x, V i | i,x <- Listx.index (Rule.variables (l,r)) ] in
 (substitute s l, substitute s r)
 
let mgu' s t = try Some (mgu s t) with Not_unifiable -> None
 
let overlap_aux rule1 rule2 =
  let l1,r1 = rename rule1 and l2, r2 = (*rename*) rule2 in
  [ (l1, r1), p, (l2, r2), mgu (subterm_at p l2) l1
  | p <- function_positions l2; 
    unifiable (subterm_at p l2) l1 && 
    (p <> [] || not (Rule.variant (l1, r1) (l2, r2))) ] 


let overlap_aux rule1 rule2 =
  let l1,r1 = rename rule1 and l2, r2 = rename rule2 in
  let add acc p =
   if (p = [] && (Rule.variant (l1, r1) (l2, r2))) then acc
   else
    match mgu' (subterm_at p l2) l1 with
     | None -> acc
     | Some sigma ->  ((l1, r1), p, (l2, r2), sigma)::acc
  in   
  List.rev (List.fold_left add [] (function_positions l2))
;;

let overlap2 rules1 rules2 = 
  Listset.unique
    [ x | rule1 <- rules1; rule2 <- rules2; 
          x <- overlap_aux rule1 rule2 ]

let overlap rules = overlap2 rules rules

let cp_of_overlap ((l1, r1), p, (l2, r2), mu) =
  (Term.substitute mu (replace l2 r1 p), Term.substitute mu r2)

let cp2 rules1 rules2 = 
  [ cp_of_overlap o | o <- overlap2 rules1 rules2 ]

let cp2b b rules1 rules2 =
 let overlap_auxb rule1 rule2 =
  let l1,r1 = rename rule1 and l2, r2 = (*rename*) rule2 in
  let add acc p =
   if (p = [] && (Rule.variant (l1, r1) (l2, r2))) then acc
   else
    match mgu' (subterm_at p l2) l1 with
     | None -> acc
     | Some sigma ->  ((l1, r1), p, (l2, r2), sigma)::acc
  in
  let id x = x in
  let pos = (if b then Listx.remove [] else id) (function_positions l2) in
  List.rev (List.fold_left add [] pos)
 in
 let overlap2b rs1 rs2 =
  Listset.unique [ x | r1 <- rs1; r2 <- rs2; x <- overlap_auxb r1 r2 ]
 in  [ cp_of_overlap o | o <- overlap2b rules1 rules2 ]
;;

(* without renaming *)
let overlap_aux' rule1 rule2 =
  let l1,r1 = rule1 and l2, r2 = rule2 in
  let fpos = if l1 < l2 then function_positions_below_root else function_positions in
  [ (l1, r1), p, (l2, r2), mgu (subterm_at p l2) l1
  | p <- fpos l2;
    unifiable (subterm_at p l2) l1 &&
    (p <> [] || not (Rule.variant (l1, r1) (l2, r2))) ]

let overlap2' rules1 rules2 =
  Listset.unique
    [ x | rule1 <- rules1; rule2 <- rules2;
          x <- overlap_aux' rule1 rule2 ]

let cp2' rules1 rules2 =
  [ cp_of_overlap o | o <- overlap2' rules1 rules2 ]
(* *)

let cp rules = cp2 rules rules

let cp_rules rs = 
 let rules (rl1, _,rl2,_) = Listx.unique [rl1;rl2] in
 [ cp_of_overlap o, rules o | o <- overlap2 rs rs]

let cp_rules2 r1 r2 =
 let rules (rl1, _,rl2,_) = Listx.unique [rl1;rl2] in
 [ cp_of_overlap o, rules o | o <- overlap2 r1 r2]

let is_overlap rule1 p rule2 =
  let l1, r1 = rename rule1 
  and l2, r2 = rename rule2 in
  unifiable l1 (subterm_at p l2) && 
  (p <> [] || not (Rule.variant (l1, r1) (l2, r2)))

let overlapping_aux (((l1, r1) as rule1), ((l2, r2) as rule2)) =
  List.exists 
    (fun p -> is_overlap rule1 p rule2)
    (function_positions l2)

let overlapping rules = 
  List.exists overlapping_aux [ x,y | x <- rules; y <- rules ]

let non_overlapping rules = not (overlapping rules)
