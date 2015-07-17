open Term
open Subst
open Format

type t = Rule.t * int list * Rule.t * Subst.t

let count = ref 0

let fresh () = Signature.fresh_var ()

let rename (l, r) =  
  let s = [ x, V (fresh ()) | x <- variables l ] in
  (substitute s l, substitute s r)

(* AC Overlaps *)
let overlap_aux ac rule1 rule2 =
  let l1, r1 = rename rule1
  and l2, r2 = (*rename*) rule2 in
  [ (l1, r1), p, (l2, r2),  u
  | p <- Ac_term.funs_pos ac l2; 
    ac_unifs <- [Ac_subst.unify ac ((Ac_term.subterm_at l2 p),l1)];
    ns <- [Listx.interval 0 (List.length (Term.direct_subterms l2))];
    ac_unifs <> [] &&
    (p <> ([],ns) || not (Rule.variant (l1, r1) (l2, r2))); u <- ac_unifs ] 

let overlap2 ac rules1 rules2 = 
  Listset.unique
    [ x | rule1 <- rules1; rule2 <- rules2; 
          x <- overlap_aux ac rule1 rule2 ]

let overlap ac rules = overlap2 ac rules rules

(* AC critical pairs *)

let cp_of_overlap ((l1, r1), p, (l2, r2), mu) =
  let u,v = (Term.substitute mu (Ac_term.replace l2 r1 p), Term.substitute mu r2) in
(*       Format.printf "CP between %a and %a is %a \n%!"
    Rule.print (Variant.rename_rule [] (l1, r1)) 
   Rule.print (Variant.rename_rule [] (l2, r2)) Rule.print (u,v);*)
 u,v

let cp2 ac rules1 rules2 = 
 let nontrivial (s,t) = flatten ac s <> (flatten ac t) in
  List.filter nontrivial [ cp_of_overlap o | o <- overlap2 ac rules1 rules2]

let cp ac rules = cp2 ac rules rules
