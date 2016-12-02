open Term

let x = V (-1)
let y = V (-2)
let z = V (-3)

let associativity f =
  let lhs = F(f, [F(f, [x; y]); z]) in
  let rhs = F(f, [x; F(f, [y; z])]) in
  (lhs, rhs)
;;

let commutativity f = (F(f, [x; y]), F(f, [y; x]))

let cassociativity f =
  let lhs = F(f, [x; F(f, [y; z])]) in
  let rhs = F(f, [y; F(f, [x; z])]) in
  (lhs, rhs)
;;

let ac_symbols es =
  let is_a f (l,r) = Variant.eq_variant (l,r) (associativity f) in
  let is_c f (l,r) = Variant.eq_variant (l,r) (commutativity f)  in
  let binary_root = function F(_, [_;_]) -> true | _ -> false in
  let fs = [ root l | l,_ <- es@[ r,l | l,r <- es ]; binary_root l ] in
  [ f | f <- fs; List.exists (is_a f) es && List.exists (is_c f) es ]
;;

(* underapproximation of LPO: assuming only subterm property and lexicographic
   left-to-right comparison of arguments below same function symbol *)
let rec gt_lpo var_order = function
  | V x', V y' -> Listx.pos x' var_order < (Listx.pos y' var_order)
  | F (_, ss), t -> List.exists (fun si -> si = t || gt_lpo var_order (si,t)) ss
  | _ -> false
;;

let ac_joinable_for trs (s,t) f var_order =
  if not (List.exists (Rule.variant (associativity f)) trs) then false
  else
  let check_step (l,r) u =
    try
      let sub = Subst.pattern_match l u in
      if not (gt_lpo var_order (substitute sub x, substitute sub y)) then u
      else substitute sub r
    with Subst.Not_matched -> u
  in
  let rec nf u = function
    | [] -> u 
    | p :: ps ->
      let u0 = subterm_at p u in
      let u1 = Rewriting.nf trs u0 in
      let u2 = check_step (commutativity f) u1 in
      let u3 = check_step (cassociativity f) u2 in
      if u0 = u3 then nf u ps
      else let u' = replace u u3 p in (
      nf u' (positions u'))
  in let r = nf s (positions s) = nf t (positions t) in
  r
;;

let ac_joinable trs (s,t) f =
  let vars = Rule.variables (s,t) in
  not (Term.is_variable s && Term.is_variable t) &&
  List.for_all (ac_joinable_for trs (s,t) f) (List.rev (Listx.permutation vars))
;;

let rec joinable (trs, es, acsyms) (s,t) =
  let es_symm = [t,s | s,t <- es] @ es in
  s = t ||
  (Rewriting.nf trs s = (Rewriting.nf trs t)) ||
  (List.exists (Rule.is_instance (s,t)) es_symm) ||
  (List.exists (ac_joinable trs (s,t)) acsyms) ||
  (joinable_args (trs, es, acsyms) (s,t))
and joinable_args system = function
 | F(f, ss), F(f', ts) when f = f' ->
   List.fold_left2 (fun b si ti -> b && joinable system (si,ti)) true ss ts
 | _ -> false
;;

let non_joinable system st = not (joinable system st)

let joinable (trs, es, acsyms) st =
  let j = joinable (trs, es, acsyms) st in
  j 
;;

let add_ac es acs =
  let cs = [ Variant.normalize_rule (commutativity f) | f <- acs ] in
  let cs' = [ Variant.normalize_rule (cassociativity f) | f <- acs ] in
  Listx.unique (cs @ cs' @ es)
;;