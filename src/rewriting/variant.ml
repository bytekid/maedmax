open Format
open Term
open Rewriting


let eq_variant (s, t) (u, v) =
  Rule.variant (s, t) (u, v) || Rule.variant (t, s) (u, v)
;;

let eq_subset es1 es2 =
 List.for_all (fun x -> List.exists (eq_variant x) es2) es1

let eq_set_equal es1 es2 = eq_subset es1 es2 && eq_subset es2 es1

let rec var_name fs i = i * 13

let rename_rule (l, r) =
  let s = [ x, V i | i, x <- Listx.ix (Rule.variables (l, r)) ] in
  (substitute s l, substitute s r)
;;

let rename_rules rs = [ rename_rule rule | rule <- rs ]

let rec unique ~eq = function
  | [] -> []
  | x :: ys -> x :: unique ~eq [ y | y <- ys; not (eq x y) ]
;;

let rec remove_rule x = function
  | [] -> []
  | y :: ys -> if Rule.variant x y then remove_rule x ys
               else y :: remove_rule x ys
;;

let r_hat rls = [ l, nf rls r | l,r <- rls ]

let reduce rls =
 let rls_hat = r_hat rls in
 [ l, r | l,r <- rls_hat; l = nf (remove_rule (l,r) rls_hat) l ]
;;

let reduce_encomp rls =
 let rls_hat = r_hat rls in
 let proper_enc l l' = Subst.enc l l' && not (Subst.enc l' l) in
 let nonred l = List.for_all (fun (l',r') -> not (proper_enc l l')) rls_hat in
 [ l, r | l,r <- rls_hat; nonred l ]
;;

let right_reduce rls =
 let rls_hat = r_hat rls in
 [ l, r | l,r <- rls_hat; nf (remove_rule (l,r) rls_hat) l <> r ]
;;

let interreduce rr = 
  let rr_prime = [ l, nf rr r | l,r <- rr; nf (remove_rule (l,r) rr) l = l ] in
  let ee_prime = [ l, r | l,r <- rr; nf (remove_rule (l,r) rr) l <> l ] in 
  rr_prime, ee_prime
;;

let union_es es1 es2 = unique ~eq:eq_variant (es1 @ es2)

let t_normalize = ref 0.0

let normalize_rule_dir (s,t) =
  let tt = Unix.gettimeofday () in
  let s',t' =  Term.substitute_bot s, Term.substitute_bot t in
  let rule, dir =
    if s = t || s' < t' then (s,t), true
    else if t' < s' then (t,s), false
    else if rename_rule (s,t) < rename_rule (t,s) then (s,t), true
    else (t,s), false
  in
  let res = rename_rule rule, dir in
  t_normalize := !t_normalize +. (Unix.gettimeofday () -. tt);
  res
;;

let normalize_rule (s,t) = fst (normalize_rule_dir (s,t))

let normalize_term t =
  let sigma = [ x, V i | i, x <- Listx.ix (Term.variables t) ] in
  Term.substitute sigma t
;;
