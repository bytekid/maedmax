open Format
open Term
open Rewriting


let eq_variant (s, t) (u, v) =
  Rule.variant (s, t) (u, v) ||
  Rule.variant (t, s) (u, v)

let eq_subset es1 es2 =
 List.for_all (fun x -> List.exists (eq_variant x) es2) es1

let eq_set_equal es1 es2 = 
 eq_subset es1 es2 && eq_subset es2 es1

let rec var_name fs i = i * 13 (*
  let xs = Listset.diff ["x";"y";"z";"w"] fs in
  let n = List.length xs in
  if i < n then List.nth xs i else 
  let x = sprintf "x%d" (i - n + 1) in 
  if List.mem x fs then
    var_name fs (i + 1)
  else 
    x*)

let rename_rule fs (l, r) =
  let s = [ x, V i | i, x <- Listx.ix (Rule.variables (l, r)) ] in
  (substitute s l, substitute s r)

let rename_rules rs =
  let fs = Rules.functions rs in
  [ rename_rule fs rule | rule <- rs ]

let rec unique ~eq = function
  | [] -> []
  | x :: ys -> x :: unique ~eq [ y | y <- ys; not (eq x y) ]

let rec remove_rule x = function
  | [] -> []
  | y :: ys -> if Rule.variant x y then remove_rule x ys
               else y :: remove_rule x ys

let r_hat rls = [ l, nf rls r | l,r <- rls ]

let reduce rls =
 let rls_hat = r_hat rls in
 [ l, r | l,r <- rls_hat; l = nf (remove_rule (l,r) rls_hat) l ]

let reduce_encomp rls =
 let rls_hat = r_hat rls in
 let proper_enc l l' = Subst.enc l l' && not (Subst.enc l' l) in
 let nonred l = List.for_all (fun (l',r') -> not (proper_enc l l')) rls_hat in
 [ l, r | l,r <- rls_hat; nonred l ]

let right_reduce rls =
 let rls_hat = r_hat rls in
 [ l, r | l,r <- rls_hat; nf (remove_rule (l,r) rls_hat) l <> r ]

let rec lookup_rule (l, r) = function
  | [] -> raise Not_found
  | ((s, t), v) :: _ when Rule.variant (l, r) (s, t) -> v
  | _ :: rs -> lookup_rule (l, r) rs

let rec lookup_eq (s,t) = function
  | [] -> raise Not_found
  | (e, v) :: l when Rule.variant (s, t) e || Rule.variant (t, s) e -> v
  | _ :: l -> lookup_eq (s,t) l

(* 
let rec interreduce = function
  | [] -> [], []
  | (l,r) :: rr ->
	let rr, ee = interreduce rr in 
	if nf rr l <> l then
	  rr, ((l,r) :: ee)
	else
	 ((l, nf rr r) :: rr), ee
*)

let interreduce rr = 
  let rr_prime = [ l, nf rr r | l,r <- rr; nf (remove_rule (l,r) rr) l = l ] in
  let ee_prime = [ l, r | l,r <- rr; nf (remove_rule (l,r) rr) l <> l ] in 
  rr_prime, ee_prime
;;

let union_es es1 es2 = unique ~eq:eq_variant (es1 @ es2)

let normalize_rule_dir (s,t) =
 let s',t' =  Term.rename_canonical s, Term.rename_canonical t in
 let rule, dir = if s' < t' then (s,t), true else (t,s), false in
 rename_rule [] rule, dir
;;

let normalize_rule (s,t) = fst (normalize_rule_dir (s,t))
