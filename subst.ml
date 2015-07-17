open Format
open Term

type t = subst

exception Not_unifiable

exception Not_matched

let add x t subst =
  if V x = t then subst else
    (x, t) :: 
    [ y, substitute [x, t] term | (y, term) <- subst; not (x = y) ]

let rec unify_aux subst = function
  | [] -> subst
  | (s, t) :: eqs when s = t -> unify_aux subst eqs
  | (V x, t) :: eqs 
  | (t, V x) :: eqs when not (List.mem x (Term.variables t)) ->
      unify_aux (add x t subst)
	[ substitute [x, t] l, substitute [x, t] r | l, r <- eqs ]
  | (F (f, ss), F (g, ts)) :: eqs when f = g ->
      unify_aux subst ((List.combine ss ts) @ eqs)
  | _ -> raise Not_unifiable

let check unifier l r = 
  substitute unifier l = substitute unifier r

let mgu_list eqs =
  let u = unify_aux [] eqs in
  (*assert (List.for_all (fun (l, r) -> check u l r) eqs);*)
  u

let mgu l r = 
  let u = mgu_list [(l, r)] in
  (*assert (check u l r); *)
  u

let unifiable term1 term2 = 
  try ignore (mgu term1 term2); true with Not_unifiable -> false 



let rec pattern_match' subst = function 
  | [] -> subst
  | (V x as l, t) :: list 
    when List.mem_assoc x subst && Term.substitute subst l = t -> 
      pattern_match' subst list 
  | (V x, t) :: list when not (List.mem_assoc x subst) -> 
      pattern_match' ((x, t) :: subst) list
  | (F (f, ss), F (g, ts)) :: list 
    when (f = g) && (List.length ss = (List.length ts)) ->
      pattern_match' subst ((List.combine ss ts) @ list)
  | _ -> raise Not_matched

let pattern_match t1 t2 =
  let m = pattern_match' [] [t1, t2] in 
  assert (Term.substitute m t1 = t2); m

let is_instance_of t1 t2 =
  try ignore (pattern_match t2 t1); true with Not_matched -> false

let enc t1 t2 = 
 List.exists (fun t -> is_instance_of t t2) (Term.subterms t1)
