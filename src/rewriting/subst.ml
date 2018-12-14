(*** OPENS *******************************************************************)
open Format
open Term

(*** TYPES *******************************************************************)
type t = subst

(*** EXCEPTIONS **************************************************************)
exception Not_unifiable

exception Not_matched

(*** FUNCTIONS ***************************************************************)
let empty = []

let add x t subst =
  if V x = t then subst else
  (x, t) :: [y, substitute [x, t] term | (y, term) <- subst; not (x = y)]
;;

let after mu sigma = 
  let mu' = [x,t | x,t <- mu; not (List.exists (fun (y, _) -> x = y) sigma) ] in
  [x, substitute mu t | x,t <- sigma ] @ mu'
;;

let rec unify_aux subst = function
  | [] -> subst
  | (s, t) :: eqs when s = t -> unify_aux subst eqs
  | (V x, t) :: eqs when not (List.mem x (variables t)) ->
    let eqs' = [substitute [x, t] l, substitute [x, t] r | l, r <- eqs] in
    unify_aux (add x t subst) eqs'
  | (t, V x) :: eqs when not (List.mem x (variables t)) ->
    let eqs' = [substitute [x, t] l, substitute [x, t] r | l, r <- eqs] in
    unify_aux (add x t subst) eqs'
  | (F (f, ss), F (g, ts)) :: eqs when f = g ->
    unify_aux subst ((List.combine ss ts) @ eqs)
  | _ -> raise Not_unifiable
;;

let check unifier l r = substitute unifier l = substitute unifier r

let mgu_list eqs = unify_aux [] eqs

let mgu l r = mgu_list [(l, r)]

let unifiable term1 term2 = 
  try
    ignore (mgu term1 term2);
    true
  with Not_unifiable -> false 
;;

let rec pattern_match' subst = function 
  | [] -> subst
  | (V x as l, t) :: list ->
    if List.mem_assoc x subst then (
      if Term.substitute subst l <> t then raise Not_matched;
      pattern_match' subst list
    ) else
      pattern_match' ((x, t) :: subst) list
  | (F (f, ss), F (g, ts)) :: list when f = g ->
    pattern_match' subst ((List.combine ss ts) @ list)
  | _ -> raise Not_matched
;;

let pattern_match t1 t2 = pattern_match' [] [t1, t2]

let is_instance_of t1 t2 =
  try ignore (pattern_match t2 t1); true
  with Not_matched -> false
;;

let enc t1 t2 = List.exists (fun t -> is_instance_of t t2) (Term.subterms t1)

let is_renaming subst =
  let dom, ran = [x | x,_ <- subst], [t | _,t <- subst] in
  (List.for_all is_variable ran) &&
  (List.length (Listx.unique ran) = List.length dom)
;;

(* tau after rho *)
let compose (rho:t) (tau:t) =
  [x, substitute tau t| x, t <- rho] @
  [x, t | x, t <- tau; not (List.mem_assoc x rho)]
;;
