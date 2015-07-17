open Format
open Formatx
open Signature

type t = 
  | V of Signature.var
  | F of Signature.sym * t list

type binding = Signature.var * t

type subst = binding list

let rec print ppf = function
  | V x -> fprintf ppf "%s" (get_var_name x)
  | F (f, ts) -> fprintf ppf "%s(%a)" (get_fun_name f) (print_list print ",") ts

let rec functions_aux = function
  | V _ -> []
  | F (f, ts) -> [f] @ [ g | t <- ts; g <- functions_aux t ]

let functions t = Listx.unique (functions_aux t)

let rec variables_aux = function
  | V x -> [x]
  | F (f, ts) -> [ g | t <- ts; g <- variables_aux t ]

let variables t = Listx.unique (variables_aux t)

let rec count_variable x = function
  | V y when x = y -> 1
  | V _ -> 0
  | F (f, ts) -> Listx.sum [ count_variable x t | t <- ts ]

let is_variable = function
  | V _ -> true
  | F (_, _) -> false

let rec signature = function
  | V _ -> []
  | F (f, ts) -> 
      Listx.unique ((f, List.length ts) :: [ x | t <- ts; x <- signature t ])

let rec subterms = function
  | V _ as t -> [t]
  | F (_, ts) as t -> 
      t :: [ s | ti <- Listx.unique ts; s <- subterms ti ]

let proper_subterms =  function
  | V _ -> []
  | F (_, ts) -> [ s | ti <- Listx.unique ts; s <- subterms ti ]

let root = function
  | V x -> invalid_arg "Term.root"
  | F (f, _) -> f

let is_subterm s t = List.mem s (subterms t)

let is_proper_subterm s t = List.mem s (proper_subterms t)

let apply subst x = try List.assoc x subst with Not_found -> V x

let rec substitute subst = function
  | V x -> apply subst x
  | F (f, ts) -> F (f, [ substitute subst ti | ti <- ts ])

let rec ren = function
  | V x -> V (fresh_var ())
  | F (f, ts) -> F (f, [ ren t | t <- ts ])

let rename l =
  let subst = List.map (fun x -> x,V (fresh_var ())) (variables l) in
  substitute subst l

let rename_canonical t =
  let subst = [x,V i | i,x <- Listx.index (variables t)] in
  substitute subst t
;;

let direct_subterms = function
  | V _ -> []
  | F (_, ss) -> ss

let rec positions = function
  | V x -> [[]]
  | F (_, ts) -> [] :: [ i :: q | i, ti <- Listx.ix ts; q <- positions ti ]

let rec variable_positions = function
  | V _ -> [ [] ]
  | F (_, ts) -> [ i :: q | i, ti <- Listx.ix ts; q <- variable_positions ti ]

let rec function_positions = function
  | V x -> []
  | F (_, ts) -> [] :: [ i :: q | i, ti <- Listx.ix ts; q <- function_positions ti ]

let function_positions_below_root = function
  | V x -> []
  | F (_, ts) -> [ i :: q | i, ti <- Listx.ix ts; q <- function_positions ti ]

let rec subterm_at p t =
  match p, t with
  | [], _ -> t
  | i :: q, F (_, ts) -> subterm_at q (List.nth ts i)
  | _ -> invalid_arg "Term.subterm_at"

let rec replace s t p =
  match s, p with
  | _, [] -> t
  | F (f, ss), i :: q ->
      F (f, [ if i = j then replace sj t q else sj | j, sj <- Listx.ix ss ])
  | _ -> invalid_arg "Term.replace"

let rec count_variables t x =
  match t with
  | V y when x = y -> 1
  | V _ -> 0
  | F (_, ts) -> List.fold_left (+) 0 [ count_variables ti x | ti <- ts ]

let linear t =
  List.for_all (fun x -> count_variables t x = 1) (variables t)

(* for ac *)

let head f = function
  | F(g,gs) when f=g -> true
  | _ -> false

let rec unflatten ac = function
  | V _ as v -> v
  | F(f,ts) ->
     let unflat_args = List.map (unflatten ac) ts in
     if (List.mem f ac) && List.length ts > 2 then
      make_args f unflat_args 
     else F(f,unflat_args)
and make_args f = function
  | h1 :: h2 :: [] -> F(f,[h1;h2])
  | h1 :: h2 :: tt -> 
	F(f,[h1; (make_args f (h2 :: tt))])
  | _ -> invalid_arg "Term.make_args"

(*
let rec flatten ac = function
  | V _ as v -> v
  | F(f,ts) ->
      let ts_flat = List.map (flatten ac) ts in 
      if not (List.mem f ac) then F(f, ts_flat)
      else
	if List.exists (head f) ts 
	then flatten ac (F(f, iter f ts_flat))
	else F(f,ts_flat)
and iter f = function
  | [] -> []
  | (F(g,gs)) :: tt when f=g -> gs @ (iter f tt)
  | h :: tt -> h :: (iter f tt)
*)

(* sorts list of terms such that constants come before compound
   terms where the root has positive arity come before variables *)
let rec lex = function
  | [],[] -> 0
  | [],_ -> -1
  |_, [] -> 1
  | x::xs,y::ys -> let c = my_compare x y in if c=0 then lex (xs,ys) else c
and my_compare t t' =
 match t, t' with
  | V x, V y -> compare x y
  | F _, V _ -> -1
  | V _, F _ -> 1
  | F (_,[]), F(_,_::_) -> -1
  | F(_,_::_), F(_,[]) -> 1
  | F(f,fs), F(g,gs) when f=g -> lex (fs,gs)
  | F(f,_), F(g,_) -> compare f g
;;


let rec flatten ac = function
 | V x -> V x
 | F (f,ts) when List.mem f ac ->
  (match find_arg f [] ts with
    | None -> F (f, List.sort my_compare (List.map (flatten ac) ts))
    | Some (t, ts') -> flatten ac (F(f,direct_subterms t @ ts')))
 | F (f,ts) -> F (f, List.sort my_compare (List.map (flatten ac) ts))
 and
 find_arg f acc = function
  | [] -> None
  | (F(f',_) as t) :: ts' when f=f' -> Some (t, acc@ts')
  | t :: ts' -> find_arg f (t::acc) ts'
;;

let rec size = function
  | V _ -> 1
  | F(_,fs) ->
       let size_arg = [size fi | fi <- fs ] in
       1 + (List.fold_left (+) 0 size_arg)

let is_sharped = function
  | V _ -> false
  | F (f, _) -> String.contains (get_fun_name f) '#' (* dubios *)
;;


let rec is_embedded s t = 
 if s = t then true else
 match s,t with
  | _, V _ -> false
  | F (f,ss), F (g,ts) when f=g ->
   let us = List.map2 (fun x y -> (x,y)) ss ts in
   List.for_all (fun (si,ti) -> is_embedded si ti) us ||
   (List.exists (is_embedded s) ts)
  | _, F (g,ts) -> List.exists (is_embedded s) ts
;;
