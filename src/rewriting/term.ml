(*** OPENS *******************************************************************)
open Format
open Formatx
open Signature

(*** TYPES *******************************************************************)
type t = 
  | V of Signature.var
  | F of Signature.sym * t list

type pos = int list

type binding = Signature.var * t

type subst = binding list

(*** FUNCTIONS ***************************************************************)
let compare = Pervasives.compare

let rec print ppf = function
  | V x -> fprintf ppf "%s" (get_var_name x)
  | F (f, []) -> fprintf ppf "%s" (get_fun_name f)
  | F (f, ts) -> fprintf ppf "%s(%a)" (get_fun_name f) (print_list print ",") ts

let to_string t = flush_str_formatter (print str_formatter t)

let rec functions_aux = function
  | V _ -> []
  | F (f, ts) -> f :: [g | t <- ts; g <- functions_aux t]

let functions t = Listx.unique (functions_aux t)

let rec variables_aux = function
  | V x -> [x]
  | F (f, ts) -> [g | t <- ts; g <- variables_aux t]

let variables t = Listx.unique (variables_aux t)

let rec count_variable x = function
  | V y when x = y -> 1
  | V _ -> 0
  | F (f, ts) -> Listx.sum [count_variable x t | t <- ts]

let is_variable = function
  | V _ -> true
  | F (_, _) -> false

let rec signature = function
  | V _ -> []
  | F (f, ts) -> 
    Listx.unique ((f, List.length ts) :: [x | t <- ts; x <- signature t])

let rec subterms = function
  | V _ as t -> [t]
  | F (_, ts) as t -> 
      t :: [s | ti <- Listx.unique ts; s <- subterms ti]

let proper_subterms =  function
  | V _ -> []
  | F (_, ts) -> [s | ti <- Listx.unique ts; s <- subterms ti]

let root = function
  | V x -> invalid_arg "Term.root"
  | F (f, _) -> f

let args = function
  | V x -> invalid_arg "Term.args"
  | F (_, args) -> args

let is_subterm s t = List.mem s (subterms t)

let is_proper_subterm s t = List.mem s (proper_subterms t)

let apply subst x = try List.assoc x subst with Not_found -> V x

let rec substitute subst = function
  | V x -> apply subst x
  | F (f, ts) -> F (f, [substitute subst ti | ti <- ts])

let rename_canonical t =
  let subst = [x, V i | i, x <- Listx.index (variables t)] in
  substitute subst t

let rec substitute_bot = function
  | V x -> V 0
  | F (f, ts) -> F (f, [substitute_bot ti | ti <- ts])

let direct_subterms = function
  | V _ -> []
  | F (_, ss) -> ss

let rec positions = function
  | V x -> [[]]
  | F (_, ts) -> [] :: [i :: q | i, ti <- Listx.ix ts; q <- positions ti]

let rec variable_positions = function
  | V _ -> [ [] ]
  | F (_, ts) -> [i :: q | i, ti <- Listx.ix ts; q <- variable_positions ti]

let rec function_positions = function
  | V x -> []
  | F (_, ts) -> [] :: [i :: q | i, u <- Listx.ix ts; q <- function_positions u]

let function_positions_below_root = function
  | V x -> []
  | F (_, ts) -> [i :: q | i, ti <- Listx.ix ts; q <- function_positions ti]

let rec subterm_at p t =
  match p, t with
  | [], _ -> t
  | i :: q, F (_, ts) -> subterm_at q (List.nth ts i)
  | _ -> invalid_arg "Term.subterm_at"

let rec replace s t p =
  match s, p with
  | _, [] -> t
  | F (f, ss), i :: q ->
      F (f, [if i = j then replace sj t q else sj | j, sj <- Listx.ix ss])
  | _ -> invalid_arg "Term.replace"

let rec count_variables t x =
  match t with
  | V y when x = y -> 1
  | V _ -> 0
  | F (_, ts) -> List.fold_left (+) 0 [count_variables ti x | ti <- ts]

let linear t =
  List.for_all (fun x -> count_variables t x = 1) (variables t)

(* for ac *)

let head f = function
  | F(g, gs) when f = g -> true
  | _ -> false

let rec unflatten ac = function
  | V _ as v -> v
  | F(f,ts) ->
     let unflat_args = List.map (unflatten ac) ts in
     if (List.mem f ac) && List.length ts > 2 then
      make_args f unflat_args 
     else F(f,unflat_args)
and make_args f = function
  | h1 :: h2 :: [] -> F(f, [h1; h2])
  | h1 :: h2 :: tt -> 
	F(f,[h1; (make_args f (h2 :: tt))])
  | _ -> invalid_arg "Term.make_args"

let rec flatten' acs = function
 | V _ as v -> v
 | F (f, ts) ->
  let ts' = List.map (flatten' acs) ts in
  if not (List.mem f acs) then F(f, ts')
  else
   let frooted = function V _ -> false | F(g, _) -> f = g in 
   let (tsf, tsr) = List.partition frooted ts' in
   F (f, (List.concat [args ti | ti <- tsf]) @ tsr)

let rec args_sort syms = function
  | F (f, ts) ->
  let ts' =  List.map (args_sort syms) ts in
  F (f, if List.mem f syms then List.sort compare ts' else ts')
  | v -> v

let flatten acs t = args_sort acs (flatten' acs t)

let rec size = function
  | V _ -> 1
  | F(_,fs) ->
       let size_arg = [size fi | fi <- fs] in
       1 + (List.fold_left (+) 0 size_arg)

let rec depth = function
  | V _ -> 1
  | F(_,fs) ->
       let depth_arg = [depth fi | fi <- fs] in
       1 + (List.fold_left max 0 depth_arg)

let is_sharped = function
  | V _ -> false
  | F (f, _) -> String.contains (get_fun_name f) '#' (* FIXME *)

let rec is_embedded s t = 
  if s = t then true else
  match s,t with
  | _, V _ -> false
  | F (f, ss), F (g, ts) when f=g ->
    let us = List.map2 (fun x y -> (x, y)) ss ts in
    List.for_all (fun (si,ti) -> is_embedded si ti) us ||
    (List.exists (is_embedded s) ts)
  | _, F (g, ts) -> List.exists (is_embedded s) ts

let rec to_xml = function
  | V x -> Xml.Element("var", [], [Xml.PCData (get_var_name x)])
  | F(f, ts) ->
    let xs = List.map (fun a -> Xml.Element ("arg", [], [to_xml a])) ts in
    let name = Xml.Element("name", [], [Xml.PCData (get_fun_name f)]) in
    Xml.Element("funapp", [], name :: xs)

let rec to_tptp = function
  | V x -> "X" ^ (get_var_name x)
  | F(f, []) -> "f" ^ (get_fun_name f)
  | F(f, t1 :: ts) ->
    let s = List.fold_left (fun s u -> s ^ "," ^ (to_tptp u)) (to_tptp t1) ts in
    "f" ^ (get_fun_name f) ^ "(" ^ s ^ ")"

let similarity_wrt s t =
  let exists p s = try let _ = subterm_at p s in true with _ -> false in
  let same p s t = 
    match subterm_at p s, subterm_at p t with
      V _, V _ -> true
    | F (f,_), F (g,_) when f=g -> true
    | _ -> false
  in
  let pos = positions t in
  let l = List.length [ p | p <- pos; exists p s && same p s t ] in
  float_of_int l /. (float_of_int (List.length pos))

let similarity acs cs s t = (similarity_wrt s t +. similarity_wrt t s) /. 2.
