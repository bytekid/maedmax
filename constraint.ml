(*** MODULES *****************************************************************)

(*** OPENS *******************************************************************)
open Rewriting

(*** TYPES *******************************************************************)
type c =
 TRS of int | NEG of c | AND of c list | OR of c list |
 BOT | TOP | R of Rule.t

type t = Rule.t * c

let index : (Rule.t, int) Hashtbl.t = Hashtbl.create 128

let count = ref 0
(*** FUNCTIONS ***************************************************************)

let idx r = 
 try Hashtbl.find index r
 with Not_found -> 
  let i = !count in 
(*  Format.printf "indexed %a as %i\n%!" Rule.print r i;*)
  Hashtbl.add index r i; count := i + 1; i

(* * OUTPUT  * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let rec printc ppf = function
 | TRS rs -> Format.fprintf ppf "TRS %i" rs
 | R r -> (*Rule.print ppf r*) Format.fprintf ppf "%i" (idx r)
 | NEG cn -> Format.fprintf ppf "(NOT %a)" printc cn
 | AND cs -> Format.fprintf ppf "(%a)" (Formatx.print_list printc " AND ") cs
 | OR cs -> Format.fprintf ppf "(%a)" (Formatx.print_list printc " OR ") cs
 | BOT -> Format.fprintf ppf "F"
 | TOP -> Format.fprintf ppf "T"

let print_ceq ppf (st,c) =
(* Format.fprintf ppf "@[@[%a@]| ...@]" Rule.print st*)
 Format.fprintf ppf "%i: @[@[%a@]| %a@]" (idx st) Rule.print st printc c

let print ppf c_rules =
  Format.fprintf ppf "@[<v 0>%a@]" (Formatx.print_list print_ceq "@ ") c_rules

(* * CONSTRAINT OPERATORS * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let (<&>) c c' = 
 match c,c' with
  | TOP, y -> y
  | x,TOP -> x
  | BOT, _
  |_,BOT -> BOT
  | TRS r, NEG (TRS r') when r=r' -> BOT
  | NEG (TRS r), TRS r' when r=r' -> BOT
(*  | AND xs, AND ys -> AND (Listx.unique (List.rev_append xs ys))
  | AND xs, y -> AND (Listx.unique (y::xs))
  | x, AND ys -> AND (Listx.unique (x::ys))*)
  | x,y -> (AND [x;y])
;;

let rec big_and = function
 | [] -> BOT
 | [x] -> x
 | x :: xs -> x <&> (big_and xs)
;; 

let (<|>) c c' = 
 match c,c' with
  | TOP, _
  | _,TOP -> TOP
  | BOT, x -> x
  | x,BOT -> x
  | TRS r, TRS r' when r=r' -> TRS r
  | x, AND [y;x'] when (x=x') -> x
  | x, AND [x';y] when (x=x') -> x
  | AND [x;y], AND [x';NEG y'] when ((x=x') && (y=y')) -> x
  | x,y -> (OR [x;y])
;;

let rec rules = function
 | R r -> [idx r]
 | NEG cn -> rules cn
 | AND cs -> List.concat (List.map rules cs)
 | OR cs -> List.concat (List.map rules cs)
 | _ -> []
