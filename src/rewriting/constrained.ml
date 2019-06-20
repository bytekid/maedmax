(*** MODULES ******************************************************************)
module Logic = Order.Logic

module Equality = struct
  type bv_expr =
    | Var of string * int
    | HexConst of string * int (* value, bitwidth *)
    | Bv_not of bv_expr
    | Bv_and of bv_expr * bv_expr
    | Bv_or of bv_expr * bv_expr
    | Bv_xor of bv_expr * bv_expr
    | Bv_neg of bv_expr
    | Bv_add of bv_expr * bv_expr
    | Bv_sub of bv_expr * bv_expr
    | Bv_mult of bv_expr * bv_expr
    | Bv_udiv of bv_expr * bv_expr
    | Bv_sdiv of bv_expr * bv_expr
    | Bv_shl of bv_expr * bv_expr
    | Bv_ashr of bv_expr * bv_expr
    | Bv_lshr of bv_expr * bv_expr
    | Fun of string * int * bv_expr list

    type bool_expr =
    | Top
    | Bot 
    | And of bool_expr * bool_expr
    | Or of bool_expr * bool_expr
    | Not of bool_expr
    | Equal of bv_expr * bv_expr
    | Bv_lt of bv_expr * bv_expr
    | Bv_gt of bv_expr * bv_expr
    | Bv_le of bv_expr * bv_expr
    | Bv_ge of bv_expr * bv_expr
    | Pred of string * int * bv_expr list

  type t = Rule.t * bool_expr


  let fprintf = Format.fprintf

  let rec print_bv ppf = function
    | Var (v, bits) -> fprintf ppf "%s.%d" v bits
    | HexConst(c, bits) -> fprintf ppf "%s.%d" c bits
    | Bv_and(a, b) -> fprintf ppf "(%a & %a)" print_bv a print_bv b 
    | Bv_or(a, b) -> fprintf ppf "(%a | %a)" print_bv a print_bv b 
    | Bv_xor(a, b) -> fprintf ppf "(%a ^ %a)" print_bv a print_bv b 
    | Bv_not(a) -> fprintf ppf "! %a" print_bv a
    | Bv_neg(a) -> fprintf ppf "~ %a" print_bv a
    | Bv_add(a, b) -> fprintf ppf "(%a + %a)" print_bv a print_bv b  
    | Bv_sub(a, b) -> fprintf ppf "(%a - %a)" print_bv a print_bv b 
    | Bv_mult(a, b) -> fprintf ppf "(%a * %a)" print_bv a print_bv b 
    | Bv_udiv(a, b) -> fprintf ppf "(%a /u %a)" print_bv a print_bv b 
    | Bv_sdiv(a, b) -> fprintf ppf "(%a /s %a)" print_bv a print_bv b 
    | Bv_shl(a, b) -> fprintf ppf "(%a << %a)" print_bv a print_bv b 
    | Bv_ashr(a, b) -> fprintf ppf "(%a >>s %a)" print_bv a print_bv b 
    | Bv_lshr(a, b) -> fprintf ppf "(%a >>u %a)" print_bv a print_bv b 
    | Fun(n, b,es) ->
      fprintf ppf "%s.%d(%a)" n b (Formatx.print_list print_bv ",") es
  ;;

  let rec print_b ppf = function
    | Top -> fprintf ppf "T"
    | Bot -> fprintf ppf "F"
    | And(a, b) -> fprintf ppf "(%a /\\ %a)" print_b a print_b b 
    | Or(a, b) -> fprintf ppf "(%a \\/ %a)" print_b a print_b b 
    | Not(a) -> fprintf ppf "! %a" print_b a
    | Equal(a, b) -> fprintf ppf "(%a = %a)" print_bv a print_bv b 
    | Bv_le(a, b) -> fprintf ppf "(%a <= %a)" print_bv a print_bv b 
    | Bv_lt(a, b) -> fprintf ppf "(%a < %a)" print_bv a print_bv b 
    | Bv_ge(a, b) -> fprintf ppf "(%a >= %a)" print_bv a print_bv b 
    | Bv_gt(a, b) -> fprintf ppf "(%a > %a)" print_bv a print_bv b 
    | Pred(n, b, es) ->
      fprintf ppf "%s.%d(%a)" n b (Formatx.print_list print_bv ",") es
  ;;

  let print_with sep ppf ((l, r), c) =
    fprintf ppf "%a %s %a [%a]" Term.print l sep Term.print r print_b c
  ;;

  let print = print_with "="
end

module Literal = struct
  module BV = Logic.BitVector 

  open Equality
  open Logic
  open Logic.Int

  type t = {
    terms: Rule.t;
    constr: Logic.t
 }

  let logic_of_expr =
    let rec of_bexpr ctx = function
      | Top -> mk_true ctx 
      | Bot -> mk_false ctx 
      | And(a, b) -> (of_bexpr ctx a) <&> (of_bexpr ctx b)
      | Or(a, b) -> (of_bexpr ctx a) <|> (of_bexpr ctx b)
      | Not(a) -> !! (of_bexpr ctx a)
      | Equal(a, b) -> (of_bvexpr ctx a) <=> (of_bvexpr ctx b) 
      | Bv_le(a, b) -> (of_bvexpr ctx b) <>=> (of_bvexpr ctx a)
      | Bv_lt(a, b) -> (of_bvexpr ctx b) <>> (of_bvexpr ctx a)
      | Bv_ge(a, b) -> (of_bvexpr ctx a) <>=> (of_bvexpr ctx b) 
      | Bv_gt(a, b) -> (of_bvexpr ctx a) <>> (of_bvexpr ctx b)
      | Pred(n, b, es) -> failwith "Constrained.of_bexpr"
    and of_bvexpr ctx = function
      | Var(v, bits) -> BV.mk_var ctx v bits
      | HexConst(c, bits) -> BV.mk_num ctx c bits
      | Bv_and(a, b) -> BV.mk_and (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_or(a, b) -> BV.mk_or (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_xor(a, b) -> BV.mk_xor (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_not(a) -> BV.mk_not (of_bvexpr ctx a)
      | Bv_add(a, b) -> BV.mk_add (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_sub(a, b) -> BV.mk_sub (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_neg(a) -> BV.mk_neg (of_bvexpr ctx a)
      | Bv_mult(a, b) -> BV.mk_mul (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_udiv(a, b) -> BV.mk_udiv (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_sdiv(a, b) -> BV.mk_sdiv (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_shl(a, b) -> BV.mk_shl (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_ashr(a, b) -> BV.mk_ashr (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_lshr(a, b) -> BV.mk_lshr (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Fun(n, b,es) -> failwith "Constrained.of_bvexpr"
    in of_bexpr
  ;; 

  let of_equation ctx (rl, e) = { terms = rl; constr = logic_of_expr ctx e }
end

(*** OPENS *******************************************************************)
open Prelude
