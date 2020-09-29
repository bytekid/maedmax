(*** OPENS *******************************************************************)
open Z3

(*** MODULES *****************************************************************)
module B = Boolean
module Arith = Arithmetic
module I = Arith.Integer
module Real = Arith.Real
module BV = BitVector
module Big_int = Big_int_Z

(*** TYPES *******************************************************************)
type context = {
  ctx : Z3.context;
  opt: Optimize.optimize
}

type t = {
  ctx : context;
  expr: Expr.expr
}

type model = Z3.Model.model

(*** GLOBALS *****************************************************************)
let var_count = ref 0

(*** FUNCTIONS ***************************************************************)
let mk c e = { ctx = c; expr = e }

let ctx zexpr = zexpr.ctx

let z3ctx zexpr = zexpr.ctx.ctx

let opt zexpr = zexpr.ctx.opt

let expr zexpr = zexpr.expr

let is_true x = B.is_true x.expr

let is_false x = B.is_false x.expr

let to_int i =
  try Big_int.int_of_big_int i
  with _ -> 
    Format.printf "%s\n%!" (Big_int.string_of_big_int i);
    failwith "Z3x conversion error"
;;

let is_zero x = try to_int (I.get_big_int x.expr) == 0 with _ -> false

let mk_context _ =
  let c = mk_context [("timeout", "3000")] in
  { ctx = c; opt = Optimize.mk_opt c}
;;

let del_context _ = ()

let reset _ = mk_context ()

let show x = Format.printf "%s\n%!" (Expr.to_string x.expr)

let dump _ = ()

let mk_true ctx = mk ctx (B.mk_true ctx.ctx)

let mk_false ctx = mk ctx (B.mk_false ctx.ctx)

let mk_fresh_bool_var ctx =
  var_count := !var_count + 1;
  mk ctx (B.mk_const ctx.ctx (Symbol.mk_int ctx.ctx !var_count))
;;

let (!!) x =
  if is_true x then mk_false x.ctx else
  if is_false x then mk_true x.ctx else
  mk x.ctx (B.mk_not (z3ctx x) x.expr)
;;

let (<|>) x y =
  if is_true x || is_true y then mk_true x.ctx else
  if is_false x then y else if is_false y then x else
  mk x.ctx (B.mk_or (z3ctx x) [ x.expr; y.expr ])
;;

let (<&>) x y =
  if is_false x || is_false y then mk_false x.ctx else
  if is_true x then y else if is_true y then x else
  mk x.ctx (B.mk_and (z3ctx x) [ x.expr; y.expr ])
;;

let (<=>>) x y = !!x <|> y

let (<<=>>) x y = mk x.ctx (B.mk_eq (z3ctx x) x.expr y.expr )

let big_binop p_ann ann p_neut neut op ctx xs =
  if List.exists p_ann xs then ann ctx
  else match List.filter (fun x -> not (p_neut x)) xs with
      []  -> neut ctx
    | [x] -> x
    | xs  -> mk ctx (op ctx.ctx (List.map expr xs))
;;

let big_binop1 big_binop = function
  | [] -> failwith "Z3x.big_binop1: empty argument list"
  | x :: xs -> big_binop x.ctx (x :: xs)
;;

let big_and = big_binop is_false mk_false is_true mk_true B.mk_and

let big_and1 = big_binop1 big_and

let big_or = big_binop is_true mk_true is_false mk_false B.mk_or

let big_or1 = big_binop1 big_or

let ite c t f = mk c.ctx (B.mk_ite (z3ctx c) c.expr t.expr f.expr)

let (<=>) x y = mk x.ctx (B.mk_eq (z3ctx x) x.expr y.expr)

let (<!=>) x y = !! (x <=> y)

let apply (ctx : context) f args =
  let any = Sort.mk_uninterpreted_s ctx.ctx "any" in
  let argsorts = List.map (fun _ -> any) args in
  let decl = FuncDecl.mk_func_decl_s ctx.ctx f argsorts any in
  mk ctx (FuncDecl.apply decl [a.expr | a <- args])
;;

let simplify e = mk e.ctx (Expr.simplify e.expr None) 

module Int = struct
  let mk_var ctx name = mk ctx (I.mk_const_s ctx.ctx name)

  let mk_num ctx n = mk ctx (I.mk_numeral_i ctx.ctx n)
  
  let mk_zero ctx = mk_num ctx 0
  
  let mk_one ctx = mk_num ctx 1

  let (<+>) x y =
    if is_zero x then y else if is_zero y then x else
    mk x.ctx (Arithmetic.mk_add (z3ctx x) [ x.expr; y.expr ])
  ;;

  let sum = big_binop (fun _ -> false) mk_zero is_zero mk_zero Arith.mk_add

  let sum1 = big_binop1 sum

  let (<>>) x y = mk x.ctx (Arith.mk_gt (z3ctx x) x.expr y.expr)

  let (<>=>) x y = mk x.ctx (Arith.mk_ge (z3ctx x) x.expr y.expr)

  let max x y = ite (x <>> y) x y

  let get_big_int x e =
    try I.get_big_int e
    with _ -> (* optimization cost is real *)
      if Arith.is_real e &&
        to_int (I.get_big_int (Real.get_denominator e)) == 1 then
        I.get_big_int (Real.get_numerator e)
      else failwith ("Z3x.get_big_int: conversion error " ^ (Expr.to_string e))
  ;;

  let eval m x =
    match Model.eval m x.expr true with
    | Some e -> to_int (get_big_int x e)
    | _ -> failwith "Z3x.Int.eval failed"
  ;;
end

module BitVector = struct
  let mk_var ctx name bits =  mk ctx (BV.mk_const_s ctx.ctx name bits)

  let mk_num ctx n bits = mk ctx (BV.mk_numeral ctx.ctx n bits)

  let mk_add x y = mk x.ctx (BV.mk_add (z3ctx x) x.expr y.expr)

  let mk_sub x y = mk x.ctx (BV.mk_sub (z3ctx x) x.expr y.expr)

  let mk_neg x = mk x.ctx (BV.mk_neg (z3ctx x) x.expr)

  let mk_mul x y = mk x.ctx (BV.mk_mul (z3ctx x) x.expr y.expr)

  let mk_udiv x y = mk x.ctx (BV.mk_udiv (z3ctx x) x.expr y.expr)

  let mk_sdiv x y = mk x.ctx (BV.mk_sdiv (z3ctx x) x.expr y.expr)

  let mk_ugt x y = mk x.ctx (BV.mk_ugt (z3ctx x) x.expr y.expr)

  let mk_sgt x y = mk x.ctx (BV.mk_sgt (z3ctx x) x.expr y.expr)

  let mk_uge x y = mk x.ctx (BV.mk_uge (z3ctx x) x.expr y.expr)

  let mk_sge x y = mk x.ctx (BV.mk_sge (z3ctx x) x.expr y.expr)

  let mk_ult x y = mk x.ctx (BV.mk_ult (z3ctx x) x.expr y.expr)

  let mk_slt x y = mk x.ctx (BV.mk_slt (z3ctx x) x.expr y.expr)

  let mk_ule x y = mk x.ctx (BV.mk_ule (z3ctx x) x.expr y.expr)

  let mk_sle x y = mk x.ctx (BV.mk_sle (z3ctx x) x.expr y.expr)

  let mk_eq x y = mk x.ctx (B.mk_eq (z3ctx x) x.expr y.expr)

  let mk_neq x y = !! (mk_eq x y)

  let mk_and x y = mk x.ctx (BV.mk_and (z3ctx x) x.expr y.expr)

  let mk_or x y = mk x.ctx (BV.mk_or (z3ctx x) x.expr y.expr)

  let mk_xor x y = mk x.ctx (BV.mk_xor (z3ctx x) x.expr y.expr)

  let mk_not x = mk x.ctx (BV.mk_not (z3ctx x) x.expr)

  let mk_shl x y = mk x.ctx (BV.mk_shl (z3ctx x) x.expr y.expr)

  let mk_ashr x y = mk x.ctx (BV.mk_ashr (z3ctx x) x.expr y.expr)

  let mk_lshr x y = mk x.ctx (BV.mk_lshr (z3ctx x) x.expr y.expr)
  
  let eval m x =
    match Model.eval m x.expr true with
    | Some e -> Expr.to_string e
    | _ -> failwith "Z3x.BitVector.eval failed"
  ;;
end

(* assertions and stuff *)
let require x = Optimize.add (opt x) [x.expr]

let assert_weighted x n =
  let max = Symbol.mk_string (z3ctx x) "max" in
  ignore (Optimize.add_soft (opt x) x.expr (string_of_int n) max)
;;

let push ctx = Optimize.push ctx.opt

let pop ctx = Optimize.pop ctx.opt

let check ctx = Optimize.check ctx.opt == Solver.SATISFIABLE

let max_sat = check

let get_model ctx =
  match Optimize.get_model ctx.opt with
      Some m -> m
    | None -> failwith "Z3x.get_model: no model found"
;;

(* in evaluation, set set flag for model completion to true *)
let eval m x =
  match Model.eval m x.expr true with
    | Some e -> B.is_true e
    | _ -> failwith "Z3x.eval: failed"
;;

let get_cost ctx m =
  match Optimize.get_objectives ctx.opt with
  | obj :: _ -> Int.eval m (mk ctx obj)
  | _ -> failwith "Z3x.get_cost: no objective"
;;

