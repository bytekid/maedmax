(*** OPENS *******************************************************************)
open Yices

(*** TYPES *******************************************************************)
type context = Yices.context

type t = {
  ctx : Yices.context;
  expr: Yices.expr;
  decl: Yices.var_decl option
}

type model = Yices.model

(*** FUNCTIONS ***************************************************************)
let mk c e = { ctx = c; expr = e; decl = None }
let mk_with_decl c e d = { ctx = c; expr = e; decl = Some d }

let ctx yexpr = yexpr.ctx

let expr yexpr = yexpr.expr

let is_true x = let r = (x.expr == mk_true x.ctx) in r

let is_false x = (x.expr == mk_false x.ctx)

let is_zero x = (x.expr == mk_num x.ctx 0)

let mk_context = mk_context

let del_context = del_context

let reset ctx = reset ctx; ctx

let show x = pp_expr x.expr

let dump ctx = display_model (get_model ctx); dump_context ctx

let mk_true ctx = mk ctx (mk_true ctx)

let mk_false ctx = mk ctx (mk_false ctx)

let mk_fresh_bool_var ctx = mk ctx (mk_fresh_bool_var ctx)

let (!!) x =
  if is_true x then mk_false x.ctx else
  if is_false x then mk_true x.ctx else
  mk x.ctx (mk_not x.ctx x.expr)
;;

let (<|>) x y =
  if is_true x || is_true y then mk_true x.ctx else
  if is_false x then y else if is_false y then x else
  mk x.ctx (mk_or x.ctx [| x.expr; y.expr |])
;;

let (<&>) x y =
  if is_false x || is_false y then mk_false x.ctx else
  if is_true x then y else if is_true y then x else
  mk x.ctx (mk_and x.ctx [| x.expr; y.expr |])
;;

let (<=>>) x y = !!x <|> y

let (<<=>>) x y = (x <=>> y) <&> (y <=>> x)

let big_binop p_ann ann p_neut neut op ctx xs =
  if List.exists p_ann xs then ann ctx
  else match List.filter (fun x -> not (p_neut x)) xs with
      []  -> neut ctx
    | [x] -> x
    | xs  -> mk ctx (op ctx (Array.of_list (List.map expr xs)))
;;

let big_binop1 big_binop = function
  | [] -> failwith "Yicesx.big_binop1: empty argument list"
  | x :: xs -> big_binop x.ctx (x :: xs)
;;

let big_and = big_binop is_false mk_false is_true mk_true mk_and

let big_and1 = big_binop1 big_and

let big_or = big_binop is_true mk_true is_false mk_false mk_or

let big_or1 = big_binop1 big_or

let apply ctx name args =
  let a = mk_type ctx "any" in
  let k = List.length args in
  let ty = if args = [] then a else mk_function_type ctx (Array.make k a) a in
  let d =
    try get_var_decl_from_name ctx name
    with _ -> mk_var_decl ctx name ty
  in
  let f = mk_var_from_decl ctx d in
  if args = [] then mk_with_decl ctx f d
  else mk ctx (mk_app ctx f (Array.of_list [a.expr | a <- args]))
;;

let (<=>) x y = mk x.ctx (mk_eq x.ctx x.expr y.expr)

let (<!=>) x y = mk x.ctx (mk_diseq x.ctx x.expr y.expr)

let ite c t f = mk c.ctx (mk_ite c.ctx c.expr t.expr f.expr)

let simplify e = e

module Int = struct
  let mk_num ctx n = mk ctx (mk_num ctx n)
  
  let mk_zero ctx = mk_num ctx 0
  
  let mk_one ctx = mk_num ctx 1

  let mk_var ctx name =
    let ty  = mk_type ctx int_type_name in
    let d = mk_var_decl ctx name ty in
    mk_with_decl ctx (mk_var_from_decl ctx d) d
  ;;

  let (<>>) x y = mk x.ctx (mk_gt x.ctx x.expr y.expr)
  
  let (<>=>) x y = mk x.ctx (mk_ge x.ctx x.expr y.expr)

  let (<+>) x y =
    if is_zero x then y else if is_zero y then x else
    mk x.ctx (mk_sum x.ctx [| x.expr; y.expr |])
  ;;
  
  let sum = big_binop (fun _ -> false) mk_zero is_zero mk_zero mk_sum
  
  let sum1 = big_binop1 sum

  let max x y = ite (x <>> y) x y

  let eval m x =
    match x.decl with
        Some d -> Int32.to_int (get_int_value m d)
      | None -> failwith "Yicesx.Int.eval no declaration found"
  ;;
end


module BitVector = struct
  let mk_var ctx name bits =
    let ty  = mk_bitvector_type ctx bits in
    let d = mk_var_decl ctx name ty in
    mk_with_decl ctx (mk_var_from_decl ctx d) d
  ;;

  let mk_num ctx s bits =
    let n = Prelude.hex2dec s in
    mk ctx (mk_bv_constant ctx bits (Int32.of_int n))
  ;;

  let mk_add x y = mk x.ctx (mk_bv_add x.ctx x.expr y.expr)

  let mk_sub x y = mk x.ctx (mk_bv_sub x.ctx x.expr y.expr)

  let mk_neg x = mk x.ctx (mk_bv_minus x.ctx x.expr)

  let mk_mul x y = mk x.ctx (mk_bv_mul x.ctx x.expr y.expr)

  let mk_udiv x y = failwith "Yicesx.BitVector.mk_udiv"

  let mk_sdiv x y = failwith "Yicesx.BitVector.mk_sdiv"

  let mk_ugt x y = mk x.ctx (mk_bv_gt x.ctx x.expr y.expr)

  let mk_sgt x y = mk x.ctx (mk_bv_sgt x.ctx x.expr y.expr)

  let mk_uge x y = mk x.ctx (mk_bv_ge x.ctx x.expr y.expr)

  let mk_sge x y = mk x.ctx (mk_bv_sge x.ctx x.expr y.expr)

  let mk_ult x y = mk x.ctx (mk_bv_lt x.ctx x.expr y.expr)

  let mk_slt x y = mk x.ctx (mk_bv_slt x.ctx x.expr y.expr)

  let mk_ule x y = mk x.ctx (mk_bv_le x.ctx x.expr y.expr)

  let mk_sle x y = mk x.ctx (mk_bv_sle x.ctx x.expr y.expr)

  let mk_eq x y = x <=> y

  let mk_neq x y = !! (mk_eq x y)

  let mk_and x y = mk x.ctx (mk_bv_and x.ctx x.expr y.expr)

  let mk_or x y = mk x.ctx (mk_bv_or x.ctx x.expr y.expr)

  let mk_xor x y = mk x.ctx (mk_bv_xor x.ctx x.expr y.expr)

  let mk_not x = mk x.ctx (mk_bv_not x.ctx x.expr)

  let mk_shl _ _ = failwith ("Yicesx.mk_shl not implemented")

  let mk_ashr _ _ = failwith ("Yicesx.mk_ashr not implemented")

  let mk_lshr _ _ = failwith ("Yicesx.mk_lshr not implemented")

  let eval m x =
    match x.decl with
      | Some d ->
        let barr = get_bitvector_value m d 64 in
        Array.fold_left (fun s b -> s ^ (if b then "1" else "0")) "" barr
      | None -> failwith "Yicesx.eval_int: no declaration found"
  ;;
end

(* assertions and stuff *)
let require x = assert_simple x.ctx x.expr

let assert_weighted x n =
  ignore (assert_weighted x.ctx x.expr (Int64.of_int n))

let push = push

let pop = pop

let check ctx = check ctx = True

let max_sat ctx = max_sat ctx = True

let get_model = get_model

let eval m x =
 try
   let value = evaluate_in_model m x.expr in
   value = True
 with _ -> failwith "Yicesx.evaluate_in_model: variable unknown"
;;

let get_cost _ m = Int64.to_int (get_cost m)

