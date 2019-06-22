(*** MODULES ******************************************************************)
module L = Order.Logic
module F = Format
module BV = L.BitVector 

module Expr = struct
  open L

  type bv =
    | Var of string * int
    | HexConst of string * int (* value, bitwidth *)
    | Bv_not of bv
    | Bv_and of bv * bv
    | Bv_or of bv * bv
    | Bv_xor of bv * bv
    | Bv_neg of bv
    | Bv_add of bv * bv
    | Bv_sub of bv * bv
    | Bv_mult of bv * bv
    | Bv_udiv of bv * bv
    | Bv_sdiv of bv * bv
    | Bv_shl of bv * bv
    | Bv_ashr of bv * bv
    | Bv_lshr of bv * bv
    | Fun of string * int * bv list

  type boolean =
    | Top
    | Bot 
    | And of boolean * boolean
    | Or of boolean * boolean
    | Not of boolean
    | Equal of bv * bv
    | Bv_ult of bv * bv
    | Bv_ugt of bv * bv
    | Bv_ule of bv * bv
    | Bv_uge of bv * bv
    | Bv_slt of bv * bv
    | Bv_sgt of bv * bv
    | Bv_sle of bv * bv
    | Bv_sge of bv * bv
    | Pred of string * bv list

  let rec print_bv ppf = function
    | Var (v, bits) -> F.fprintf ppf "%s.%d" v bits
    | HexConst(c, bits) -> F.fprintf ppf "%s.%d" c bits
    | Bv_and(a, b) -> F.fprintf ppf "(%a & %a)" print_bv a print_bv b 
    | Bv_or(a, b) -> F.fprintf ppf "(%a | %a)" print_bv a print_bv b 
    | Bv_xor(a, b) -> F.fprintf ppf "(%a ^ %a)" print_bv a print_bv b 
    | Bv_not(a) -> F.fprintf ppf "! %a" print_bv a
    | Bv_neg(a) -> F.fprintf ppf "~ %a" print_bv a
    | Bv_add(a, b) -> F.fprintf ppf "(%a + %a)" print_bv a print_bv b  
    | Bv_sub(a, b) -> F.fprintf ppf "(%a - %a)" print_bv a print_bv b 
    | Bv_mult(a, b) -> F.fprintf ppf "(%a * %a)" print_bv a print_bv b 
    | Bv_udiv(a, b) -> F.fprintf ppf "(%a /u %a)" print_bv a print_bv b 
    | Bv_sdiv(a, b) -> F.fprintf ppf "(%a /s %a)" print_bv a print_bv b 
    | Bv_shl(a, b) -> F.fprintf ppf "(%a << %a)" print_bv a print_bv b 
    | Bv_ashr(a, b) -> F.fprintf ppf "(%a >>s %a)" print_bv a print_bv b 
    | Bv_lshr(a, b) -> F.fprintf ppf "(%a >>u %a)" print_bv a print_bv b 
    | Fun(n, b,es) ->
      F.fprintf ppf "%s.%d(%a)" n b (Formatx.print_list print_bv ",") es
  ;;

  let rec print ppf = function
    | Top -> F.fprintf ppf "T"
    | Bot -> F.fprintf ppf "F"
    | And(a, b) -> F.fprintf ppf "(%a /\\ %a)" print a print b 
    | Or(a, b) -> F.fprintf ppf "(%a \\/ %a)" print a print b 
    | Not(a) -> F.fprintf ppf "! %a" print a
    | Equal(a, b) -> F.fprintf ppf "(%a = %a)" print_bv a print_bv b 
    | Bv_ule(a, b) -> F.fprintf ppf "(%a <=u %a)" print_bv a print_bv b 
    | Bv_ult(a, b) -> F.fprintf ppf "(%a <u %a)" print_bv a print_bv b 
    | Bv_uge(a, b) -> F.fprintf ppf "(%a >=u %a)" print_bv a print_bv b 
    | Bv_ugt(a, b) -> F.fprintf ppf "(%a >u %a)" print_bv a print_bv b 
    | Bv_sle(a, b) -> F.fprintf ppf "(%a <=s %a)" print_bv a print_bv b 
    | Bv_slt(a, b) -> F.fprintf ppf "(%a <s %a)" print_bv a print_bv b 
    | Bv_sge(a, b) -> F.fprintf ppf "(%a >=s %a)" print_bv a print_bv b 
    | Bv_sgt(a, b) -> F.fprintf ppf "(%a >s %a)" print_bv a print_bv b 
    | Pred(n, es) ->
      F.fprintf ppf "%s(%a)" n (Formatx.print_list print_bv ",") es
  ;;

  let bit_width =
    let rec bw e =
      let bin a b = let i =bw a in if i = bw b then i else failwith "Expr.bw" in
      match e with
      | Var(_, i) -> i
      | HexConst(_, i) -> i
      | Bv_not e
      | Bv_neg e -> bw e
      | Bv_and(a, b)
      | Bv_or(a, b)
      | Bv_xor(a, b)
      | Bv_add(a, b)
      | Bv_sub(a, b)
      | Bv_mult(a, b)
      | Bv_udiv(a, b)
      | Bv_sdiv(a, b)
      | Bv_shl(a, b)
      | Bv_ashr(a, b)
      | Bv_lshr(a, b) -> bin a b
      | Fun(_, i, _) -> i
    in bw
  ;;

  let expand_pred n es = 
    match n, es with
    | "isPowerOf2", [x] ->
      let b = bit_width x in
      let a = Equal (Bv_and (x, Bv_sub(x, HexConst("1",b))), HexConst("0",b)) in
      And(a, Not(Equal(x, HexConst("0",b))))
    | "isPowerOf2OrZero", [x] ->
      let b = bit_width x in
      Equal (Bv_and (x, Bv_sub(x, HexConst("1",b))), HexConst("0",b))
      | _ -> failwith ("Expr.expand_pred: unknown predicate" ^ n)
  ;;

  let expand_fun n bits es = 
    match n, es with
    | "computeKnownZeroBits", [x] -> x
    | "neg", [x] -> Bv_neg x
    | _ -> failwith ("Expr.expand_fun: unknown function " ^ n)
  ;;

  let to_logic ctx e =
    let rec of_bexpr ctx = function
      | Top -> L.mk_true ctx 
      | Bot -> L.mk_false ctx 
      | And(a, b) -> (of_bexpr ctx a) <&> (of_bexpr ctx b)
      | Or(a, b) -> (of_bexpr ctx a) <|> (of_bexpr ctx b)
      | Not(a) -> !! (of_bexpr ctx a)
      | Equal(a, b) -> (of_bvexpr ctx a) <=> (of_bvexpr ctx b) 
      | Bv_ule(a, b) -> BV.mk_ule (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_ult(a, b) -> BV.mk_ult (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_uge(a, b) -> BV.mk_uge (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_ugt(a, b) -> BV.mk_ugt (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_sle(a, b) -> BV.mk_sle (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_slt(a, b) -> BV.mk_slt (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_sge(a, b) -> BV.mk_sge (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_sgt(a, b) -> BV.mk_sgt (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Pred(n, es) -> of_bexpr ctx (expand_pred n es)
    and of_bvexpr ctx = function
      | Var(v, bits) -> BV.mk_var ctx v bits
      | HexConst(c, bits) -> BV.mk_num ctx (Prelude.hex2bin c) bits
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
      | Fun(n, b, es) -> of_bvexpr ctx (expand_fun n b es)
    in
    (*Format.printf "2logic %a\n%!" print e;*)
    let r = of_bexpr ctx e in
    (*L.show r;*)
    r
  ;; 
end

module Equality = struct
  type t = Rule.t * Expr.boolean

  let print_with sep ppf ((l, r), c) =
    F.fprintf ppf "%a %s %a [%a]" Term.print l sep Term.print r Expr.print c
  ;;

  let print = print_with "="
end

module Literal = struct

  open Equality

  type t = {
    terms: Rule.t;
    constr: Expr.boolean;
    log_constr: L.t
 }

  let of_equation ctx (rl, e) =
    { terms = rl; constr = e; log_constr = Expr.to_logic ctx e}
  ;;

  let constr l = l.constr

  let log_constr l = l.log_constr

  let terms l = l.terms

  let print f l = Equality.print f (l.terms, l.constr)

  let flip l = {l with terms = Rule.flip l.terms}

  let overlaps_on_below_root l l' = []

  let overlaps_on l l' = []
end

module Literals = struct
  type t = Literal.t list

  let symmetric ls = [ Literal.flip l | l <- ls] @ ls
end