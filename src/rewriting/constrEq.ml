
type bv_expr =
  | Var of string
  | Const of string * int (* value, bitwidth *)
  | Bv_not of bv_expr
  | Bv_and of bv_expr * bv_expr
  | Bv_or of bv_expr * bv_expr
  | Bv_xor of bv_expr * bv_expr
  | Bv_neg of bv_expr
  | Bv_add of bv_expr * bv_expr
  | Bv_sub of bv_expr * bv_expr
  | Bv_mult of bv_expr * bv_expr
  | Bv_div of bv_expr * bv_expr
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
  | Lt of bv_expr * bv_expr
  | Gt of bv_expr * bv_expr
  | Le of bv_expr * bv_expr
  | Ge of bv_expr * bv_expr
  | Pred of string * int * bv_expr list

type t = Rule.t * bool_expr

let fprintf = Format.fprintf

let rec print_bv ppf = function
  | Var v -> fprintf ppf "%s" v
  | Const(c, bits) -> fprintf ppf "%s.%d" c bits
  | Bv_and(a, b) -> fprintf ppf "(%a & %a)" print_bv a print_bv b 
  | Bv_or(a, b) -> fprintf ppf "(%a | %a)" print_bv a print_bv b 
  | Bv_xor(a, b) -> fprintf ppf "(%a ^ %a)" print_bv a print_bv b 
  | Bv_not(a) -> fprintf ppf "! %a" print_bv a
  | Bv_neg(a) -> fprintf ppf "~ %a" print_bv a
  | Bv_add(a, b) -> fprintf ppf "(%a + %a)" print_bv a print_bv b  
  | Bv_sub(a, b) -> fprintf ppf "(%a - %a)" print_bv a print_bv b 
  | Bv_mult(a, b) -> fprintf ppf "(%a * %a)" print_bv a print_bv b 
  | Bv_div(a, b) -> fprintf ppf "(%a / %a)" print_bv a print_bv b 
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
  | Le(a, b) -> fprintf ppf "(%a <= %a)" print_bv a print_bv b 
  | Lt(a, b) -> fprintf ppf "(%a < %a)" print_bv a print_bv b 
  | Ge(a, b) -> fprintf ppf "(%a >= %a)" print_bv a print_bv b 
  | Gt(a, b) -> fprintf ppf "(%a > %a)" print_bv a print_bv b 
  | Pred(n, b,es) ->
    fprintf ppf "%s.%d(%a)" n b (Formatx.print_list print_bv ",") es
;;

let print_with sep ppf ((l, r), c) =
  fprintf ppf "%a %s %a [%a]" Term.print l sep Term.print r print_b c
;;

let print = print_with "="
