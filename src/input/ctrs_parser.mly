%{
module Sig = Signature
open Constrained.Expr

open Lexing
open Parsing

type preterm =
  | Node of string * preterm list
  | Bv of Constrained.Expr.bv

type attribute = Irregular | Non_standard

type input = {
  theory: string;
  logic: string;
  signature: string list;
  rules: ((preterm * preterm) * Constrained.Expr.boolean) list;
  attributes: attribute list;
  query: string
}

let empty = {
  theory = "";
  logic = "";
  signature = [];
  rules = [];
  attributes = [];
  query = ""
}

let convert_term fs cs =
  let rec convert cs = function
    | Node (x, []) when not (List.mem x fs) -> Term.V (Sig.var_called x), cs
    | Node (f, ts) ->
      let fold ti (us, cs) = let ui, cs' = convert cs ti in ui :: us, cs' in
      let us, cs' = List.fold_right fold ts ([], cs) in 
      Term.F (Sig.fun_called f, us), cs'
    | Bv e ->
      if List.mem_assoc e cs then Term.V (List.assoc e cs), cs
      else
        let z = "z" ^ (string_of_int (List.length cs)) in
        let v = Sig.fresh_var_called z in
        Term.V v, (e,v) :: cs
  in
  convert cs
;;

let convert_rule fs ((l, r), c) =
  let l', cs = convert_term fs [] l in
  let r', cs' = convert_term fs cs r in
  let add c (e, v) = And (c, Equal (Var(Sig.get_var_name v, bit_width e),e)) in
  let c' = List.fold_left add c cs' in
  (l', r'), c'
;;

let convert_rules d = List.map (convert_rule d.signature) d.rules

let syntax_error msg =
  let p = symbol_start_pos () in
  Format.eprintf "File %S at line %d, character %d:@.%s@." 
    p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol + 1) msg;
  exit 1
;;

let set_theory t d = {d with theory = t}

let set_logic l d = {d with logic = l}

let set_sig s d = {d with signature = s}

let set_rules rs d = {d with rules = rs}

let set_query q d = {d with query = q}

let add_attr a d = {d with attributes = a :: d.attributes}

%}

%token <string> IDENT
%token LPAREN RPAREN 
%token LBRACKET RBRACKET
%token ARROW COMMA SEMICOLON DOT QUOTE HASH
%token SIGNATURE RULES LOGIC SOLVER THEORY
%token OP_BV_OR
%token OP_BV_AND
%token OP_BV_XOR
%token OP_BV_ADD
%token OP_BV_SUB
%token OP_BV_MULT
%token OP_BV_DIV
%token OP_BV_ULT
%token OP_BV_UGT
%token OP_BV_ULE
%token OP_BV_UGE
%token OP_BV_SLT
%token OP_BV_SGT
%token OP_BV_SLE
%token OP_BV_SGE
%token OP_AND OP_OR OP_EQUAL
%token <string * int> CONST
%token <string * int> IDENT_BITS
%token NON_STANDARD IRREGULAR QUERY
%token OTHER EOF

%type <Constrained.Equality.t list> toplevel
%start toplevel

%%

toplevel:
  | decl EOF { convert_rules $1 }

decl:
  | THEORY IDENT SEMICOLON decl   { set_theory $2 $4 }
  | LOGIC IDENT SEMICOLON decl    { set_logic $2 $4 }
  | SOLVER IDENT SEMICOLON decl   { $4 }
  | SIGNATURE funs SEMICOLON decl { set_sig $2 $4 }
  | RULES rules decl              { set_rules $2 $3 }
  | QUERY IDENT decl              { set_query $2 $3 }
  | attribute decl                { add_attr $1 $2 }
  |                               { empty }

funs:
  | IDENT more_funs { $1 :: $2 }

more_funs:
  | COMMA funs { $2 }
  |            { [] }

attribute:
  | NON_STANDARD { Non_standard }
  | IRREGULAR    { Irregular }

rules:
  | rule SEMICOLON rules { $1 :: $3 }
  |                      { [] }

rule:
  | term ARROW term log_constraint { (($1, $3), $4) }
  | error                          { syntax_error "Syntax error." }

log_constraint:
  | LBRACKET bool_expr RBRACKET { $2 }
  |                             { Top }

bool_expr:
  | LPAREN bool_expr RPAREN {$2}
  | bool_expr OP_AND bool_expr { And($1, $3) }
  | bool_expr OP_OR bool_expr { Or($1, $3) }
  | bv_expr OP_EQUAL bv_expr { Equal($1, $3) }
  | bv_expr OP_BV_ULE bv_expr { Bv_ule($1, $3) }
  | bv_expr OP_BV_ULT bv_expr { Bv_ult($1, $3) }
  | bv_expr OP_BV_UGE bv_expr { Bv_uge($1, $3) }
  | bv_expr OP_BV_UGT bv_expr { Bv_ugt($1, $3) }
  | bv_expr OP_BV_SLE bv_expr { Bv_sle($1, $3) }
  | bv_expr OP_BV_SLT bv_expr { Bv_slt($1, $3) }
  | bv_expr OP_BV_SGE bv_expr { Bv_sge($1, $3) }
  | bv_expr OP_BV_SGT bv_expr { Bv_sgt($1, $3) }
  | IDENT LPAREN bv_exprs RPAREN {Pred($1, $3)}

bv_expr:
  | LPAREN bv_expr RPAREN {$2}
  | bv_expr OP_BV_AND bv_expr { Bv_and($1, $3) }
  | bv_expr OP_BV_OR bv_expr { Bv_or($1, $3) }
  | bv_expr OP_BV_XOR bv_expr { Bv_xor($1, $3) }
  | bv_expr OP_BV_ADD bv_expr { Bv_add($1, $3) }
  | bv_expr OP_BV_SUB bv_expr { Bv_sub($1, $3) }
  | CONST { HexConst (fst $1, snd $1) }
  | IDENT_BITS LPAREN bv_exprs RPAREN {Fun(fst $1, snd $1, $3)}
  | IDENT_BITS { Var(fst $1, snd $1) }

bv_exprs:
  | bv_expr more_bv_exprs {$1 :: $2}

more_bv_exprs:
  | COMMA bv_exprs { $2 }
  |                { [] }

term:
  | IDENT args { Node ($1, $2) }
  | bv_expr    { Bv $1 }

args:
  | LPAREN terms RPAREN { $2 }
  |                     { [] }

terms:
  | term more_terms {$1 :: $2}

more_terms:
  | COMMA terms { $2 }
  |             { [] }
