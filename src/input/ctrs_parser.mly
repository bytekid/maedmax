%{
open Lexing
open Parsing
open Term

type preterm =
  | Node of string * preterm list

type attribute = Irregular | Non_standard

type input = {
  theory: string;
  logic: string;
  signature: string list;
  rules: (preterm * preterm) list;
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

(* variables, rules, theories, conditions *)
let add xs rs ts (xs', rs', ts', cs) =
  (xs @ xs', rs @ rs', ts @ ts', cs)
;;

let add_conditions cs (xs', rs', ts', cs') = (xs', rs', ts', cs @ cs')

let rec convert_term fs = function
  | Node (x, []) when not (List.mem x fs) -> V (Signature.var_called x)
  | Node (f, ts) -> F (Signature.fun_called f, List.map (convert_term fs) ts)
;;

let convert_rule fs (l, r) =
  Literal.make_axiom (convert_term fs l, convert_term fs r)
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
%token OP_BIT_OR OP_BIT_AND OP_BIT_XOR
%token OP_PLUS OP_MINUS OP_MULT OP_DIV
%token OP_EQUAL OP_LT OP_GT OP_LE OP_GE
%token OP_AND OP_OR
%token NON_STANDARD IRREGULAR QUERY
%token OTHER EOF

%type <Literal.t list> toplevel
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
  | error { syntax_error "Syntax error." }

funs:
  | IDENT more_funs { $1 :: $2 }

more_funs:
  | COMMA funs { $2 }
  |            {[]}

attribute:
  | NON_STANDARD { Non_standard }
  | IRREGULAR    { Irregular }

rules:
  | rule SEMICOLON rules { $1 :: $3 }
  |                      { [] }

rule:
  | term ARROW term rule_condition { ($1, $3) }
  | error                          { syntax_error "Syntax error." }

rule_condition:
  | {}

term:
  | IDENT LPAREN terms RPAREN { Node ($1, $3) }
  | IDENT                     { Node ($1, []) }
  | error { syntax_error "Syntax error." }

terms:
  | term COMMA terms { $1 :: $3 }
  | term             { [$1] }
  |                  { [] }
