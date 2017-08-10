%{
module L = Literal

open Lexing
open Parsing
open Term

let var x = V (Signature.var_called x)

let func x xs = F (Signature.fun_called x, xs)

let syntax_error msg =
  let p = symbol_start_pos () in
  Format.eprintf "File %S at line %d, character %d:@.%s@." 
    p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol + 1) msg;
  exit 1

let add_axioms a (axs,ls,gs) =  a::axs, ls, gs;;
let add_equation (e,is_eq) (axs,ls,gs) =
  let l = if is_eq then L.make_axiom e else L.make_neg_axiom e in 
  axs, l::ls, gs;;
let add_goal g (axs,es,gs) = axs, es, L.make_neg_goal g::gs;;

%}

%token <string> IDENT
%token <string> VAR
%token <string> FILE
%token LPAREN RPAREN 
%token EQ NEQ COMMA SEMICOLON EOF TICK DOT COMMENT
%token CNF AXIOM HYPOTHESIS CONJECTURE NCONJECTURE INCLUDEAXIOMS

%type <string list * Literal.t list * Literal.t list> toplevel
%start toplevel

%%

toplevel:
  | decl EOF { $1 } 

decl:
  | INCLUDEAXIOMS LPAREN FILE RPAREN DOT decl { add_axioms $3 $6}
  | axiom decl { add_equation $1 $2 }
  | hypothesis decl { add_equation $1 $2 }
  | eq_conjecture decl { add_equation $1 $2 }
  | ineq_conjecture decl { add_goal (fst $1) $2 }
  | COMMENT decl { $2 }
  | { [],[],[]}
  | error { syntax_error "Syntax error." }

axiom:
 | CNF LPAREN IDENT COMMA AXIOM COMMA LPAREN equation RPAREN RPAREN DOT { $8 }
 | CNF LPAREN IDENT COMMA AXIOM COMMA LPAREN inequality RPAREN RPAREN DOT { $8 }

hypothesis:
 | CNF LPAREN IDENT COMMA HYPOTHESIS COMMA LPAREN equation RPAREN RPAREN DOT { $8 }

ineq_conjecture:
 | CNF LPAREN IDENT COMMA CONJECTURE COMMA LPAREN equation RPAREN RPAREN DOT { $8 }
 | CNF LPAREN IDENT COMMA NCONJECTURE COMMA LPAREN inequality RPAREN RPAREN DOT { $8 }

eq_conjecture:
 | CNF LPAREN IDENT COMMA NCONJECTURE COMMA LPAREN equation RPAREN RPAREN DOT { $8 }

equation:
  | term EQ term { ($1, $3), true }
  | error      { syntax_error "Syntax error: not an equation" }

inequality:
  | term NEQ term { ($1, $3), false }
  | error      { syntax_error "Syntax error: not an inequality" }

term:
  | IDENT LPAREN terms RPAREN { func $1 $3 }
  | IDENT                     { func $1 [] }
  | VAR                       { var $1 }
  | error { syntax_error "Syntax error: not a term" }

terms:
  | term COMMA terms { $1 :: $3 }
  | term             { [$1] }
  |                  { [] }
