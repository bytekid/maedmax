%{
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

let add_axioms a (axs,es,ieqs,gs) =  a::axs, es, ieqs, gs;;
let add_equation (e,is_eq) (axs,es,ieqs,gs) =
  if is_eq then axs, e::es, ieqs, gs else axs, es, e::ieqs, gs;;
let add_goal g (axs,es,ieqs,gs) = axs, es, ieqs, g::gs;;

%}

%token <string> IDENT
%token <string> VAR
%token <string> FILE
%token LPAREN RPAREN 
%token EQ NEQ COMMA SEMICOLON EOF TICK DOT COMMENT
%token CNF AXIOM HYPOTHESIS CONJECTURE NCONJECTURE INCLUDEAXIOMS

%type <string list * Rules.t * Rules.t * Rules.t> toplevel
%start toplevel

%%

toplevel:
  | decl EOF { $1 } 

decl:
  | INCLUDEAXIOMS LPAREN FILE RPAREN DOT decl { add_axioms $3 $6}
  | axiom decl { add_equation $1 $2 }
  | hypothesis decl { add_equation $1 $2 }
  | conjecture decl { add_goal (fst $1) $2 }
  | COMMENT decl { $2 }
  | { [],[],[],[] }
  | error { syntax_error "Syntax error." }

axiom:
 | CNF LPAREN IDENT COMMA AXIOM COMMA LPAREN equation RPAREN RPAREN DOT { $8 }
 | CNF LPAREN IDENT COMMA AXIOM COMMA LPAREN inequality RPAREN RPAREN DOT { $8 }

hypothesis:
 | CNF LPAREN IDENT COMMA HYPOTHESIS COMMA LPAREN equation RPAREN RPAREN DOT { $8 }

conjecture:
 | CNF LPAREN IDENT COMMA conjecturetype COMMA LPAREN equation RPAREN RPAREN DOT { $8 }
 | CNF LPAREN IDENT COMMA conjecturetype COMMA LPAREN inequality RPAREN RPAREN DOT { $8 }

conjecturetype:
 | CONJECTURE { () }
 | NCONJECTURE { () }

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
