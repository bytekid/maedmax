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
  failwith "Syntax error"
;;

let make_literal (e, eq) = if eq then L.make_axiom e else L.make_neg_axiom e

let make_clause = List.map make_literal

let add_axioms a (axs, cs, gs) =  a :: axs, cs, gs

let add_clause c (axs, cs, gs) = axs, make_clause c :: cs, gs

let add_goal_clause g (axs, cs, gs) = axs, cs, make_clause g :: gs

%}

%token <string> IDENT
%token <string> VAR
%token <string> FILE
%token LPAREN RPAREN LBRACKET RBRACKET
%token EQ NEQ COMMA SEMICOLON EOF TICK DOT OR COMMENT
%token CNF AXIOM HYPOTHESIS CONJECTURE NCONJECTURE INCLUDEAXIOMS
%token FILE_KEY STATUS_KEY INFERENCE_KEY PLAIN

%type <string list * Literal.t list list * Literal.t list list> toplevel
%type <Literal.t> equation_or_inequality
%start toplevel
%start equation_or_inequality

%%

toplevel:
  | decl EOF { $1 } 

decl:
  | INCLUDEAXIOMS LPAREN FILE RPAREN DOT decl { add_axioms $3 $6}
  | axiom decl      { add_clause $1 $2 }
  | hypothesis decl { add_clause $1 $2 }
  | conjecture decl { add_goal_clause $1 $2 }
  | COMMENT decl    { $2 }
  |                 { [],[],[]}
  | error           { syntax_error "Syntax error." }

axiom:
 | CNF LPAREN IDENT COMMA axiom_type COMMA LPAREN clause RPAREN source { $8 }

axiom_type:
 | AXIOM {}
 | PLAIN {}

hypothesis:
 | CNF LPAREN IDENT COMMA HYPOTHESIS COMMA LPAREN clause RPAREN source { $8 }

conjecture:
 | CNF LPAREN IDENT COMMA conj_type COMMA LPAREN clause RPAREN source { $8 }

conj_type:
 | CONJECTURE  {}
 | NCONJECTURE {}

source:
 | RPAREN DOT { }
 | COMMA inference RPAREN DOT { }
 | COMMA FILE_KEY LPAREN FILE COMMA IDENT RPAREN RPAREN DOT { }
 | COMMA FILE_KEY LPAREN FILE RPAREN RPAREN DOT { }

clause:
 | equation literals   { $1 :: $2 }
 | inequality literals { $1 :: $2 }

literals:
  | OR equation literals   { $2 :: $3 }
  | OR inequality literals { $2 :: $3 }
  |                        { [] }

equation_or_inequality:
 | equation EOF { make_literal $1 }
 | inequality EOF { make_literal $1 }

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

inference:
  | INFERENCE_KEY LPAREN IDENT COMMA inference_status COMMA
    LBRACKET inference inferences RPAREN {}
  | IDENT {}

inferences:
  | COMMA inference inferences {}
  | RBRACKET {}

inference_status:
  | LBRACKET STATUS_KEY LPAREN IDENT RPAREN RBRACKET {}