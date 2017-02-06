%{
open Lexing
open Parsing
open Term

let add xs rs ts (xs', rs', ts') = (xs @ xs', rs @ rs', ts @ ts')

let var x = V (Signature.var_called x)

let func x xs = F (Signature.fun_called x, xs)

(*
let rec convert_term xs = function
  | VV x -> V (Signature.var_called x)
  | FF (x, []) when List.mem x xs -> V (Signature.var_called x)
  | FF (f, ts) -> F (Signature.fun_called f, List.map (convert_term xs) ts)

let convert_rule xs (l, r) = (convert_term xs l, convert_term xs r)

let convert_rules (xs, rs, th) = List.map (convert_rule xs) rs, th
*)
let syntax_error msg =
  let p = symbol_start_pos () in
  Format.eprintf "File %S at line %d, character %d:@.%s@." 
    p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol + 1) msg;
  exit 1

let add_axioms a (axs,es,gs) =  a::axs, es, gs;;
let add_equation e (axs,es,gs) = axs, e::es, gs;;
let add_goal g (axs,es,gs) = axs, es, g::gs;;

%}

%token <string> IDENT
%token <string> VAR
%token <string> FILE
%token LPAREN RPAREN 
%token EQ NEQ COMMA SEMICOLON EOF TICK DOT COMMENT
%token CNF AXIOM HYPOTHESIS CONJECTURE NCONJECTURE INCLUDEAXIOMS

%type <string list * Rules.t * Rules.t> toplevel
%start toplevel

%%

toplevel:
  | decl EOF { $1 } 

decl:
  | INCLUDEAXIOMS LPAREN FILE RPAREN DOT decl { add_axioms $3 $6}
  | axiom decl { add_equation $1 $2 }
  | hypothesis decl { add_equation $1 $2 }
  | conjecture decl { add_goal $1 $2 }
  | COMMENT decl { $2 }
  | { [],[],[] }
  | error { syntax_error "Syntax error." }

axiom:
 | CNF LPAREN IDENT COMMA AXIOM COMMA LPAREN equation RPAREN RPAREN DOT { $8 }

hypothesis:
 | CNF LPAREN IDENT COMMA HYPOTHESIS COMMA LPAREN equation RPAREN RPAREN DOT { $8 }

conjecture:
 | CNF LPAREN IDENT COMMA conjecturetype COMMA LPAREN equation RPAREN RPAREN DOT { $8 }
 | CNF LPAREN IDENT COMMA conjecturetype COMMA LPAREN inequality RPAREN RPAREN DOT { $8 }

conjecturetype:
 | CONJECTURE { () }
 | NCONJECTURE { () }

equation:
  | term EQ term { ($1, $3) }
  | error      { syntax_error "Syntax error: not an equation" }

inequality:
  | term NEQ term { ($1, $3) }
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
