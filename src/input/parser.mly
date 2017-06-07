%{
open Lexing
open Parsing
open Term

type tt =
  | VV of string
  | FF of string * tt list

let add xs rs ts (xs', rs', ts') = (xs @ xs', rs @ rs', ts @ ts')

let rec convert_term xs = function
  | VV x -> V (Signature.var_called x)
  | FF (x, []) when List.mem x xs -> V (Signature.var_called x)
  | FF (f, ts) -> F (Signature.fun_called f, List.map (convert_term xs) ts)

let convert_rule xs (l, r) =
 Literal.make_axiom (convert_term xs l, convert_term xs r)

let convert_rules (xs, rs, th) = List.map (convert_rule xs) rs, th

let syntax_error msg =
  let p = symbol_start_pos () in
  Format.eprintf "File %S at line %d, character %d:@.%s@." 
    p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol + 1) msg;
  exit 1

%}

%token <string> IDENT
%token LPAREN RPAREN 
%token ARROW ARROWEQ COMMA SEMICOLON EOF 
%token VAR RULES OTHER STRATEGY THEORY
%token AC
%token INNERMOST CONTEXTSENSITIVE

%type <Literal.literal list * string list> toplevel
%start toplevel

%%

toplevel:
  | decl EOF { convert_rules $1 }

decl:
  | LPAREN VAR      vars      RPAREN decl { add $3 [] [] $5 }
  | LPAREN RULES    rules     RPAREN decl { add [] $3 [] $5 }
  | LPAREN STRATEGY INNERMOST RPAREN decl { $5 }
  | LPAREN THEORY   theory    RPAREN decl { add [] [] $3 $5 }
  | LPAREN IDENT    anylist   RPAREN decl { $5 }
  |                                       { ([], [], []) }
  | error { syntax_error "Syntax error." }

anylist:
  | any anylist { () }
  |             { () }

any:
  | LPAREN anylist RPAREN { () }
  | IDENT { () } 
  | ARROW { () }
  | COMMA { () }
  | OTHER { () }

vars:
  | IDENT vars { $1 :: $2 }
  |            { [] }

theory:
  | LPAREN AC IDENT RPAREN theory { $3 :: $5 }
  |            { [] }

idents:
  | IDENT idents { $1 :: $2 }
  |            { [] }

rules:
  | rule rules { $1 :: $2 }
  | { [] }

rule:
  | term ARROW term { ($1, $3) }
  | error      { syntax_error "Syntax error." }

term:
  | IDENT LPAREN terms RPAREN { FF ($1, $3) }
  | IDENT                     { FF ($1, []) }
  | error { syntax_error "Syntax error." }

terms:
  | term COMMA terms { $1 :: $3 }
  | term             { [$1] }
  |                  { [] }
