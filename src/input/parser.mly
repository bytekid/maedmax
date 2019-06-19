%{
open Lexing
open Parsing
open Term

type tt =
  | VV of string
  | FF of string * tt list

(* variables, rules, theories, conditions *)
let add xs rs ts (xs', rs', ts', cs) =
  (xs @ xs', rs @ rs', ts @ ts', cs)
;;

let add_conditions cs (xs', rs', ts', cs') = (xs', rs', ts', cs @ cs')

let rec convert_term xs = function
  | VV x -> V (Signature.var_called x)
  | FF (x, []) when List.mem x xs -> V (Signature.var_called x)
  | FF (f, ts) -> F (Signature.fun_called f, List.map (convert_term xs) ts)

let convert_rule xs (l, r) =
 Literal.make_axiom (convert_term xs l, convert_term xs r)

let convert_goal xs (l, r) =
 Literal.make_neg_axiom (convert_term xs l, convert_term xs r)

let convert_rules (xs, rs, th, cs) =
  let rules = List.map (convert_rule xs) rs in
  let c = match cs with
    | [] -> None
    | [e] ->
      Some (convert_goal xs e)
    | _ -> 
      let f = "_goal" in
      let ss, ts = List.map fst cs, List.map snd cs in
      Some (convert_goal xs (FF(f, ss), FF(f, ts)))
  in
  List.iter (fun f -> Signature.add_ac_symbol (Signature.fun_called f)) th;
  rules, c
;;

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
%token AC INNERMOST CONTEXTSENSITIVE
%token COND_TYPE OR CONDITION EQUALS

%type <Literal.t list * Literal.t option> toplevel
%start toplevel

%%

toplevel:
  | decl EOF { convert_rules $1 }

decl:
  | LPAREN VAR       vars       RPAREN decl { add $3 [] [] $5 }
  | LPAREN RULES     rules      RPAREN decl { add [] $3 [] $5 }
  | LPAREN STRATEGY  INNERMOST  RPAREN decl { $5 }
  | LPAREN COND_TYPE IDENT      RPAREN decl { $5 }
  | LPAREN THEORY    theory     RPAREN decl { add [] [] $3 $5 }
  | LPAREN CONDITION conditions RPAREN decl { add_conditions $3 $5 }
  | LPAREN IDENT     anylist    RPAREN decl { $5 }
  |                                         { ([], [], [], []) }
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
  | term ARROW term rule_condition { ($1, $3) }
  | error                          { syntax_error "Syntax error." }

rule_condition:
  | OR conditions {}
  | {}

conditions:
  | condition conditionsx { $1 :: $2 }

conditionsx:
  | COMMA condition conditionsx { $2 :: $3 }
  | { [] }

condition:
  | term EQUALS term { ($1, $3) }
  | error            { syntax_error "Syntax error." }

term:
  | IDENT LPAREN terms RPAREN { FF ($1, $3) }
  | IDENT                     { FF ($1, []) }
  | error { syntax_error "Syntax error." }

terms:
  | term COMMA terms { $1 :: $3 }
  | term             { [$1] }
  |                  { [] }
