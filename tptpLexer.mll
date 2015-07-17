{
open Lexing
open TptpParser

let ident_or_keyword = function
  | "cnf" -> CNF
  | "axiom" -> AXIOM
  | "hypothesis" -> HYPOTHESIS
  | "conjecture" -> CONJECTURE
  | "negated_conjecture" -> NCONJECTURE
  | "include" -> INCLUDEAXIOMS
  | s -> IDENT s

exception Lexing_error of string

let new_line lexbuf =
  lexbuf.lex_curr_p <- 
    { lexbuf.lex_curr_p with
      pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      pos_bol = lexbuf.lex_curr_p.pos_cnum }

}

let upper = ['A'-'Z']
let lower = ['a'-'z']

let letter = 
  ['a'-'z' 'A'-'Z' '0'-'9'
   '#' '+' '-' '*' '/' '.' '\\' ':' '=' '<' '>' '_' '@' '`' '$'
   '{' '}' '[' ']' '|' '~' '?' '&' '"' '!']

let any =
  ['a'-'z' 'A'-'Z' '0'-'9' 
   '#' '+' '-' '*' '/' '.' ',' '\\' ':' ';' '=' '<' '>' '_' '@' '`' '$'
   '(' ')' '{' '}' '[' ']' '|' '~' '?' '&' '"' '!' '\'' ' ' '\t']

rule token = parse
  | [' ' '\r' '\t'] {  token lexbuf }
  | '\n'   { new_line lexbuf; token lexbuf }
  | ";"    { SEMICOLON }
  | "="  { EQ }
  | "!="   { INEQ }
  | "("    { LPAREN }
  | ")"    { RPAREN }
  | ","    { COMMA }
  | "."    { DOT }
  | "'" (letter+ as s) "'" { FILE s }
  | "%" any* { COMMENT }
  | (upper letter*) as s { VAR  s }
  | letter+ as s { ident_or_keyword s }
  | eof    { EOF }
