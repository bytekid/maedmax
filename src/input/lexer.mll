{
open Lexing
open Parser

let ident_or_keyword = function
  | "VAR" -> VAR
  | "RULES" -> RULES
  | "STRATEGY" -> STRATEGY
  | "INNERMOST" -> INNERMOST
  | "THEORY" -> THEORY
  | "AC" -> AC
  | s -> IDENT s

exception Lexing_error of string

let new_line lexbuf =
  lexbuf.lex_curr_p <- 
    { lexbuf.lex_curr_p with
      pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      pos_bol = lexbuf.lex_curr_p.pos_cnum }

}

let letter = 
  ['a'-'z' 'A'-'Z' '0'-'9' '\''
   '#' '+' '-' '*' '/' '.' '\\' ':' '=' '<' '>' '_' '@' '`' '$'
   '{' '}' '[' ']' '|' '~' '?' '&' '"' '!' '%']

rule token = parse
  | [' ' '\r' '\t'] {  token lexbuf }
  | '\n'   { new_line lexbuf; token lexbuf }
  | ";"    { SEMICOLON }
  | "->="  { ARROWEQ }
  | "->"   { ARROW }
  | "("    { LPAREN }
  | ")"    { RPAREN }
  | ","    { COMMA }
  | letter+ as s { ident_or_keyword s }
  | _      { OTHER }
  | eof    { EOF }
