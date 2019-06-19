{
open Lexing
open Ctrs_parser

let ident_or_keyword = function
  | "THEORY" -> THEORY
  | "RULES" -> RULES
  | "LOGIC" -> LOGIC
  | "SOLVER" -> SOLVER
  | "SIGNATURE" -> SIGNATURE
  | "NON-STANDARD" -> NON_STANDARD
  | "IRREGULAR" -> IRREGULAR
  | "QUERY" -> QUERY
  | s -> IDENT s

exception Lexing_error of string

let new_line lexbuf =
  lexbuf.lex_curr_p <- 
    { lexbuf.lex_curr_p with
      pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      pos_bol = lexbuf.lex_curr_p.pos_cnum }

}

let letter = 
  ['a'-'z' 'A'-'Z' '0'-'9' ':' '<' '>' '_' '@' '`' '$'
   '{' '}' '-' '~' '?' '"' '!' '%']

rule token = parse
  | [' ' '\r' '\t'] {  token lexbuf }
  | '\n'   { new_line lexbuf; token lexbuf }
  | ";"    { SEMICOLON }
  | "->"   { ARROW }
  | "("    { LPAREN }
  | ")"    { RPAREN }
  | "["    { LBRACKET }
  | "]"    { RBRACKET }
  | ","    { COMMA }
  | "."    { DOT }
  | '"'    { QUOTE }
  | "#"    { HASH }
  | "\\/"  { OP_OR }
  | "/\\"  { OP_AND }
  | "|"    { OP_BIT_OR }
  | "&"    { OP_BIT_AND }
  | "^"    { OP_BIT_XOR }
  | "+"    { OP_PLUS }
  | "-"    { OP_MINUS }
  | "*"    { OP_MULT }
  | "/"    { OP_DIV }
  | "="    { OP_EQUAL }
  | "END OF FILE"    { EOF }
  | letter+ as s { ident_or_keyword s }
  | _      { OTHER }
  | eof    { EOF }
