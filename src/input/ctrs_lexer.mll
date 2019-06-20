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

let bv_op op ws =
  let w = int_of_string ws in
  match op with
  | "+" -> OP_BV_ADD w
  | "-" -> OP_BV_SUB w
  | "|" -> OP_BV_OR w
  | "&" -> OP_BV_AND w
  | "^" -> OP_BV_XOR w
  | "=" -> OP_BV_EQ w
  | "<=" -> OP_BV_LE w
  | "<" -> OP_BV_LT w
  | ">=" -> OP_BV_LE w
  | ">" -> OP_BV_LT w
  | _ -> failwith "unknown bitvector operator"
;;

exception Lexing_error of string

let new_line lexbuf =
  lexbuf.lex_curr_p <- 
    { lexbuf.lex_curr_p with
      pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      pos_bol = lexbuf.lex_curr_p.pos_cnum }

}

let bv_op_sym = ['&' '|' '=' '<' '>' '^' '~' '-' '+' '*']

let letter = 
  ['a'-'z' 'A'-'Z' '0'-'9' ':' '<' '>' '_' '@' '`' '$'
   '{' '}' '-' '~' '?' '"' '!' '%']

let num = ['0' - '9']+

let hex = ['0' - '9' 'a'-'f']+


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
  | '"'    { QUOTE }
  | "#"    { HASH }
  | "\\/"  { OP_OR }
  | "/\\"  { OP_AND }
  | "="    { OP_EQUAL }
  | "END OF FILE"    { EOF }
  | (bv_op_sym+ as op) "." (num as n) { bv_op op n }
  | "bv" (num as n) "\"#x" (hex as v) "\"" { CONST (v, int_of_string n) }
  | (letter+ as id) "." (num as n) { IDENT_BITS (id, int_of_string n) }
  | letter+ as s { ident_or_keyword s }
  | _      { OTHER }
  | eof    { EOF }
