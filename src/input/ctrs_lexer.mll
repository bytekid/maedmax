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

let bv_op op =
  match op with
  | "+" -> OP_BV_ADD
  | "-" -> OP_BV_SUB
  | "|" -> OP_BV_OR
  | "&" -> OP_BV_AND
  | "^" -> OP_BV_XOR
  | "<=u" -> OP_BV_ULE
  | "<u" -> OP_BV_ULT
  | ">=u" -> OP_BV_UGE
  | ">u" -> OP_BV_UGT
  | "<=s" -> OP_BV_SLE
  | "<s" -> OP_BV_SLT
  | ">=s" -> OP_BV_SGE
  | ">s" -> OP_BV_SGT
  | _ -> failwith "unknown bitvector operator"
;;

exception Lexing_error of string

let new_line lexbuf =
  lexbuf.lex_curr_p <- 
    { lexbuf.lex_curr_p with
      pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      pos_bol = lexbuf.lex_curr_p.pos_cnum }

}

let bv_op_sym = ['&' '|' '=' '<' '>' '^' '~' '-' '+' '*' 'u' 's']

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
  | (bv_op_sym+ as op) { bv_op op }
  | "bv" (num as n) "\"#x" (hex as v) "\"" { CONST (v, int_of_string n) }
  | (letter+ as id) "." (num as n) { IDENT_BITS (id, int_of_string n) }
  | letter+ as s { ident_or_keyword s }
  | _      { OTHER }
  | eof    { EOF }
