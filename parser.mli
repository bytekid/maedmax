type token =
  | IDENT of (string)
  | LPAREN
  | RPAREN
  | ARROW
  | ARROWEQ
  | COMMA
  | SEMICOLON
  | EOF
  | VAR
  | RULES
  | OTHER
  | STRATEGY
  | THEORY
  | AC
  | INNERMOST
  | CONTEXTSENSITIVE

val toplevel :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Rules.t * string list
