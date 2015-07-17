type token =
  | IDENT of (string)
  | VAR of (string)
  | FILE of (string)
  | LPAREN
  | RPAREN
  | EQ
  | INEQ
  | COMMA
  | SEMICOLON
  | EOF
  | TICK
  | DOT
  | COMMENT
  | CNF
  | AXIOM
  | HYPOTHESIS
  | CONJECTURE
  | NCONJECTURE
  | INCLUDEAXIOMS

val toplevel :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> string list * Rules.t
