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

open Parsing;;
let _ = parse_error;;
# 2 "tptpParser.mly"
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

let add_axioms a (aa,ee) =  a::aa, ee

let add_equation e (aa,ee) = aa, e::ee

# 56 "tptpParser.ml"
let yytransl_const = [|
  260 (* LPAREN *);
  261 (* RPAREN *);
  262 (* EQ *);
  263 (* INEQ *);
  264 (* COMMA *);
  265 (* SEMICOLON *);
    0 (* EOF *);
  266 (* TICK *);
  267 (* DOT *);
  268 (* COMMENT *);
  269 (* CNF *);
  270 (* AXIOM *);
  271 (* HYPOTHESIS *);
  272 (* CONJECTURE *);
  273 (* NCONJECTURE *);
  274 (* INCLUDEAXIOMS *);
    0|]

let yytransl_block = [|
  257 (* IDENT *);
  258 (* VAR *);
  259 (* FILE *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\003\000\004\000\005\000\007\000\007\000\006\000\006\000\008\000\
\008\000\008\000\008\000\009\000\009\000\009\000\000\000"

let yylen = "\002\000\
\002\000\006\000\002\000\002\000\002\000\002\000\000\000\001\000\
\011\000\011\000\011\000\001\000\001\000\003\000\001\000\004\000\
\001\000\001\000\001\000\003\000\001\000\000\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\008\000\000\000\000\000\000\000\023\000\000\000\
\000\000\000\000\000\000\006\000\000\000\000\000\001\000\003\000\
\004\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\
\012\000\013\000\000\000\000\000\000\000\000\000\000\000\002\000\
\000\000\000\000\000\000\000\000\000\000\018\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\019\000\
\000\000\000\000\000\000\014\000\000\000\000\000\000\000\016\000\
\009\000\010\000\011\000\020\000"

let yydgoto = "\002\000\
\007\000\008\000\009\000\010\000\011\000\039\000\027\000\040\000\
\050\000"

let yysindex = "\008\000\
\001\255\000\000\000\000\001\255\013\255\027\255\000\000\032\000\
\001\255\001\255\001\255\000\000\032\255\031\255\000\000\000\000\
\000\000\000\000\028\255\030\255\011\255\026\255\033\255\034\255\
\000\000\000\000\035\255\001\255\036\255\040\255\041\255\000\000\
\002\255\002\255\002\255\000\000\042\255\000\000\043\255\044\255\
\046\255\047\255\021\255\048\255\021\255\049\255\050\255\000\000\
\039\255\051\255\038\255\000\000\052\255\053\255\021\255\000\000\
\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\038\000\000\000\000\000\038\000\000\000\000\000\000\000\000\000\
\038\000\038\000\038\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\038\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\255\010\255\000\000\000\000\000\000\
\000\000\000\000\030\255\000\000\000\000\000\000\000\000\000\000\
\054\255\000\000\000\000\000\000\000\000\000\000\030\255\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\252\255\000\000\000\000\000\000\251\255\000\000\221\255\
\240\255"

let yytablesize = 64
let yytable = "\012\000\
\003\000\036\000\037\000\038\000\016\000\017\000\018\000\049\000\
\001\000\052\000\015\000\019\000\004\000\005\000\017\000\017\000\
\013\000\017\000\006\000\049\000\048\000\037\000\038\000\032\000\
\023\000\024\000\025\000\026\000\041\000\042\000\014\000\015\000\
\019\000\020\000\022\000\021\000\028\000\007\000\060\000\033\000\
\029\000\030\000\031\000\034\000\035\000\043\000\055\000\044\000\
\057\000\045\000\046\000\047\000\051\000\053\000\054\000\056\000\
\000\000\000\000\021\000\000\000\000\000\000\000\058\000\059\000"

let yycheck = "\004\000\
\000\001\000\001\001\001\002\001\009\000\010\000\011\000\043\000\
\001\000\045\000\005\001\006\001\012\001\013\001\005\001\006\001\
\004\001\008\001\018\001\055\000\000\001\001\001\002\001\028\000\
\014\001\015\001\016\001\017\001\034\000\035\000\004\001\000\000\
\001\001\003\001\005\001\008\001\011\001\000\000\055\000\004\001\
\008\001\008\001\008\001\004\001\004\001\004\001\008\001\005\001\
\011\001\006\001\005\001\005\001\005\001\005\001\005\001\005\001\
\255\255\255\255\005\001\255\255\255\255\255\255\011\001\011\001"

let yynames_const = "\
  LPAREN\000\
  RPAREN\000\
  EQ\000\
  INEQ\000\
  COMMA\000\
  SEMICOLON\000\
  EOF\000\
  TICK\000\
  DOT\000\
  COMMENT\000\
  CNF\000\
  AXIOM\000\
  HYPOTHESIS\000\
  CONJECTURE\000\
  NCONJECTURE\000\
  INCLUDEAXIOMS\000\
  "

let yynames_block = "\
  IDENT\000\
  VAR\000\
  FILE\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 47 "tptpParser.mly"
             ( _1 )
# 183 "tptpParser.ml"
               : string list * Rules.t))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 50 "tptpParser.mly"
                                              ( add_axioms _3 _6)
# 191 "tptpParser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'axiom) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 51 "tptpParser.mly"
               ( add_equation _1 _2 )
# 199 "tptpParser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'hypothesis) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 52 "tptpParser.mly"
                    ( add_equation _1 _2 )
# 207 "tptpParser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'conjecture) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 53 "tptpParser.mly"
                    ( _2 )
# 215 "tptpParser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 54 "tptpParser.mly"
                 ( _2 )
# 222 "tptpParser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "tptpParser.mly"
    ( [],[] )
# 228 "tptpParser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "tptpParser.mly"
          ( syntax_error "Syntax error." )
# 234 "tptpParser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _8 = (Parsing.peek_val __caml_parser_env 3 : 'equation) in
    Obj.repr(
# 59 "tptpParser.mly"
                                                                        ( _8 )
# 242 "tptpParser.ml"
               : 'axiom))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _8 = (Parsing.peek_val __caml_parser_env 3 : 'equation) in
    Obj.repr(
# 62 "tptpParser.mly"
                                                                             ( _8 )
# 250 "tptpParser.ml"
               : 'hypothesis))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 6 : 'conjecturetype) in
    let _8 = (Parsing.peek_val __caml_parser_env 3 : 'equation) in
    Obj.repr(
# 65 "tptpParser.mly"
                                                                                 ( _8 )
# 259 "tptpParser.ml"
               : 'conjecture))
; (fun __caml_parser_env ->
    Obj.repr(
# 68 "tptpParser.mly"
              ( () )
# 265 "tptpParser.ml"
               : 'conjecturetype))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "tptpParser.mly"
               ( () )
# 271 "tptpParser.ml"
               : 'conjecturetype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 72 "tptpParser.mly"
                 ( (_1, _3) )
# 279 "tptpParser.ml"
               : 'equation))
; (fun __caml_parser_env ->
    Obj.repr(
# 73 "tptpParser.mly"
               ( syntax_error "Syntax error." )
# 285 "tptpParser.ml"
               : 'equation))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'terms) in
    Obj.repr(
# 76 "tptpParser.mly"
                              ( func _1 _3 )
# 293 "tptpParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 77 "tptpParser.mly"
                              ( func _1 [] )
# 300 "tptpParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 78 "tptpParser.mly"
                              ( var _1 )
# 307 "tptpParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "tptpParser.mly"
          ( syntax_error "Syntax error." )
# 313 "tptpParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'terms) in
    Obj.repr(
# 82 "tptpParser.mly"
                     ( _1 :: _3 )
# 321 "tptpParser.ml"
               : 'terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 83 "tptpParser.mly"
                     ( [_1] )
# 328 "tptpParser.ml"
               : 'terms))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "tptpParser.mly"
                     ( [] )
# 334 "tptpParser.ml"
               : 'terms))
(* Entry toplevel *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let toplevel (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : string list * Rules.t)
