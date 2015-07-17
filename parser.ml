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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
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

let convert_rule xs (l, r) = (convert_term xs l, convert_term xs r)

let convert_rules (xs, rs, th) = List.map (convert_rule xs) rs, th

let syntax_error msg =
  let p = symbol_start_pos () in
  Format.eprintf "File %S at line %d, character %d:@.%s@." 
    p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol + 1) msg;
  exit 1

# 48 "parser.ml"
let yytransl_const = [|
  258 (* LPAREN *);
  259 (* RPAREN *);
  260 (* ARROW *);
  261 (* ARROWEQ *);
  262 (* COMMA *);
  263 (* SEMICOLON *);
    0 (* EOF *);
  264 (* VAR *);
  265 (* RULES *);
  266 (* OTHER *);
  267 (* STRATEGY *);
  268 (* THEORY *);
  269 (* AC *);
  270 (* INNERMOST *);
  271 (* CONTEXTSENSITIVE *);
    0|]

let yytransl_block = [|
  257 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\006\000\006\000\007\000\007\000\007\000\007\000\007\000\003\000\
\003\000\005\000\005\000\008\000\008\000\004\000\004\000\009\000\
\009\000\010\000\010\000\010\000\011\000\011\000\011\000\000\000"

let yylen = "\002\000\
\002\000\005\000\005\000\005\000\005\000\005\000\000\000\001\000\
\002\000\000\000\003\000\001\000\001\000\001\000\001\000\002\000\
\000\000\005\000\000\000\002\000\000\000\002\000\000\000\003\000\
\001\000\004\000\001\000\001\000\003\000\001\000\000\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\008\000\000\000\032\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\012\000\000\000\013\000\014\000\
\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
\016\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\
\000\000\011\000\006\000\002\000\028\000\000\000\000\000\003\000\
\024\000\004\000\000\000\005\000\000\000\026\000\000\000\029\000\
\018\000"

let yydgoto = "\002\000\
\005\000\006\000\021\000\024\000\029\000\018\000\019\000\000\000\
\025\000\026\000\047\000"

let yysindex = "\004\000\
\004\255\000\000\000\000\000\255\000\000\010\000\019\255\012\255\
\015\255\018\255\024\255\000\000\000\000\019\255\000\000\000\000\
\000\000\033\255\019\255\012\255\038\255\000\000\040\255\041\255\
\015\255\042\255\044\255\030\255\045\255\046\255\004\255\000\000\
\000\000\004\255\039\255\004\255\000\000\039\255\004\255\049\255\
\004\255\000\000\000\000\000\000\000\000\047\255\048\255\000\000\
\000\000\000\000\051\255\000\000\039\255\000\000\024\255\000\000\
\000\000"

let yyrindex = "\000\000\
\045\000\000\000\000\000\000\000\000\000\000\000\052\255\053\255\
\054\255\000\000\055\255\000\000\000\000\052\255\000\000\000\000\
\000\000\000\000\052\255\053\255\000\000\034\255\027\255\000\000\
\054\255\000\000\000\000\000\000\000\000\000\000\045\000\000\000\
\000\000\045\000\033\255\045\000\000\000\000\000\045\000\000\000\
\045\000\000\000\000\000\000\000\000\000\056\255\000\000\000\000\
\000\000\000\000\000\000\000\000\033\255\000\000\055\255\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\239\255\032\000\035\000\006\000\244\255\000\000\000\000\
\000\000\221\255\009\000"

let yytablesize = 62
let yytable = "\046\000\
\007\000\030\000\049\000\003\000\001\000\004\000\032\000\008\000\
\009\000\012\000\010\000\011\000\020\000\043\000\022\000\023\000\
\044\000\046\000\048\000\013\000\014\000\050\000\015\000\052\000\
\016\000\028\000\027\000\027\000\017\000\027\000\027\000\027\000\
\027\000\025\000\025\000\031\000\025\000\028\000\045\000\023\000\
\034\000\035\000\040\000\036\000\007\000\038\000\039\000\041\000\
\042\000\051\000\054\000\033\000\053\000\055\000\010\000\017\000\
\023\000\019\000\030\000\037\000\057\000\056\000"

let yycheck = "\035\000\
\001\001\014\000\038\000\000\001\001\000\002\001\019\000\008\001\
\009\001\000\000\011\001\012\001\001\001\031\000\000\001\001\001\
\034\000\053\000\036\000\001\001\002\001\039\000\004\001\041\000\
\006\001\002\001\000\001\001\001\010\001\003\001\004\001\014\001\
\006\001\000\001\001\001\003\001\003\001\004\001\000\001\001\001\
\003\001\002\001\013\001\003\001\000\000\004\001\003\001\003\001\
\003\001\001\001\003\001\020\000\006\001\003\001\003\001\003\001\
\003\001\003\001\003\001\025\000\055\000\053\000"

let yynames_const = "\
  LPAREN\000\
  RPAREN\000\
  ARROW\000\
  ARROWEQ\000\
  COMMA\000\
  SEMICOLON\000\
  EOF\000\
  VAR\000\
  RULES\000\
  OTHER\000\
  STRATEGY\000\
  THEORY\000\
  AC\000\
  INNERMOST\000\
  CONTEXTSENSITIVE\000\
  "

let yynames_block = "\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 42 "parser.mly"
             ( convert_rules _1 )
# 171 "parser.ml"
               : Rules.t * string list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'vars) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 45 "parser.mly"
                                          ( add _3 [] [] _5 )
# 179 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'rules) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 46 "parser.mly"
                                          ( add [] _3 [] _5 )
# 187 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 47 "parser.mly"
                                          ( _5 )
# 194 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'theory) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 48 "parser.mly"
                                          ( add [] [] _3 _5 )
# 202 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'anylist) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 49 "parser.mly"
                                          ( _5 )
# 211 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
                                          ( ([], [], []) )
# 217 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 51 "parser.mly"
          ( syntax_error "Syntax error." )
# 223 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'any) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'anylist) in
    Obj.repr(
# 54 "parser.mly"
                ( () )
# 231 "parser.ml"
               : 'anylist))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
                ( () )
# 237 "parser.ml"
               : 'anylist))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'anylist) in
    Obj.repr(
# 58 "parser.mly"
                          ( () )
# 244 "parser.ml"
               : 'any))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 59 "parser.mly"
          ( () )
# 251 "parser.ml"
               : 'any))
; (fun __caml_parser_env ->
    Obj.repr(
# 60 "parser.mly"
          ( () )
# 257 "parser.ml"
               : 'any))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
          ( () )
# 263 "parser.ml"
               : 'any))
; (fun __caml_parser_env ->
    Obj.repr(
# 62 "parser.mly"
          ( () )
# 269 "parser.ml"
               : 'any))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'vars) in
    Obj.repr(
# 65 "parser.mly"
               ( _1 :: _2 )
# 277 "parser.ml"
               : 'vars))
; (fun __caml_parser_env ->
    Obj.repr(
# 66 "parser.mly"
               ( [] )
# 283 "parser.ml"
               : 'vars))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'theory) in
    Obj.repr(
# 69 "parser.mly"
                                  ( _3 :: _5 )
# 291 "parser.ml"
               : 'theory))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
               ( [] )
# 297 "parser.ml"
               : 'theory))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'idents) in
    Obj.repr(
# 73 "parser.mly"
                 ( _1 :: _2 )
# 305 "parser.ml"
               : 'idents))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
               ( [] )
# 311 "parser.ml"
               : 'idents))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'rule) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'rules) in
    Obj.repr(
# 77 "parser.mly"
               ( _1 :: _2 )
# 319 "parser.ml"
               : 'rules))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
    ( [] )
# 325 "parser.ml"
               : 'rules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 81 "parser.mly"
                    ( (_1, _3) )
# 333 "parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "parser.mly"
               ( syntax_error "Syntax error." )
# 339 "parser.ml"
               : 'rule))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'terms) in
    Obj.repr(
# 85 "parser.mly"
                              ( FF (_1, _3) )
# 347 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 86 "parser.mly"
                              ( FF (_1, []) )
# 354 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    Obj.repr(
# 87 "parser.mly"
          ( syntax_error "Syntax error." )
# 360 "parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'terms) in
    Obj.repr(
# 90 "parser.mly"
                     ( _1 :: _3 )
# 368 "parser.ml"
               : 'terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 91 "parser.mly"
                     ( [_1] )
# 375 "parser.ml"
               : 'terms))
; (fun __caml_parser_env ->
    Obj.repr(
# 92 "parser.mly"
                     ( [] )
# 381 "parser.ml"
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
   (Parsing.yyparse yytables 1 lexfun lexbuf : Rules.t * string list)
