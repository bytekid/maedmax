open Format
open Lexing

let finally handler f x =
  let r = try f x with e -> handler (); raise e in 
  handler (); r

let open_in_do ?path f =
  match path with 
  | None -> f stdin
  | Some file -> 
      let in_channel = open_in file in
      finally (fun () -> close_in in_channel) f in_channel


let syntax_error p =
  eprintf "File %S at line %d, character %d:@.Syntax error.@." 
    p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)

let read_trs filename =
  let f ch = 
    let lexbuf = from_channel ch in
    let lex_curr_p = 
      { lexbuf.lex_curr_p with pos_fname = filename } in
    try
      let buf = { lexbuf with lex_curr_p = lex_curr_p } in
      Parser.toplevel Lexer.token buf
    with Parsing.Parse_error -> 
      (syntax_error lexbuf.lex_curr_p; exit 1)
  in
  try
    open_in_do ~path:filename f
  with Sys_error s -> 
    (eprintf "Error:@.%s@." s; exit 1)

let union3 (xs,ys,zs) (xs',ys',zs') = (xs @ xs',ys @ ys',zs @ zs')

let rec read_tptp filename =
  let read ch =
    let lexbuf = from_channel ch in
    let lex_curr_p = { lexbuf.lex_curr_p with pos_fname = filename } in
    try
      TptpParser.toplevel TptpLexer.token { lexbuf with lex_curr_p=lex_curr_p }
    with Parsing.Parse_error ->
      (syntax_error lexbuf.lex_curr_p; exit 1)
  in
  try
    let axs, eqs, ieqs, gls = open_in_do ~path:filename read in
    let add res a = let res' = read_tptp a in union3 res res' in
    List.fold_left add (eqs,ieqs,gls) axs
  with Sys_error s ->
    (eprintf "Error:@.%s@." s; exit 1)

let read filename = 
  if Filename.check_suffix filename "trs"  then fst (read_trs filename), [], []
  else read_tptp filename
