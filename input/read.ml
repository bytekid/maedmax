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

let read_file parse lex filename =
  let f ch = 
    let lexbuf = from_channel ch in
    let lex_curr_p = 
      { lexbuf.lex_curr_p with pos_fname = filename } in
    try
      parse lex { lexbuf with lex_curr_p = lex_curr_p }
    with Parsing.Parse_error -> 
      (syntax_error lexbuf.lex_curr_p; exit 1)
  in
  try
    open_in_do ~path:filename f
  with Sys_error s -> 
    (eprintf "Error:@.%s@." s; exit 1)


let rec read_tptp parse lex filename =
  let f ch =
    let lexbuf = from_channel ch in
    let lex_curr_p =
      { lexbuf.lex_curr_p with pos_fname = filename } in
    try
      parse lex { lexbuf with lex_curr_p = lex_curr_p }
    with Parsing.Parse_error ->
      (syntax_error lexbuf.lex_curr_p; exit 1)
  in
  try
    let axs, rls = open_in_do ~path:filename f in 
    List.fold_left (fun rs a -> read_tptp parse lex a @ rs ) rls axs
  with Sys_error s ->
    (eprintf "Error:@.%s@." s; exit 1)

let read_trs filename = 
  if Filename.check_suffix filename "trs"  then
   read_file Parser.toplevel Lexer.token filename
  else read_tptp TptpParser.toplevel TptpLexer.token filename,[]
