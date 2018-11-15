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

let union2 (xs, ys) (xs', ys') = (xs @ xs', ys @ ys')

let is_unit = List.for_all (function [e] -> true | _ -> false)

let to_unit = List.map (function [e] -> e | _ -> failwith "Read.to_unit")

let transform_input cls gs =
  if not (is_unit cls && is_unit gs) then
    Settings.NonUnit(cls, gs)
  else
    let eqs, gs = to_unit cls, to_unit gs in
    let gs_pos, gs_neg = List.partition Literal.is_equality gs in
    let gs_neg' = List.map Literal.to_goal gs_neg in
    Settings.Unit(eqs @ gs_pos, gs_neg')
;;

let read_tptp orig_filename =
  let rec read_tptp filename =
    let fn =
      if Sys.file_exists filename then filename
      else match Sys.getenv_opt  "TPTP" with
      | Some tptp -> Filename.concat tptp filename
      | None -> (
        let dir = Filename.dirname orig_filename in
        let fn_dir = Filename.concat dir filename in
        if Sys.file_exists fn_dir then fn_dir
        else
          raise (Sys_error ("Input file" ^ filename ^ " was not found."))
      )
    in
    let read ch =
      let lexbuf = from_channel ch in
      let lex_curr_p = { lexbuf.lex_curr_p with pos_fname = filename } in
      try
        TptpParser.toplevel TptpLexer.token { lexbuf with lex_curr_p=lex_curr_p }
      with Parsing.Parse_error ->
        (syntax_error lexbuf.lex_curr_p; exit 1)
    in
    try
      let axs, cls, gls = open_in_do ~path:fn read in
      let add res a = let res' = read_tptp a in union2 res res' in
      List.fold_left add (cls, gls) axs
    with Sys_error s ->
      (eprintf "Error:@.%s@." s; exit 1)
  in
  let cls, gs = read_tptp orig_filename in
  transform_input cls gs
;;

let file filename = 
  if Filename.check_suffix filename "trs"  then
    Settings.Unit(fst (read_trs filename), [])
  else
    read_tptp filename
;;

let equation_or_inequality s =
  let lexbuf = from_string s in
  try
    TptpParser.equation_or_inequality TptpLexer.token lexbuf
  with Parsing.Parse_error ->
    ((*syntax_error lexbuf.lex_curr_p;*) failwith "parse error")
;; 
