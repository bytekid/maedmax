open Term

let rec stol s = 
 let l = String.length s in 
 if l = 0 then []
 else 
  (String.sub s 0 1) :: (stol (String.sub s 1 (l-1)))

let matches s = 
 fun c -> List.mem c (stol s)

let wspace = matches " \t\n\r"
let brackets = matches "()"
let comma = matches ","
let arrow = matches "->"
let semicolon = matches ";"
let alphanum = matches "abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

let splittk t s =
  let rec splittk1 ttype head seq = 
    match seq with
    | [] -> head, seq
    | h :: tl -> 
	if ttype h then splittk1 ttype (head^h) tl
	else head, seq
  in
  splittk1 t "" s
    
exception AdHocLexerError of string

let rec lexer s =
  match snd (splittk wspace s) with
  | [] -> []
  | h :: tl ->
      if brackets h then h :: (lexer tl)
      else
	let ttype =
	  if comma h then comma
	  else if alphanum h then alphanum
	  else if arrow h then arrow
	  else if semicolon h then semicolon
	  else
	    raise (AdHocLexerError ("at: -> "^h^" <-"))
	in
	let token, rest = splittk ttype tl in
	(h^token) :: lexer rest

exception ParseError of string

let rec parse_term t = 
 match t with
 | "," :: tls -> parse_term tls
 | const_sym::"("::")"::tls -> F (Signature.fun_called const_sym,[]), tls
 | func_sym::"("::tl -> (     
     match parse_terms [] tl with
     | tm_ls, ")"::tls -> F (Signature.fun_called func_sym, tm_ls), tls
     | _ , _ -> raise (ParseError "missing closing bracket")
     )
 | var_name::tls -> V (Signature.fun_called var_name), tls
 | _ -> raise (ParseError ("not a valid term: "^(List.fold_left (^) "" t)))
and parse_terms trms tl =
 match tl with
 | [] -> raise (ParseError "missing closing bracket2")
 | ")"::tls -> trms, ")"::tls
 | _ -> 
     let t, rst = parse_term tl in
      parse_terms (trms @ [t]) rst

let parse_t t =
  let t, rest = parse_term (lexer (stol t)) in
  if rest = [] then t 
  else raise (ParseError "not a term")

let rec parse_rl r = 
 let ls = lexer (stol r) in
 match parse_term ls with
   | left, "->" :: tl -> (
       match parse_term tl with
       | right, [] -> (left, right)
       | _, tl -> raise  (ParseError "invalid rhs")
      )
   | _ , _ -> raise (ParseError "invalid lhs")

let parse_rls rls = 
 let rec parse_rls1 rls1 =
   match parse_term rls1 with
   | left, "->" :: tl -> (
       match parse_term tl with
       | right, [] -> [(left, right)]
       | right, ";" :: rest -> (left, right) :: (parse_rls1 rest)
       | _ , _ -> raise (ParseError "invalid rhs") 
      )
   | _ , _ -> raise (ParseError "invalid lhs")
 in parse_rls1 (lexer (stol rls))

let read_from_file f =
 let ic = open_in f in
 let n = in_channel_length ic in
 let s = String.create n in
 really_input ic s 0 n;
 close_in ic;
 parse_rls s
;;
