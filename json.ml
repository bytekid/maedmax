type t = 
   Int of int
 | Float of float
 | String of string
 | Assoc of (string * t) list

let encode s =
 let replace = ["\n","\\n"] in
 List.fold_left (fun r (p,sub) -> Str.global_replace (Str.regexp p) sub r) s replace
;;

let rec to_string = function
   Int i -> string_of_int i
 | Float f -> string_of_float f
 | String s -> "\""^(encode s)^"\""
 | Assoc [] -> "{}"
 | Assoc ((s,v) :: xs) ->
  let str (s,v) = "\""^s^"\": "^(to_string v) in
  let append r (s,v) =  r ^ ", " ^ (str (s,v)) in
  let s = List.fold_left append (str (s,v)) xs in
  "{"^s^"}"
;;
