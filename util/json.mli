type t =
   Int of int
 | Float of float
 | String of string
 | Assoc of (string * t) list

val to_string : t -> string
