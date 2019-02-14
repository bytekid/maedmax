type var = int

type sym = int

type t = (sym * int) list

val get_var_name : var -> string

val get_fun_name : sym -> string

val fresh_var : unit -> var

val var_called : string -> var

val fun_called : string -> sym

val fresh_fun_called : string -> sym

val sharp_fun : sym -> sym
