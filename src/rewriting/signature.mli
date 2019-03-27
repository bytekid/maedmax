type var = int

type sym = int

type t = (sym * int) list

val get_var_name : var -> string

val get_fun_name : sym -> string

val fresh_var : unit -> var

val fresh_fun : unit -> sym

val var_called : string -> var

val fun_called : string -> sym

val fresh_fun_called : string -> sym

val fresh_var_called : string -> var

val sharp_fun : sym -> sym

val is_ac_symbol : sym -> bool

val ac_symbols : unit -> sym list

val add_ac_symbol : sym -> unit
