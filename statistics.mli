val t_gc : float ref
val t_cache : float ref
val t_insert : float ref
val t_maxk : float ref
val t_norm : float ref
val t_project : float ref
val t_orient_constr : float ref
val t_overlap : float ref
val t_sat : float ref
val t_translate : float ref
val t_upd : float ref
val t_tmp1 : float ref
val t_tmp2 : float ref

val ces : int ref
val iterations : int ref
val restarts : int ref

val take_time : float ref -> ('a -> 'b) -> 'a -> 'b

val print : unit -> unit
val json : string -> int -> int -> Yojson.Basic.json
