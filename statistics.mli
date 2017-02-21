
val t_cache : float ref
val t_ccomp : float ref
val t_ccpred : float ref
val t_cred : float ref
val t_gjoin_check : float ref
val t_maxk : float ref
val t_rewrite : float ref
val t_orient_constr : float ref
val t_overlap : float ref
val t_process : float ref
val t_sat : float ref
val t_select : float ref
val t_success_check : float ref
val t_tmp1 : float ref
val t_tmp2 : float ref

val ces : int ref
val goals : int ref
val iterations : int ref
val restarts : int ref

val time_diffs : float list ref
val mem_diffs : int list ref

val memory : unit -> int

val take_time : float ref -> ('a -> 'b) -> 'a -> 'b

val print : unit -> unit
val json : string -> int -> int -> Yojson.Basic.json
val analyze : Rules.t -> Yojson.Basic.json
