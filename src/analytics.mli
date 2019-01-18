
val t_cache : float ref
val t_ccomp : float ref
val t_ccpred : float ref
val t_cred : float ref
val t_gjoin_check : float ref
val t_maxk : float ref
val t_rewrite : float ref
val t_rewrite_goals : float ref
val t_orient_constr : float ref
val t_overlap : float ref
val t_process : float ref
val t_sat : float ref
val t_select : float ref
val t_success_check : float ref
val t_subsumption: float ref
val t_tmp1 : float ref
val t_tmp2 : float ref
val t_tmp3 : float ref
val equalities : int ref
val goals : int ref
val iterations : int ref
val restarts : int ref
val smt_checks : int ref
val time_diffs : float list ref
val mem_diffs : int list ref
val eq_counts : int list ref
val goal_counts : int list ref
val shape : Settings.shape ref

val memory : unit -> int

val set_time_mem : unit -> unit

val runtime : unit -> float

val is_duplicating : Rules.t -> bool

val take_time : float ref -> ('a -> 'b) -> 'a -> 'b

val analyze : Literal.t list -> Literal.t list -> Yojson.Basic.json

val problem_shape : Rules.t-> Settings.shape

val theory_equations : Literal.t list -> Literal.t list

val json : unit -> Yojson.Basic.json

val print : unit -> unit

val init_proof_track : Literal.t list -> unit

val update_proof_track : Literal.t list -> Literal.t list -> unit

val show_proof_track : Settings.t -> (Literal.t * 'a) list ref -> unit

val little_progress : int -> bool

val some_progress : unit -> bool

val goal_similarity : Settings.t -> Literal.t -> float

val restart : unit -> unit

val add_state : int -> int -> int -> int -> unit

val last_cp_count : unit -> int
