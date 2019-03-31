type t = Settings.termination_strategy

val ts_lpo : Settings.t_term
val ts_kbo : Settings.t_term

val strategy_red : t
val strategy_maxcomp : t
val strategy_maxcomp_lpo : t
val strategy_maxcomp_kbo : t
val strategy_lpo : t
val strategy_kbo : t
val strategy_mpol : t
val strategy_auto : t
val strategy_auto2 : t
val strategy_cpred : t
val strategy_comp : t
val strategy_dp : t
val strategy_dg : t
val strategy_dgk : t
val strategy_not_oriented : t
val strategy_temp : t
val strategy_ordered : t
val strategy_ordered_lpo : t
val strategy_ordered_kbo : t
val strategy_ordered_lpokbo : t
val strategy_ordered_sat : t
val strategy_aql : t
val strategy_order_generation : t
val strategy_ac : t

val get_termination : t -> Settings.t_term
val term_to_string : Settings.t_term -> string
val to_string : t -> string

val has_dps : Settings.t_term -> bool
val init : Settings.t_term -> int -> Settings.Logic.context -> Rules.t -> unit
val assert_constraints : Settings.t_term -> int -> Settings.Logic.context ->
  Rules.t -> unit
val bootstrap_constraints :
  int -> Settings.Logic.context -> (Rule.t * Settings.Logic.t) list ->
  Settings.Logic.t
val decode_print : int -> Settings.Logic.model -> Settings.t_term -> unit
val decode : int -> Settings.Logic.model -> Settings.t_term -> Order.t
val clear : unit -> unit
val cond_gt : Settings.t_term -> int -> Settings.Logic.context ->
  (Term.t * Term.t) list -> Term.t -> Term.t -> Settings.Logic.t
