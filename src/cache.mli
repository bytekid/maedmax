val ht_trsvars : (int, Settings.Logic.t) Hashtbl.t

val ht_rdcbl_constr : (Rule.t, Settings.Logic.t) Hashtbl.t

val ht_itrss : (int, Rules.t) Hashtbl.t

val ht_rewriters: (int, Rewriter.rewriter) Hashtbl.t

val find_trs_var : int -> Settings.Logic.t

val find_rule : Rule.t -> Settings.Logic.t

val find_eq : Rule.t -> Settings.Logic.t

val find_eq_weight : Rule.t -> Settings.Logic.t

val rule_var : Settings.Logic.context -> Rule.t -> Settings.Logic.t

val eq_var : Settings.Logic.context -> Rule.t -> Settings.Logic.t

val eq_weight_var : Settings.Logic.context -> Rule.t -> Settings.Logic.t

val find_weak_var : int * Rule.t -> Settings.Logic.t

val find_strict_var : int * Rule.t -> Settings.Logic.t

val get_strict_var : Settings.Logic.context -> (int*Rule.t) -> Settings.Logic.t

val get_weak_var : Settings.Logic.context -> (int * Rule.t) -> Settings.Logic.t

val get_rdcbl_var : Settings.Logic.context -> Rule.t -> Settings.Logic.t

val contains : int -> int -> bool

val assert_rule : Rule.t -> (Rule.t -> unit) -> unit

val trs_of_index : int -> Rule.t list

val redtrs_of_index : int -> Rules.t

val store_rule_var : Settings.Logic.context -> Rule.t -> Settings.Logic.t

val store_rule_vars : Settings.Logic.context -> Rule.t list -> unit

val store_eq_var : Settings.Logic.context -> Rule.t ->
  Settings.Logic.t * Settings.Logic.t

val store_eq_vars : Settings.Logic.context -> Rule.t list -> unit

val store_trs : Rules.t -> int

val store_redtrs : Rules.t -> int -> unit

val get_all_strict : int -> (Rule.t * Settings.Logic.t) list

val clear : unit -> unit

val decode_print : Settings.Logic.model -> int -> unit
