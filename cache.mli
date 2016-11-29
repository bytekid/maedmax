val ht_trsvars : (int, Yicesx.t) Hashtbl.t

val ht_itrss : (int, Rules.t) Hashtbl.t

val find_trs_var : int -> Yicesx.t

val find_rule : Rule.t -> Yicesx.t

val find_eq : Rule.t -> Yicesx.t

val find_eq_weight : Rule.t -> Yicesx.t

val rule_var : Yices.context -> Rule.t -> Yicesx.t

val eq_var : Yices.context -> Rule.t -> Yicesx.t

val eq_weight_var : Yices.context -> Rule.t -> Yicesx.t

val find_weak_var : int * Rule.t -> Yicesx.t

val find_strict_var : int * Rule.t -> Yicesx.t

val get_strict_var : Yices.context -> (int * Rule.t) -> Yicesx.t

val get_weak_var : Yices.context -> (int * Rule.t) -> Yicesx.t

val contains : int -> int -> bool

val assert_rule : Rule.t -> (Rule.t -> unit) -> unit

val trs_of_index : int -> Rule.t list

val redtrs_of_index : int -> Rules.t

val store_rule_vars : Yices.context -> Rule.t list -> unit

val store_eq_vars : Yices.context -> Rule.t list -> unit

val store_trs : Rules.t -> int

val store_redtrs : Rules.t -> int -> unit

val get_all_strict : int -> (Rule.t * Yicesx.t) list

val was_oriented : Rule.t -> bool

val clear : unit -> unit

val decode : Yices.model -> int -> unit
