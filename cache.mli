val ht_cvars : (Constraint.c, Yices.expr) Hashtbl.t

val ht_trsvars : (int, Yices.expr) Hashtbl.t

val ht_itrss : (int, Rules.t) Hashtbl.t

val ht_cvars : (Constraint.c, Yices.expr) Hashtbl.t

val find_trs_var : int -> Yices.expr

val find_rule : Rule.t -> Yices.expr

val find_eq : Rule.t -> Yices.expr

val find_eq_weight : Rule.t -> Yices.expr

val find_weak_var : int * Rule.t -> Yices.expr

val find_strict_var : int * Rule.t -> Yices.expr

val get_strict_var : Yices.context -> (int * Rule.t) -> Yices.expr

val get_weak_var : Yices.context -> (int * Rule.t) -> Yices.expr

val contains : int -> int -> bool

val assert_rule : Rule.t -> (Rule.t -> unit) -> unit

val trs_of_index : int -> Rule.t list

val redtrs_of_index : int -> Rules.t

val store_rule_vars : Yices.context -> Rule.t list -> unit

val store_eq_vars : Yices.context -> Rule.t list -> unit

val store_trs : Rules.t -> int

val store_redtrs : Rules.t -> int -> unit

val assert_with : Yices.context -> (Yices.context -> Term.t -> Term.t -> Yices.expr) -> Constraint.t list -> unit

val get_all_strict : int -> (Rule.t * Yices.expr) list

val was_oriented : Rule.t -> bool

val clear : unit -> unit

val decode : Yices.model -> int -> unit
