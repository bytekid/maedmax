val u_nf : Rules.t -> Term.t -> Rules.t option * Term.t

val nf : Rules.t -> Term.t -> Term.t

val nf_with : Rules.t -> Term.t -> Rules.t * Term.t

val nf_with_at : Rules.t -> Term.t -> (Rule.t * int list * Subst.t) list * Term.t

val nf_with_ht : (Term.t, Rules.t * Term.t) Hashtbl.t ->  Rules.t -> Term.t -> Rules.t * Term.t

val reducible_with : Rules.t -> Term.t -> bool

val rewrite_at_root : Term.t -> Rules.t -> Rule.t option * Term.t

val step_at_with : Term.t -> int list -> Rule.t -> Term.t * Subst.t