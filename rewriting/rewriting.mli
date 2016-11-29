val u_nf : Rules.t -> Term.t -> Rules.t option * Term.t

val nf : Rules.t -> Term.t -> Term.t

val nf_with : Rules.t -> Term.t -> Rules.t * Term.t

val nf_with_ht : (Term.t, Rules.t * Term.t) Hashtbl.t ->  Rules.t -> Term.t -> Rules.t * Term.t

val reducible_with : Rules.t -> Term.t -> bool
