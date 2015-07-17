val eq_variant : Term.t * Term.t -> Term.t * Term.t -> bool

val eq_subset : (Term.t * Term.t) list -> (Term.t * Term.t) list -> bool

val eq_set_equal : (Term.t * Term.t) list -> (Term.t * Term.t) list -> bool

val r_hat : Rules.t -> Rules.t

val reduce : Rules.t -> Rules.t

val right_reduce : Rules.t -> Rules.t

val remove_rule : Rule.t -> Rules.t -> Rules.t

val rename_rule : string list -> Rule.t -> Rule.t

val rename_rules : Rules.t -> Rules.t

val unique : eq:('a -> 'a -> bool) -> 'a list -> 'a list

val interreduce : Rules.t -> Rules.t * Rules.t

val union_es : Rules.t -> Rules.t -> Rules.t
