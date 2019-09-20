type t = Rule.t * int list * Rule.t * Subst.t

val overlap_between_at : Rule.t -> Rule.t -> int list -> t option

val overlaps_between : Rule.t -> Rule.t -> t list

val overlaps : Rules.t -> t list

val cp_rules : Rules.t -> (Rule.t * Rules.t) list

val cp_of_overlap : t -> Rule.t

val cps : Rules.t -> Rules.t

val nontrivial_cps : Rule.t -> Rule.t -> Rule.t list

val subst : t -> Term.subst