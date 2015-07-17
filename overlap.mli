type t = Rule.t * int list * Rule.t * Subst.t

val overlap : Rules.t -> t list

val overlap2 : Rules.t -> Rules.t -> t list

val cp_rules : Rules.t -> (Rule.t * Rules.t) list

val cp_of_overlap : t -> Rule.t

val cp : Rules.t -> Rules.t

val cp2 : Rules.t -> Rules.t -> Rules.t

val cp2b : bool -> Rules.t -> Rules.t -> Rules.t

val non_overlapping : Rules.t -> bool
