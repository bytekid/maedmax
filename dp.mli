val x_def : Signature.sym -> Yices.expr

val init : Yices.context -> Constraint.t list -> Yices.expr

val cands_rule : Rule.t -> (Rule.t * Signature.sym) list

val cands_trs : Rules.t -> (Rule.t * Signature.sym) list

val sharp_signature : (Signature.sym * int) list -> (Signature.sym * int) list

val dp_constraint : Yices.context -> int -> Rule.t -> Yices.expr

val decode: int -> Yices.model -> unit
