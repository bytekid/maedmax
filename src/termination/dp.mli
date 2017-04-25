val x_def : Signature.sym -> Yicesx.t

val init : Yices.context -> Rules.t -> Yicesx.t

val cands_rule : Rule.t -> (Rule.t * Signature.sym) list

val cands_trs : Rules.t -> (Rule.t * Signature.sym) list

val sharp_signature : (Signature.sym * int) list -> (Signature.sym * int) list

val dp_constraint : Yices.context -> int -> Rule.t -> Yicesx.t

val decode_print: int -> Yices.model -> unit
