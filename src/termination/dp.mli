val x_def : Signature.sym -> Settings.Logic.t

val init : Settings.Logic.context -> Rules.t -> Settings.Logic.t

val cands_rule : Rule.t -> (Rule.t * Signature.sym) list

val cands_trs : Rules.t -> (Rule.t * Signature.sym) list

val sharp_signature : (Signature.sym * int) list -> (Signature.sym * int) list

val dp_constraint : Settings.Logic.context -> int -> Rule.t -> Settings.Logic.t

val decode_print: int -> Settings.Logic.model -> unit
