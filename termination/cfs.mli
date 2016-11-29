
val gt : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val ge : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val init : (Yices.context * int) -> (Signature.sym * int) list -> Yicesx.t

val decode: int -> Yices.model -> unit

