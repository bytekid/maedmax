
val gt : (Yices.context * int) -> Term.t -> Term.t -> Yices.expr

val ge : (Yices.context * int) -> Term.t -> Term.t -> Yices.expr

val init : (Yices.context * int) -> (Signature.sym * int) list -> Yices.expr

val decode: int -> Yices.model -> unit

val clear : unit -> unit
