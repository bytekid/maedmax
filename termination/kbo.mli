
val gt : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val ge : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val init : (Yices.context * int) -> (Signature.sym * int) list -> Yicesx.t

val decode : int -> Yices.model -> unit

val decode_term_gt : int -> Yices.model -> (Term.t -> Term.t -> bool)

val cond_gt : int -> Yices.context -> (Term.t * Term.t) list -> Term.t ->
              Term.t -> Yicesx.t
