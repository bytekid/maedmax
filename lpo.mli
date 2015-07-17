val set_af : unit -> unit

val ylpo_gt : (Yices.context * int) -> Term.t -> Term.t -> Yices.expr

val ylpo_ge : (Yices.context * int) -> Term.t -> Term.t -> Yices.expr

val ylpo_af_gt : (Yices.context * int) -> Term.t -> Term.t -> Yices.expr

val ylpo_af_ge : (Yices.context * int) -> Term.t -> Term.t -> Yices.expr

val init : (Yices.context * int) -> (Signature.sym * int) list -> Yices.expr

val init_af : (Yices.context * int) -> (Signature.sym * int) list -> Yices.expr

val decode: int -> Yices.model -> unit

val decode_af: int -> Yices.model -> unit

val clear : unit -> unit
