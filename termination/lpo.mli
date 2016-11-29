val set_af : unit -> unit

val gt : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val ge : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val gt_af : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val ge_af : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val init : (Yices.context * int) -> (Signature.sym * int) list -> Yicesx.t

val init_af : (Yices.context * int) -> (Signature.sym * int) list -> Yicesx.t

val decode: int -> Yices.model -> unit

val decode_af: int -> Yices.model -> unit

val clear : unit -> unit
