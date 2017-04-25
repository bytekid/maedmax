val set_af : unit -> unit

val gt : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val ge : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val gt_af : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val ge_af : (Yices.context * int) -> Term.t -> Term.t -> Yicesx.t

val init : (Yices.context * int) -> (Signature.sym * int) list -> Yicesx.t

val init_af : (Yices.context * int) -> (Signature.sym * int) list -> Yicesx.t

val decode_print: int -> Yices.model -> unit

val decode_term_gt : int -> Yices.model -> (Term.t -> Term.t -> bool)

val decode_print_af: int -> Yices.model -> unit

val decode: int -> Yices.model -> Order.t

val clear : unit -> unit

val cond_gt : int -> Yices.context -> (Term.t * Term.t) list -> Term.t ->
              Term.t -> Yicesx.t
