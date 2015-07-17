val init_without_sccs : unit -> unit

val init_with_sccs : Yices.context -> (Signature.sym * int) list -> int -> int -> Yices.expr

val x_edge : Yices.context -> int -> Rule.t -> Rule.t -> Yices.expr

val has_edge : Yices.context -> Rule.t -> Rule.t -> Yices.expr

val has_edge' : Yices.context -> Rule.t -> Rule.t -> Yices.expr

val has_edge_bool : Rule.t -> Rule.t -> bool

val x_w : Yices.context -> int -> Signature.sym -> Yices.expr

val x_scc : Yices.context -> int -> Signature.sym -> Yices.expr

val decode : int -> Yices.model -> unit

val decode_scc : int -> int -> Yices.model -> unit

val uf : Rule.t list -> Signature.sym list list
