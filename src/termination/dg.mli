val init_without_sccs : unit -> unit

val init_with_sccs : Settings.Logic.context -> (Signature.sym * int) list ->
  int -> int -> Settings.Logic.t

val x_edge : Settings.Logic.context -> int -> Rule.t -> Rule.t ->
  Settings.Logic.t

val has_edge : Settings.Logic.context -> Rule.t -> Rule.t -> Settings.Logic.t

val has_edge' : Settings.Logic.context -> Rule.t -> Rule.t -> Settings.Logic.t

val has_edge_bool : Rule.t -> Rule.t -> bool

val x_w : Settings.Logic.context -> int -> Signature.sym -> Settings.Logic.t

val x_scc : Settings.Logic.context -> int -> Signature.sym -> Settings.Logic.t

val decode_print : int -> Settings.Logic.model -> unit

val uf : Rule.t list -> Signature.sym list list
