type lit = Literal.t

type theory_extension_state

type state = {
  context : Settings.Logic.context;
  equations : Nodes.t;
  goals : Nodes.t;
  new_nodes : lit list;
  last_trss : (Literal.t list * int * Order.t) list;
  extension : theory_extension_state option
}

val settings : Settings.t ref

val heuristic : Settings.heuristic ref

val make_state : Settings.Logic.context -> lit list -> Nodes.t -> state

val update_state : state -> Nodes.t -> Nodes.t -> state

val set_settings : Settings.t -> unit

val set_heuristic : Settings.heuristic -> unit

val set_iteration_stats : state -> unit

val store_remaining_nodes : Settings.Logic.context -> Nodes.t -> Nodes.t -> unit

val get_rewriter :  Settings.Logic.context -> int ->
  Settings.literal list * int * Order.t -> Rewriter.rewriter

val rewrite : ?max_size:int -> Rewriter.rewriter -> Nodes.t -> Nodes.t * Nodes.t

val reduced : ?max_size:int -> Rewriter.rewriter -> Nodes.t -> Nodes.t

val reduced_goals: Rewriter.rewriter -> Nodes.t -> Nodes.t * Nodes.t

val equations_for_overlaps: Nodes.t -> Nodes.t -> lit list

val overlaps: ?only_new:bool -> state -> lit list -> lit list -> Nodes.t * Overlapper.overlapper

val overlaps_on: lit list -> lit list -> Nodes.t -> Nodes.t

val max_k : state -> (lit list * int * Order.t) list

val succeeds : state -> (lit list * Nodes.t) -> Rewriter.rewriter ->
  (lit list * Nodes.t * Nodes.t) -> Rules.t -> Nodes.t ->
  (Settings.answer * Settings.proof) option

(* given settings and heuristic, equations and goals, try to produce a
  (ground-) complete system or refute a goal. *)
val ckb : Settings.t * Settings.heuristic -> (lit list * lit list)->
  Settings.result
