(* given settings and heuristic, equations and goals, try to produce a
  (ground-) complete system or refute a goal. *)
val ckb : Settings.t * Settings.heuristic -> (Literal.t list * Literal.t list)
  -> Settings.result
