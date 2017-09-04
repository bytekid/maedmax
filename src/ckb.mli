type rewrite_steps = (Rule.t * Term.pos * Term.t) list
type result = Completion of Rules.t
  | GroundCompletion of (Rules.t * Rules.t * Order.t)
  | Proof of (Rule.t * (rewrite_steps * rewrite_steps) * Subst.t)
  | Disproof of (Rules.t * Rules.t * Order.t * (rewrite_steps * rewrite_steps))

val settings: Settings.t

(* given settings, equations and goals, produce a (ground-)complete system *)
val ckb : Settings.t -> (Literal.t list * Literal.t list) -> result
