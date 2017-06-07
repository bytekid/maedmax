type result = Completion of Rules.t
  | GroundCompletion of (Rules.t * Rules.t * Order.t)
  | Proof of (Rule.t * ((Rule.t * Term.pos) list * (Rule.t * Term.pos) list) *
              Subst.t)

val settings: Settings.t

(* given settings, equations and goals, produce a (ground-)complete system *)
val ckb : Settings.t -> (Literal.literal list * Literal.literal list) -> result
