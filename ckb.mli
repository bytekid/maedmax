type result = Completion of Rules.t
  | GroundCompletion of (Rules.t * Rules.t)
  | Proof

val settings: Settings.t

(* given settings, equations and goals, produce a (ground-)complete system *)
val ckb : Settings.t -> Rules.t -> Rules.t -> result
