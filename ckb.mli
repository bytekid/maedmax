val settings: Settings.t

(* given settings, equations and goals, produce a (ground-)complete system *)
val ckb : Settings.t -> Rules.t -> Rules.t -> (Rules.t * Rules.t)
