val settings: Settings.t

(* given settings, equations and goals, produce a (ground-)complete system *)
val ckb : Settings.t -> (Literal.t list * Literal.t list) -> Settings.result
