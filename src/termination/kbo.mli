
val gt : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val ge : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val init : (Settings.Logic.context * int) -> (Signature.sym * int) list ->
  Settings.Logic.t

val decode_print : int -> Settings.Logic.model -> unit

val decode_term_gt : int -> Settings.Logic.model -> (Term.t -> Term.t -> bool)

val decode: int -> Settings.Logic.model -> Order.t

val cond_gt : int -> Settings.Logic.context -> (Term.t * Term.t) list ->
  Term.t -> Term.t -> Settings.Logic.t
