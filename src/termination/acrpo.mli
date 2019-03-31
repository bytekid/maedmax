val gt : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val ge : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val init : (Settings.Logic.context * int) -> (Signature.sym * int) list ->
   Settings.Logic.t

val decode: int -> Settings.Logic.model -> Order.t

val decode_print: int -> Settings.Logic.model -> unit

