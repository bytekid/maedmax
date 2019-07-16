val set_af : unit -> unit

val gt : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val ge : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val gt_af : (Settings.Logic.context * int) -> Term.t -> Term.t ->
  Settings.Logic.t

val ge_af : (Settings.Logic.context * int) -> Term.t -> Term.t ->
  Settings.Logic.t

val init : (Settings.Logic.context * int) -> (Signature.sym * int) list ->
  Settings.Logic.t

val init_af : (Settings.Logic.context * int) -> (Signature.sym * int) list ->
  Settings.Logic.t

val fix_parameters : (Settings.Logic.context * int) -> Rules.t ->
  Settings.Logic.t

val decode_print: int -> Settings.Logic.model -> unit

val decode_term_gt : int -> Settings.Logic.model -> (Term.t -> Term.t -> bool)

val decode_print_af: int -> Settings.Logic.model -> unit

val decode: int -> Settings.Logic.model -> Order.t

val clear : unit -> unit

val cond_gt : int -> Settings.Logic.context -> (Term.t * Term.t) list ->
  Term.t -> Term.t -> Settings.Logic.t
