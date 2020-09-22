
val gt : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val ge : (Settings.Logic.context * int) -> Term.t -> Term.t -> Settings.Logic.t

val init : Settings.t -> Settings.Logic.context -> int -> Settings.Logic.t

val decode_print : int -> Settings.Logic.model -> unit

val decode: int -> Settings.Logic.model -> Order.t

val cond_gt : int -> Settings.Logic.context -> (Term.t * Term.t) list ->
  Term.t -> Term.t -> Settings.Logic.t

val eval_table : int -> Settings.Logic.model ->
  (int * 'a, Settings.Logic.t) Hashtbl.t -> ('a, int) Hashtbl.t

val eval_bool_table : int -> Settings.Logic.model ->
  (int * 'a, Settings.Logic.t) Hashtbl.t -> ('a, bool) Hashtbl.t