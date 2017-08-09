type t = { ctx : Yices.context;
           expr: Yices.expr;
           decl: Yices.var_decl option;
           size: int }

val ctx : t -> Yices.context
val size : t -> int
val mk_context : unit -> Yices.context
val del_context : Yices.context -> unit
val show : t -> unit
val mk_true : Yices.context -> t
val mk_false : Yices.context -> t
val mk_zero : Yices.context -> t
val mk_one : Yices.context -> t
val mk_num : Yices.context -> int -> t
val mk_fresh_bool_var : Yices.context -> t
val mk_int_var : Yices.context -> string -> t
val is_true : t -> bool
val is_false : t -> bool
val (!!) : t -> t
val (<|>) : t -> t -> t
val (<&>) : t -> t -> t
val (<=>>) : t -> t -> t
val (<<=>>) : t -> t -> t
val big_and : Yices.context -> t list -> t
val big_and1 : t list -> t
val big_or : Yices.context -> t list -> t
val big_or1 : t list -> t
val (<+>) : t -> t -> t
val sum : Yices.context -> t list -> t
val sum1 : t list -> t
val (<>>) : t -> t -> t
val (<>=>) : t -> t -> t
val (<=>) : t -> t -> t
val (<!=>) : t -> t -> t
val ite : t -> t -> t -> t
val max : t -> t -> t
val require : t -> unit
val assert_weighted : t -> int -> unit
val push : Yices.context -> unit
val pop : Yices.context -> unit
val check : Yices.context -> bool
val max_sat : Yices.context -> bool
val get_model : Yices.context -> Yices.model
val eval : Yices.model -> t -> bool
val eval_int_var : Yices.model -> t -> int
val get_cost : Yices.model -> int
