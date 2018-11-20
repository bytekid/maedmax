module type Logic =
sig
  type t
  type context
  type model

  val ctx : t -> context
  val mk_context : unit -> context
  val del_context : context -> unit
  val reset : context -> context
  val show : t -> unit
  val mk_true : context -> t
  val mk_false : context -> t
  val mk_zero : context -> t
  val mk_one : context -> t
  val mk_num : context -> int -> t
  val mk_fresh_bool_var : context -> t
  val mk_int_var : context -> string -> t
  val is_true : t -> bool
  val is_false : t -> bool
  val (!!) : t -> t
  val (<|>) : t -> t -> t
  val (<&>) : t -> t -> t
  val (<=>>) : t -> t -> t
  val (<<=>>) : t -> t -> t
  val big_and : context -> t list -> t
  val big_and1 : t list -> t
  val big_or : context -> t list -> t
  val big_or1 : t list -> t
  val (<+>) : t -> t -> t
  val sum : context -> t list -> t
  val sum1 : t list -> t
  val (<>>) : t -> t -> t
  val (<>=>) : t -> t -> t
  val (<=>) : t -> t -> t
  val (<!=>) : t -> t -> t
  val ite : t -> t -> t -> t
  val max : t -> t -> t
  val require : t -> unit
  val assert_weighted : t -> int -> unit
  val push : context -> unit
  val pop : context -> unit
  val check : context -> bool
  val max_sat : context -> bool
  val get_model : context -> model
  val eval : model -> t -> bool
  val eval_int_var : model -> t -> int
  val get_cost : context -> model -> int
end
