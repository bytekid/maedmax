

module type Logic = sig
  type t
  type context
  type model

  module Int : sig
    val mk_var : context -> string -> t
    val mk_zero : context -> t
    val mk_one : context -> t
    val mk_num : context -> int -> t
    val (<+>) : t -> t -> t
    val sum : context -> t list -> t
    val sum1 : t list -> t
    val (<>>) : t -> t -> t
    val (<>=>) : t -> t -> t
    val max : t -> t -> t
    val eval : model -> t -> int
  end
  
  module BitVector : sig
    val mk_var : context -> string -> int -> t
    val mk_num : context -> string -> int -> t
    val mk_add : t -> t -> t
    val mk_sub : t -> t -> t
    val mk_mul : t -> t -> t
    val mk_neg : t -> t
    val mk_udiv : t -> t -> t
    val mk_sdiv : t -> t -> t
    val mk_ugt : t -> t -> t
    val mk_sgt : t -> t -> t
    val mk_uge : t -> t -> t
    val mk_sge : t -> t -> t
    val mk_eq : t -> t -> t
    val mk_neq : t -> t -> t
    val mk_and : t -> t -> t
    val mk_or : t -> t -> t
    val mk_xor : t -> t -> t
    val mk_not : t -> t
    val mk_shl : t -> t -> t
    val mk_lshr : t -> t -> t
    val mk_ashr : t -> t -> t
    val eval : model -> t -> string
  end

  val ctx : t -> context
  val mk_context : unit -> context
  val del_context : context -> unit
  val reset : context -> context
  val show : t -> unit
  val dump : context -> unit
  val mk_true : context -> t
  val mk_false : context -> t
  val mk_fresh_bool_var : context -> t
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
  val ite : t -> t -> t -> t
  val (<=>) : t -> t -> t
  val (<!=>) : t -> t -> t
  val apply : context -> string -> t list -> t
  val require : t -> unit
  val assert_weighted : t -> int -> unit
  val push : context -> unit
  val pop : context -> unit
  val check : context -> bool
  val max_sat : context -> bool
  val get_model : context -> model
  val eval : model -> t -> bool
  val get_cost : context -> model -> int
end
