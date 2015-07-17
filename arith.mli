(** Arithmetic contraints based on Yices bitvectors. *)

type t = int * Yices.expr
(* (k, bv) means k-bits vector bv. *)

val int : Yices.context -> int -> t
val add : Yices.context -> t -> t -> t
val sum : Yices.context -> t list -> t
val mul : Yices.context -> t -> t -> t
val geq : Yices.context -> t -> t -> Yices.expr
val gt  : Yices.context -> t -> t -> Yices.expr


val conj : Yices.context -> Yices.expr list -> Yices.expr
val disj : Yices.context -> Yices.expr list -> Yices.expr
val xor  : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
