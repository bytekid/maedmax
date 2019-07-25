(* $Id: term.mli,v 1.3 2014/09/29 07:37:28 swinkler Exp $ *)

module Var : Map.OrderedType
module Sub : sig
  type key = Signature.var
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val map : ('a -> 'b) -> 'a t -> 'b t
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end
(** Term operations *)

type t = 
  | V of Signature.var
  | F of Signature.sym * t list

type pos = int list

type binding = Signature.var * t

type subst = t Sub.t

val compare : t -> t -> int

val print : Format.formatter -> t -> unit

val variables : t -> Signature.var list

val functions : t -> Signature.sym list

val args : t -> t list

val count_variable : Signature.var -> t -> int

val signature : t -> Signature.t

val subterms : t -> t list

val proper_subterms : t -> t list

val is_variable : t -> bool

val is_subterm : t -> t -> bool

val is_proper_subterm : t -> t -> bool

val root : t -> Signature.sym

val substitute : subst -> t -> t

val substitute_uniform : t -> t -> t

val substitute_bot : t -> t

val positions : t -> int list list

val variable_positions : t -> int list list

val function_positions : t -> int list list

val function_positions_below_root : t -> int list list

val subterm_at : int list -> t -> t

val replace : t -> t -> int list -> t

val direct_subterms : t -> t list

val count_variables : t -> Signature.var -> int

val linear : t -> bool

val flatten : Signature.sym list -> t -> t

val args_sort : Signature.sym list -> t -> t

val unflatten : Signature.sym list -> t -> t

val size :  t -> int

val depth :  t -> int

val is_sharped : t -> bool

val is_embedded : t -> t -> bool

val to_xml : t -> Xml.xml

val to_tptp : t -> string

val to_string : t -> string

val similarity : Signature.sym list -> Signature.sym list -> t -> t -> float