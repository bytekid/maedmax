(* $Id: term.mli,v 1.3 2014/09/29 07:37:28 swinkler Exp $ *)

(** Term operations *)

type t = 
  | V of Signature.var
  | F of Signature.sym * t list

type pos = int list

type binding = Signature.var * t

type subst = binding list

val compare : t -> t -> int

val print : Format.formatter -> t -> unit

val variables : t -> Signature.var list

val functions : t -> Signature.sym list

val count_variable : Signature.var -> t -> int

val signature : t -> Signature.t

val subterms : t -> t list

val proper_subterms : t -> t list

val is_variable : t -> bool

val is_subterm : t -> t -> bool

val is_proper_subterm : t -> t -> bool

val root : t -> Signature.sym

val ren : t -> t

val substitute : subst -> t -> t

val rename : t -> t

val rename_canonical : t -> t

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

val similarity : Signature.sym list -> Signature.sym list -> t -> t -> float