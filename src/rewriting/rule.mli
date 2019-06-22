type t = Term.t * Term.t

val print : Format.formatter -> t -> unit

val print_with : string -> Format.formatter -> t -> unit

val to_string : t -> string

val equal : t -> t -> bool

val hash : t -> int

val compare : t -> t -> int

val variables : t -> Signature.var list

val functions : t -> Signature.sym list

val signature : t -> Signature.t

val is_non_erasing : t -> bool

val is_duplicating : t -> bool

val is_non_duplicating : t -> bool

val linear : t -> bool

val left_linear : t -> bool

val right_linear : t -> bool

val variable_condition : t -> bool

val renaming_for : t -> Term.subst 

val rename : t -> t

val rename_canonical : ?from:int -> t -> t

val flip : t -> t

val variant : t -> t -> bool

val equation_variant : t -> t -> bool

val is_instance : t -> t -> bool

val is_proper_instance : t -> t -> bool

val instantiate_to : t -> t -> Subst.t

val remove : t list -> t -> t list

val is_rule : t -> bool

val is_ground : t -> bool

val size : t -> int

val is_dp : t -> bool

val substitute : Term.subst -> t -> t

val to_xml : t -> Xml.xml

val to_tptp : t -> string
