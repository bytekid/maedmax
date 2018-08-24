type t = Rule.t list

val print : Format.formatter -> t -> unit

val print_with : string -> Format.formatter -> t -> unit

val variables : t -> Signature.var list

val functions : t -> Signature.sym list

val signature : t -> Signature.t

val defined_symbols : t -> Signature.sym list

val is_non_duplicating : t -> bool

val is_ground : t -> bool

val variable_condition : t -> bool

val is_constructor_system : t -> bool

val linear : t -> bool

val left_linear : t -> bool

val right_linear : t -> bool

val remove : t -> t -> t

val flatten : Signature.sym list -> t -> t

val rules_over : t -> t

val rpl_spcl_char : t -> t

val is_srs : t -> bool

val to_xml : t -> Xml.xml

val subsumption_free : t -> t

val flip : t -> t
