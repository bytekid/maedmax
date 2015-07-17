(* string list: contains list of ac smybols *)

val nf : Signature.sym list -> Rules.t -> Term.t -> Term.t

val equal : Signature.sym list -> Term.t -> Term.t -> bool

(* returns R, AC-symbols, AC-rules *)
val find_ac : Rules.t -> ((Rules.t * Signature.sym list * Rules.t * Rules.t) option)

