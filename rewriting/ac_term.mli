type t = int list * int list

val funs_pos : Signature.sym list -> Term.t -> t list

val subterm_at : Term.t -> t -> Term.t

val replace : Term.t -> Term.t -> t -> Term.t 
