(* return (axioms, inequality axioms, goals) *)
val file : string -> Literal.t list * Literal.t list
val equation_or_inequality : string -> Literal.t
