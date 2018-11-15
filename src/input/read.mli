(* return (axioms, inequality axioms, goals) *)
val file : string -> Settings.input
val equation_or_inequality : string -> Literal.t
