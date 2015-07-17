type t = RPO 

val yacrpo : 
 Yices.context -> Signature.sym list -> 
 (Signature.sym * Yices.expr) list * (Signature.sym * Yices.expr) list -> 
 Term.t -> Term.t -> Yices.expr

