(* 
unify ac_sym t1 t2

computes a complete set of unifiers for t1 and t2
where ac_sym contains the ac-symbols that appear
in t1 and t2 and

matcher ac_sym t1 t2

computes a complete set of matchers for t1 and t2
i.e. phi(t_1) = t2

Resulting substitutions may contain flattened terms
*)

val unify : Signature.sym list -> Term.t * Term.t -> Term.subst list 

val matcher : Signature.sym list -> Term.t * Term.t -> Term.subst list
