
  val unify : Term.t -> Term.t -> Subst.t list

  val match_term : Term.t -> Term.t -> Subst.t list

  val test : unit -> unit
  