type t = Settings.dismatching_constraints

let satisfies1 sigma (ss, ts) =
  not (Subst.are_instances ss [ Term.substitute sigma ti | ti <- ts])
;;

let satisfies sigma = List.for_all (satisfies1 sigma)
