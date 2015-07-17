val lpo : Yices.context -> Rules.t -> (Rule.t * Yices.expr) list

val mpo : Yices.context -> Rules.t -> (Rule.t * Yices.expr) list

val kbo : Yices.context -> Rules.t -> (Rule.t * Yices.expr) list

val max : 
  order:(Yices.context -> Rules.t -> (Rule.t * Yices.expr) list) -> 
  int -> Rules.t -> Rules.t list
