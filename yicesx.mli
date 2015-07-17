val ytrue : Yices.context -> Yices.expr
val yfalse : Yices.context -> Yices.expr
val yor : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val yimp : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val yiff : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val yand : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val ybig_and : Yices.context -> Yices.expr list -> Yices.expr
val ybig_or : Yices.context -> Yices.expr list -> Yices.expr
val ynot : Yices.context -> Yices.expr -> Yices.expr
val ysum : Yices.context -> Yices.expr list -> Yices.expr
val ygt : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val yge : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val yneq : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val yeq : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val yeval : Yices.model -> Yices.expr -> bool
val yite : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr -> Yices.expr
val ymax : Yices.context -> Yices.expr -> Yices.expr -> Yices.expr
val ymul : Yices.context -> Yices.expr list -> Yices.expr
val yzero : Yices.context -> Yices.expr
val yone : Yices.context -> Yices.expr
