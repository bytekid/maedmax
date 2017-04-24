type v = Arith.t list
type m = v list

val zero_v : Yices.context -> int -> v
val zero_m : Yices.context -> int -> m
val unit_m : Yices.context -> int -> m
val add_v  : Yices.context -> v -> v -> v
val sum_v  : Yices.context -> int -> v list -> v 
val mul_vv : Yices.context -> v -> v -> Arith.t
val add_m  : Yices.context -> m -> m -> m
val sum_m  : Yices.context -> int -> m list -> m
val mul_mv : Yices.context -> m -> v -> v
val mul_mm : Yices.context -> m -> m -> m
val gt_v   : Yices.context -> v -> v -> Yices.expr
val geq_v  : Yices.context -> v -> v -> Yices.expr
val geq_m  : Yices.context -> m -> m -> Yices.expr
