type order = LPO | KBO | Matrix | Cfs | Cfsn | MPol

type orders = Or of order list | Seq of order list

type t_term = Orders of orders | Dp of orders | Dg of orders | DgScc of (int * orders)

type t_constraint = Empty | Red | Comp

type t_max_constraint = MaxEmpty | MaxRed | Oriented | CPsRed | NotOriented |
                        GoalRed

type t_setting = t_term * (t_constraint list) * (t_max_constraint list) * int

type t = t_setting list

val strategy_red : t
val strategy_maxcomp : t
val strategy_maxcomp_lpo : t
val strategy_lpo : t
val strategy_kbo : t
val strategy_mpol : t
val strategy_auto : t
val strategy_auto2 : t
val strategy_cpred : t
val strategy_comp : t
val strategy_dp : t
val strategy_dg : t
val strategy_dgk : t
val strategy_not_oriented : t
val strategy_temp : t
val strategy_ordered : t
val strategy_ordered_lpo : t
val strategy_ordered_kbo : t

val term_to_string : t_term -> string

val get_termination : t -> t_term

val to_string : t -> string

val init : t_term -> int -> Yices.context -> Rules.t -> unit

val assert_constraints : t_term -> int -> Yices.context -> Rules.t -> unit

val bootstrap_constraints : int -> Yices.context -> Rules.t -> Yicesx.t

val decode : int -> Yices.model -> t_term -> unit

val clear : unit -> unit

val cond_gt : t_term -> int -> Yices.context -> (Term.t * Term.t) list -> Term.t 
              -> Term.t -> Yicesx.t
