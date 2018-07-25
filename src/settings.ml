(*** TYPES *******************************************************************)
(* Type for reduction order *)
type order = LPO | KBO | Matrix | Cfs | Cfsn | MPol
(* Constructors connecting different reduction orders *)
type orders = Choice of (order * order) | Seq of order list

type t_term = 
   Orders of orders (* plain reduction orders *)
 | Dp of orders (* dependency pairs followed by orders *)
 | Dg of orders (* dependency graph without SCCs *)
 | DgScc of (int * orders) (* dependency graph with k SCCs *)
 
 type selection = Size | SizeAge of int

type t_constraint = Empty | Red | Comp | RedSize
type t_max_constraint = MaxEmpty | MaxRed | Oriented | CPsRed | NotOriented |
                        GoalRed | MinCPs
type limit = IterationLimit of int | TimeLimit of float
type t_setting =
  t_term * (t_constraint list) * (t_max_constraint list) * limit * selection
type termination_strategy = t_setting list

(* heuristically detected problem shape *)
type shape = NoShape | Boro | Calcio | Carbonio | Elio | Silicio | Ossigeno |
            Piombo | Xeno | Zolfo


type literal = { terms: Rule.t; is_goal: bool; is_equality: bool }

type t = {
 auto     : bool ref; (* automatic mode *)
 ac_syms  : Signature.sym list ref; (* only relevant for ordered completion *)
 only_c_syms  : Signature.sym list ref; (* only relevant for ordered completion *)
 signature: (Signature.sym * int) list ref;
 d        : int ref ; (* debug mode *)
 axioms   : literal list ref ;
 json     : bool ref; (* output json result and statistics *)
 gs       : Rules.t ref ;
 k        : (int -> int) ref;  (* k TRSs are chosen in an iteration *)
 large    : bool ref;
 n        : int ref;  (* how many equations are (at most) selected *)
 max_oriented : int ref;
 unfailing : bool ref;
 strategy : termination_strategy ref;
 tmp      : int ref; (* various purpose parameter *)
 output_tproof : bool ref;
 check_subsumption : int ref;
 pcp : int ref;
 extended_signature: bool ref;
 keep_orientation: bool ref;
 reduce_trss : bool ref;
 size_age_ratio: int ref;
 size_bound_equations: int ref;
 size_bound_goals: int ref;
 reduce_AC_equations_for_CPs: bool ref;
 full_CPs_with_axioms : bool ref
}

type rewrite_steps = (Rule.t * Term.pos * Term.t) list
type proof = Completion of Rules.t
| GroundCompletion of (Rules.t * Rules.t * Order.t)
| Proof of (Rule.t * (rewrite_steps * rewrite_steps) * Subst.t)
| Disproof of (Rules.t * Rules.t * Order.t * (rewrite_steps * rewrite_steps))

type answer = SAT | UNSAT
type result = answer * proof


(*** GLOBALS *****************************************************************)
(* k functions *)
let k_default = fun i -> if i < 4 then 4 else 2
let k2 _ = 2

let tmp = ref false

(* settings *)
let default = {
 auto      = ref true;
 ac_syms   = ref [];
 only_c_syms   = ref [];
 signature = ref [];
 d         = ref 0;
 axioms    = ref [] ;
 json      = ref false;
 gs        = ref [] ;
 k         = ref k_default;
 large     = ref false;
 n         = ref 10;
 max_oriented = ref 1000;
 unfailing = ref false;
 strategy  = ref [];
 tmp       = ref 0;
 output_tproof = ref false;
 check_subsumption = ref 1;
 pcp = ref 0;
 extended_signature = ref false;
 keep_orientation = ref false;
 reduce_trss = ref true;
 size_age_ratio = ref 100;
 size_bound_equations = ref 200;
 size_bound_goals = ref 30;
 reduce_AC_equations_for_CPs = ref false;
 full_CPs_with_axioms = ref false
}

let do_assertions = ref false
let do_debug = ref false
let do_proof = ref false
let do_proof_debug = ref false
let is_ordered = ref false
let interactive = ref false
let generate_order = ref false
let inst_depth : int ref = ref 2
let max_eq_size : int ref = ref 2500
let max_goal_size : int ref = ref 100
let input_file = ref ""
let generate_benchmarks = ref false

let shape_to_string = function
    NoShape -> "none"
  | Boro -> "boro"
  | Calcio -> "calcio"
  | Carbonio -> "carbonio"
  | Elio -> "elio"
  | Silicio -> "silicio"
  | Ossigeno -> "ossigeno"
  | Piombo -> "piombo"
  | Xeno -> "xeno"
  | Zolfo -> "zolfo"
;;
