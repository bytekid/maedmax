(*** MODULES *****************************************************************)
module Logic = Order.Logic

(*** TYPES *******************************************************************)
(* Type for reduction order *)
type order =
  | LPO
  | KBO
  | Matrix
  | Cfs
  | Cfsn
  | MPol

(* Constructors connecting different reduction orders *)
type orders = Choice of (order * order) | Seq of order list

type t_term = 
  | Orders of orders (* plain reduction orders *)
  | Dp of orders (* dependency pairs followed by orders *)
  | Dg of orders (* dependency graph without SCCs *)
  | DgScc of (int * orders) (* dependency graph with k SCCs *)
 
type selection =
  | Size
  | SizeAge of int

type t_constraint =
  | Empty
  | Red
  | Comp
  | RedSize

type t_max_constraint =
  | MaxEmpty
  | MaxRed
  | Oriented
  | CPsRed
  | NotOriented
  | GoalRed
  | MinCPs

type limit =
  | IterationLimit of int
  | TimeLimit of float

type t_setting =
  t_term * (t_constraint list) * (t_max_constraint list) * limit * selection

type termination_strategy = t_setting list

(* heuristically detected problem class *)
type shape =
  | Boro
  | Calcio
  | Carbonio
  | Elio
  | Magnesio
  | Silicio
  | Ossigeno
  | Piombo
  | Xeno
  | Zolfo
  | NoShape

type literal = { terms: Rule.t; is_goal: bool; is_equality: bool }

type proof_format = CPF | TPTP

type t = {
  auto : bool; (* automatic mode *)
  ac_syms : Signature.sym list; (* only relevant for ordered completion *)
  only_c_syms : Signature.sym list; (* only relevant for ordered completion *)
  signature : (Signature.sym * int) list;
  debug : int; (* debug level *)
  axioms : literal list;
  json : bool; (* output json result and statistics *)
  gs : Rules.t; (* initial goals *)
  unfailing : bool;
  tmp : int; (* various purpose parameter *)
  output_tproof : bool;
  extended_signature: bool;
  keep_orientation: bool;
  trace_selection: bool
}

type heuristic = {
  hard_bound_equations: int;
  hard_bound_goals: int;
  k : int -> int;  (* k TRSs are chosen in an iteration *)
  n : int;  (* how many equations are (at most) selected *)
  n_goals : int;  (* how many equations are (at most) selected *)
  strategy : termination_strategy;
  check_subsumption : int; (* degree of subsumption check, in {0,1,2} *)
  max_oriented : int;
  pcp : int; (* use critical pair criterion *)
  reduce_trss : bool; (* interreduce TRSs *)
  restart_carry : int; (* restart_carry * #restarts: equations carried over *)
  size_age_ratio: int;
  soft_bound_equations: int;
  soft_bound_goals: int;
  reduce_AC_equations_for_CPs: bool;
  full_CPs_with_axioms : bool
}

type rewrite_steps = (Rule.t * Term.pos * Term.t) list

type proof =
  | Completion of Rules.t
  | GroundCompletion of (Rules.t * Rules.t * Order.t)
  | Proof of (Rule.t * (rewrite_steps * rewrite_steps) * Subst.t)
  | Disproof of (Rules.t * Rules.t * Order.t * (rewrite_steps * rewrite_steps))

type answer =
  | SAT
  | UNSAT

type result = answer * proof


(*** GLOBALS *****************************************************************)
(* k functions *)
let k_default = fun i -> if i < 3 then 6 else 2
let k2 _ = 2

(* default settings *)
let default = {
  auto = true;
  ac_syms = [];
  only_c_syms = [];
  signature = [];
  debug = 0;
  axioms = [];
  json = false;
  gs = [];
  unfailing = false;
  tmp = 0;
  output_tproof = false;
  extended_signature = false;
  keep_orientation = false;
  trace_selection = false
}

(* default settings *)
let default_heuristic = {
  hard_bound_equations = 2500;
  hard_bound_goals = 200;
  k = k_default;
  n = 10;
  n_goals = 2;
  max_oriented = 1000;
  strategy = [];
  check_subsumption = 1;
  pcp = 0;
  reduce_trss = true;
  restart_carry = 3;
  size_age_ratio = 100;
  soft_bound_equations = 200;
  soft_bound_goals = 30;
  reduce_AC_equations_for_CPs = false;
  full_CPs_with_axioms = false
}

let do_assertions = ref false
let do_debug = ref false
let do_proof : proof_format option ref = ref None
let interactive = ref false
let generate_order = ref false
let inst_depth : int ref = ref 2
let input_file = ref ""
let generate_benchmarks = ref false
let track_equations : literal list ref = ref []
let benchmark = ref false
let tmp = ref 0
let fixed_shape = ref ""

let shape_to_string = function
  | Boro -> "boro"
  | Calcio -> "calcio"
  | Carbonio -> "carbonio"
  | Elio -> "elio"
  | Magnesio -> "magnesio"
  | Silicio -> "silicio"
  | Ossigeno -> "ossigeno"
  | Piombo -> "piombo"
  | Xeno -> "xeno"
  | Zolfo -> "zolfo"
  | NoShape -> "none"
;;

let do_proof_debug () = !do_debug && (!do_proof <> None)
