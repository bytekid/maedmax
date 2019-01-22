(*** MODULES *****************************************************************)
module Logic = Order.Logic

(*** TYPES *******************************************************************)
exception Backtrack 
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

let ts_lpo = Orders (Seq [LPO])
let ts_kbo = Orders (Seq [KBO])

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
  | Idrogeno
  | Magnesio
  | Silicio
  | Ossigeno
  | Piombo
  | Xeno
  | Zolfo
  | NoShape

type literal = { terms: Rule.t; is_equality: bool }

type clause = literal list

type input =
  | Unit of literal list * literal list
  | NonUnit of literal list list * literal list list

type proof_format = CPF | TPTP | SelectionTrace | TraceForInstgen


type state_features = {
  equations: int;
  goals: int;
  iterations: int;
}

type equation_features = {
  is_goal_selection: bool;
  size: int;
  size_diff: int;
  linear: bool;
  age: float; (* (max age - node age) / max age *)
  orientable: bool * bool;
  duplicating: bool * bool;
  matches: float; (* normalized by number of nodes *)
  cps: float (* normalized by number of nodes *)
}

type selection_features = literal * equation_features * state_features

type selection_mode =
  | MixedSelect
  | AgeSelect
  | RandomSelect
  | SizeSelect
  | ClassifiedMixed

type classifier =
  ?bound:float -> equation_features -> state_features ->
  (float array * float array) -> bool

type t = {
  auto : bool; (* automatic mode *)
  ac_syms : Signature.sym list; (* only relevant for ordered completion *)
  only_c_syms : Signature.sym list; (* only relevant for ordered completion *)
  signature : (Signature.sym * int) list;
  debug : int; (* debug level *)
  axioms : literal list;
  instgen : bool;
  json : bool; (* output json result and statistics *)
  gs : Rules.t; (* initial goals *)
  unfailing : bool;
  tmp : int; (* various purpose parameter *)
  output_tproof : bool;
  extended_signature: bool;
  keep_orientation: bool;
  selection: selection_mode;
  select_classify: classifier option;
  complete_if_no_goal : bool;
  switch_to_okb : bool
}

type mode = OnlySAT | OnlyUNSAT | SATorUNSAT

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
  restart_carry : int * int; (* (c, d) * #restarts * c + d equations selected *)
  size_age_ratio: int;
  soft_bound_equations: int;
  soft_bound_goals: int;
  reduce_AC_equations_for_CPs: bool;
  full_CPs_with_axioms : bool;
  prune_AC : bool;
  no_similar_select: bool;
  mode : mode
}

type rewrite_steps = (Rule.t * Term.pos * Subst.t * Term.t) list

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
  instgen = false;
  json = false;
  gs = [];
  unfailing = false;
  tmp = 0;
  output_tproof = false;
  extended_signature = false;
  keep_orientation = false;
  selection = MixedSelect;
  select_classify = None;
  complete_if_no_goal = true;
  switch_to_okb = false
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
  restart_carry = (2, 0);
  size_age_ratio = 100;
  soft_bound_equations = 200;
  soft_bound_goals = 30;
  reduce_AC_equations_for_CPs = false;
  full_CPs_with_axioms = false;
  prune_AC = true;
  no_similar_select = false;
  mode = SATorUNSAT
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
let tmp = ref 0.0
let fixed_shape = ref ""

let shape_to_string = function
  | Boro -> "boro"
  | Calcio -> "calcio"
  | Carbonio -> "carbonio"
  | Elio -> "elio"
  | Idrogeno -> "idrogeno"
  | Magnesio -> "magnesio"
  | Silicio -> "silicio"
  | Ossigeno -> "ossigeno"
  | Piombo -> "piombo"
  | Xeno -> "xeno"
  | Zolfo -> "zolfo"
  | NoShape -> "none"
;;

let do_proof_debug () = !do_debug && !do_proof <> None

let h_piombo h = { h with
  hard_bound_equations = 4000;
  hard_bound_goals = 200;
  n = 10;
  strategy = [ts_lpo, [], [MaxRed], IterationLimit 10000, Size]
}

let h_zolfo h = { h with
  n = 10;
  restart_carry = (2, 0)
}

let h_xeno0 h = { h with
  n = 10;
  n_goals = 1;
  reduce_AC_equations_for_CPs = true;
  hard_bound_equations = 90;
  hard_bound_goals = 120;
  size_age_ratio = 60;
  soft_bound_equations = 70;
  soft_bound_goals = 100;
  restart_carry = (2, 0);
}

let h_xeno1 h = { h_xeno0 h with
  no_similar_select = true
}

let h_elio h = { h with
  n = 10;
  hard_bound_equations = 45;
  hard_bound_goals = 45;
  soft_bound_equations = 30;
  soft_bound_goals = 30;
  restart_carry = (2, 2)
}

let h_silicio h = { h with
  n = 10;
  n_goals = 1;
  size_age_ratio = 80;
  strategy = [ts_lpo, [], [MaxRed], IterationLimit 10000, Size];
  hard_bound_equations = 45;
  hard_bound_goals = 45;
  soft_bound_equations = 30;
  soft_bound_goals = 30
}

let h_ossigeno h = { h with
  n = 12;
  size_age_ratio = 80;
  hard_bound_equations = 45;
  hard_bound_goals = 45;
  soft_bound_equations = 30;
  soft_bound_goals = 30;
  restart_carry = (2, 2)
}

let h_carbonio h = { h with
  full_CPs_with_axioms = true;
  hard_bound_equations = 360;
  hard_bound_goals = 270;
  n = 10;
  n_goals = 3;
  size_age_ratio = 60;
  soft_bound_equations = 40;
  soft_bound_goals = 100;
}

let h_calcio h = { h with n = 6 }

let h_magnesio h = { h with
  n = 6;
  hard_bound_equations = 40;
  hard_bound_goals = 45;
  soft_bound_equations = 25;
  soft_bound_goals = 37
}

let h_no_shape1 h = { h with
  n = 6;
  hard_bound_equations = 60;
  hard_bound_goals = 90;
  soft_bound_equations = 40;
  soft_bound_goals = 70;
  restart_carry = (3, 0)
}

let h_no_shape0 h = { h_no_shape1 h with
  restart_carry = (2, 2)
}

let h_idrogeno h = { h with
  hard_bound_equations = 65;
  n = 6;
  soft_bound_equations = 45;
  strategy = [ts_lpo, [], [MaxRed], IterationLimit 10000, Size]
}

let h_boro h = { h with
  hard_bound_equations = 20;
  hard_bound_goals = 20;
  n = 14;
  size_age_ratio = 70;
  soft_bound_equations = 16;
  strategy = [ts_kbo, [], [MaxRed], IterationLimit 10000, Size]
}
