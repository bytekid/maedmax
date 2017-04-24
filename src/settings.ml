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

type t_constraint = Empty | Red | Comp
type t_max_constraint = MaxEmpty | MaxRed | Oriented | CPsRed | NotOriented |
                        GoalRed
type limit = IterationLimit of int | TimeLimit of float
type t_setting = t_term * (t_constraint list) * (t_max_constraint list) * limit
type termination_strategy = t_setting list

type t = {
 ac_syms  : Signature.sym list ref; (* only relevant for ordered completion *)
 signature: (Signature.sym * int) list ref;
 d        : bool ref ; (* debug mode *)
 es       : Rules.t ref ;
 json     : bool ref; (* output json result and statistics *)
 k        : (int -> int) ref;  (* k TRSs are chosen in an iteration *)
 n        : int ref;  (* how many equations are (at most) selected *)
 unfailing : bool ref;
 strategy : termination_strategy ref;
 tmp      : int ref; (* various purpose parameter *)
 output_tproof : bool ref;
 check_subsumption : bool ref;
 extended_signature: bool ref
}

(*** GLOBALS *****************************************************************)
(* k functions *)
let k_default = fun i -> if i < 3 then 6 else 2
let k2 _ = 2

let tmp = ref false

(* settings *)
let default = {
 ac_syms   = ref [];
 signature = ref [];
 d         = ref false;
 es        = ref [] ;
 json      = ref false;
 k         = ref k_default;
 n         = ref 10;
 unfailing = ref false;
 strategy  = ref [];
 tmp       = ref 19;
 output_tproof = ref false;
 check_subsumption = ref false;
 extended_signature = ref false
}

let do_assertions = ref false
let do_debug = ref false
let do_proof = ref false
let do_proof_debug = ref false
let is_ordered = ref false

let inequalities : Rules.t ref = ref []
let inst_depth : int ref = ref 2
