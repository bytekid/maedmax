(*** TYPES *******************************************************************)
type t = {
 ac_syms  : Signature.sym list ref; (* only relevant for ordered completion *)
 d        : bool ref ; (* debug mode *)
 es       : Rules.t ref ;
 json     : bool ref; (* output json result and statistics *)
 k        : (int -> int) ref;  (* k TRSs are chosen in an iteration *)
 n        : int ref;  (* how many equations are (at most) selected *)
 unfailing : bool ref;
 strategy : Strategy.t ref;
 tmp      : int ref; (* various purpose parameter *)
 output_tproof : bool ref;
 check_subsumption : bool ref;
}

(*** GLOBALS *****************************************************************)
(* k functions *)
let k_default = fun i -> if i < 3 then 6 else 2
let k2 _ = 2

(* settings *)
let default = {
 ac_syms   = ref [];
 d         = ref false;
 es        = ref [] ;
 json      = ref false;
 k         = ref k_default;
 n         = ref 10;
 unfailing = ref false;
 strategy  = ref Strategy.strategy_red;
 tmp       = ref 19;
 output_tproof = ref false;
 check_subsumption = ref false
}

let do_assertions = ref false
let do_debug = ref false
let is_ordered = ref false