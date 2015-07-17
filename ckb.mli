type flags = {
 d   : bool ref ; 
 es : Constraint.t list ref;
 json: bool ref;
 k   : (int -> int) ref; 
 n  : int ref; 
 ordered_completion : bool ref;
 strategy : Strategy.t ref;
 tmp : int ref;
 output_tproof : bool ref;
 check_subsumption : bool ref
}

val offset: int 

val flags: flags

val debug: bool ref 

val ckb : flags -> Rules.t -> (Rules.t * Rules.t)

val check_termination : flags -> Rules.t -> bool
