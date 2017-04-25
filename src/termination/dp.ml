
(*** OPENS *******************************************************************)
open Yicesx
open Rewriting

(*** MODULES *****************************************************************)
module C = Cache
module T = Term

(*** TYPES *******************************************************************)
type t_env = { def_vars : (Signature.sym * Yicesx.t) list }

(*** GLOBALS *****************************************************************)
let env = ref { def_vars=[] }

(*** FUNCTIONS ***************************************************************)
let x_def f = List.assoc f !env.def_vars

(* sharp term *)
let f_sharp f = Signature.sharp_fun f

let sharp = function
  | T.V _ -> failwith "sharp: not a functional term"
  | T.F (f, ts) -> T.F (f_sharp f, ts)

(* compute dp candidates of rule/TRS *)
let cands_rule (l,r) =
 [ (sharp l, sharp u), T.root u | 
   u <- T.subterms r; not (T.is_variable l) && 
   not (T.is_variable u) && not (T.is_subterm u l)]
;;

let cands_trs trs = [ st | lr <- trs; st <- cands_rule lr]

let sharp_signature fs = fs @ [f_sharp f,a | ( f,a) <- fs]

let init ctx rs =
 let fs = Rules.signature rs in
 let fresh () = mk_fresh_bool_var ctx in
 env := { def_vars =  [ f, fresh () | f,_ <- fs ] };
 mk_true ctx
;;

let dp_constraint ctx j ((l,r) as lr) =
 let x_rule = C.get_strict_var ctx (j,lr) in
 if Rule.is_rule lr && not (T.is_subterm l r) 
 then (
  (* assert X^{rule}_{l-> r} => X^{def}_{root l} *)
  let f = T.root (fst lr) in
  let c = x_rule <=>> (x_def f) in
  (* assert presence of DPs if X^{rule}_{l-> r} *)
  let var st = C.get_strict_var ctx ((j+1),st) in
  let dps = big_and ctx [x_def g <=>> (var st) | st,g <- cands_rule lr] in
  c <&> (x_rule <=>> dps))
 else !! x_rule
;;

let decode_print j m =
 Format.printf "DPs:@\n ";
 let dps = [ dp | (dp,v) <- C.get_all_strict (j+1); eval m v ] in
 Listx.print Rule.print "@\n" dps;
 Format.printf "\n%!"
;;
