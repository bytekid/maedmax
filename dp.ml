
(*** OPENS *******************************************************************)
open Yices
open Yicesx
open Rewriting

(*** MODULES *****************************************************************)
module C = Cache
module T = Term

(*** TYPES *******************************************************************)
type t_env = { def_vars : (Signature.sym * Yices.expr) list }

(*** GLOBALS *****************************************************************)
let env = ref {def_vars=[]}

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

let init ctx ce =
 let fs = Rules.signature (List.map fst ce) in
 (*let fs' = List.rev_append fs (List.map (fun (f,a) -> f_sharp f,a) fs) in*)
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
  let c = (yimp ctx x_rule (x_def f)) in
  (* assert presence of DPs if X^{rule}_{l-> r} *)
  let var st = C.get_strict_var ctx ((j+1),st) in
  let dps = ybig_and ctx [yimp ctx (x_def g) (var st) | st,g <- cands_rule lr] in
  let c' = yimp ctx x_rule dps in
  yand ctx c c')
 else ynot ctx x_rule
;;

let decode j m =
 Format.printf "DPs:@\n ";
 let is_dp (_, v) = evaluate_in_model m v == True in
 let dps = [ rl | rl <- C.get_all_strict (j+1); is_dp rl ] in
 Listx.print Rule.print "@\n" (List.map fst dps);
 Format.printf "\n%!"
;;
