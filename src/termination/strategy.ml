(*** MODULES *****************************************************************)
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yices
open Yicesx
open Arith
open Settings

(*** TYPES *****************************************************************)
type t = Settings.termination_strategy

(*** GLOBALS *****************************************************************)
(* Caching termination constraints for efficiency: Associates a rule s-> t 
   and a stage j with a constraint c which gives a condition for s > t at 
   strategy stage j. *)
let constraints : (Rule.t * int, Yicesx.t) Hashtbl.t = Hashtbl.create 128

(* caching constraint associated with (pair of) DP candidates *)
let t_dg : (Rule.t * int, Yicesx.t) Hashtbl.t = Hashtbl.create 128
let t_dg2 : (Rule.t * Rule.t * int, Yicesx.t) Hashtbl.t = Hashtbl.create 128
let t_dg_w : (Rule.t * int, Yicesx.t) Hashtbl.t = Hashtbl.create 128

let choice_vars : (int, Yicesx.t) Hashtbl.t = Hashtbl.create 32

let offset = 20

let funs = ref []

(* some predefined strategies *)
(* termination strategies *)
let ts_dp = Dp (Seq [Cfs; Cfs; Cfs; LPO])
let ts_dp5 = Dp (Seq [Cfs; Cfs; Cfs; Cfs; Cfs; LPO])
let ts_dpn = Dp (Seq [Cfsn; LPO])
let ts_dg = Dg (Seq [Cfsn; LPO])
let ts_dgk = DgScc (2, Seq [Cfsn; LPO])
let ts_lpo = Orders (Seq [LPO])
let ts_cfsn = Orders (Seq [Cfsn])
let ts_kbo = Orders (Seq [KBO])
let ts_lpokbo = Orders (Choice (LPO, KBO))
let ts_mpol = Orders (Seq [MPol])

(* overall strategies *)
let max = IterationLimit 10000
let strategy_maxcomp = [ts_dpn, [],[Oriented], max]
let strategy_maxcomp_lpo = [ts_lpo, [],[Oriented], max]
let strategy_maxcomp_kbo = [ts_kbo, [],[Oriented], max]

let strategy_red = [ts_dpn, [Red],[], max]
let strategy_lpo = [ts_lpo, [Red; Comp],[CPsRed], max]
let strategy_kbo = [ts_kbo, [Red; Comp],[CPsRed], max]
let strategy_mpol = [ts_mpol, [Red; Comp],[CPsRed], max]
let strategy_comp = [ts_dpn, [Red; Comp], [], max]
let strategy_cpred = [ts_dpn, [Red], [CPsRed], max]
let strategy_dp = [ts_dpn, [Red; Comp], [CPsRed], max]
let strategy_dg = [ts_dg, [Red; Comp], [CPsRed], max]
let strategy_dgk = [ts_dgk, [Red; Comp], [CPsRed], max]
let strategy_not_oriented = [ ts_dpn, [Red; Comp], [NotOriented], max]
let strategy_all = [(ts_dpn, [Red; Comp], [CPsRed], max);
                    (ts_dp, [Comp], [MaxRed], max)]
let strategy_ordered = [ (ts_kbo, [], [MaxRed], IterationLimit 8);
                         (ts_lpo, [], [MaxRed], IterationLimit 12);
                         (ts_kbo, [], [MaxRed], IterationLimit 41);
                         (ts_kbo, [], [Oriented], IterationLimit 10);
                         (ts_lpo, [], [MaxRed], IterationLimit 50); 
                         (ts_kbo, [], [MaxRed], IterationLimit 70);]
let strategy_ordered_sat = [ (ts_lpo, [], [MaxRed], IterationLimit 11);
                         (ts_kbo, [], [MaxRed], IterationLimit 100);
                         (ts_lpo, [], [MaxRed], IterationLimit 200); ]
let strategy_ordered_lpo = [ts_lpo, [], [MaxRed], max]
let strategy_ordered_kbo = [ts_kbo, [], [MaxRed], max]
let strategy_ordered_lpokbo = [ts_lpokbo, [], [MaxRed], max]
let strategy_aql = [ts_cfsn, [RedSize],[Oriented; CPsRed], max;
                    ts_cfsn, [],[Oriented; CPsRed], max]
let strategy_temp = [ts_cfsn, [Red; Comp],[CPsRed], max]

let strategy_auto = [
 (ts_lpo, [Red; Comp], [CPsRed], max);
 (ts_dpn, [Red; Comp], [CPsRed], max);
 (ts_lpo, [Comp], [MaxRed], max)
]

let strategy_auto2 = [
 (ts_lpo, [Comp], [MaxRed], max);
 (ts_dpn, [Red; Comp], [CPsRed], max);
 (ts_lpo, [Red], [], max)
]


(*** FUNCTIONS ***************************************************************)
let clear _ =
 Hashtbl.clear constraints;
 Hashtbl.clear t_dg;
 Hashtbl.clear t_dg2;
 Hashtbl.clear t_dg_w;
 Lpo.clear ();
 Cfsn.clear ()
;;

let term_to_string = 
 let ostr = function 
  LPO -> "LPO" | KBO -> "KBO" | Matrix -> "matrix" | 
  Cfs -> "cfs" | Cfsn -> "cfsn" | MPol -> "mpol"
 in
 let osstr = function
   Choice (o1,o2) ->
   "Choice (" ^ (ostr o1) ^ ", " ^ (ostr o2) ^ ")"
 | Seq os ->
   Listx.to_string ostr ", " os
 in function
   Orders os -> "Orders (" ^ (osstr os) ^ ")"
 | Dp os -> "Dp (" ^ (osstr os) ^ ")"
 | Dg os -> "Dg (" ^ (osstr os) ^ ")"
 | DgScc (k,os) -> "DgScc ("^(string_of_int k)^", "^ (osstr os) ^ ")"
;;

let c_to_string = function
    Empty -> "None"
  | Red -> "Red"
  | Comp -> "Comp"
  | RedSize -> "RedSize"
;;

let mc_to_string = function 
    MaxEmpty -> "None"
  | MaxRed -> "MaxRed"
  | MinCPs -> "MinCPs"
  | CPsRed -> "CPRed"
  | Oriented -> "Oriented"
  | NotOriented -> "NotOriented"
  | GoalRed -> "GoalRed"
;;

let setting_to_string (t, c, mc, i) =
 let limit =
   match i with
    | IterationLimit i -> string_of_int i ^ " cycles"
    | TimeLimit l -> string_of_float l ^ "s"
 in
 "(" ^ (term_to_string t) ^ ", " ^(Listx.to_string c_to_string ", " c) ^ ", " ^
   (Listx.to_string mc_to_string ", " mc) ^ ", " ^ limit ^")"
;;

let to_string = Listx.to_string setting_to_string ", "

(* abbreviations *)
let index = Listx.index;;

let cache t f k =
 try Hashtbl.find t k 
 with Not_found -> let v = f k in Hashtbl.add t k v; v
;;

(* Asserts initial constraints for stage j and all s -> t in rs, applying a
   case distinction on the strategy s *)
let init s j ctx rs =
 let fs = Rules.signature rs in
 let init_ord ?(af=false) fs i = function
  | LPO -> (if af then Lpo.init_af else Lpo.init) (ctx,i) fs
  | KBO -> Kbo.init (ctx,i) fs
  | Cfs -> Cfs.init (ctx,i) fs
  | Cfsn -> Cfsn.init (ctx,i) fs
  | MPol -> MPol.init (ctx,i) fs
  | _ -> failwith "Strategy.init_ord: not implemented"
 in
 let fs' = Dp.sharp_signature fs in
 let dp_init = Dp.init ctx rs in
 let c =
  match s with
  | Orders (Seq os) -> big_and ctx [init_ord fs i o | i,o <- index ~i:(j+1) os]
  | Orders (Choice (o1, o2)) ->
    Hashtbl.add choice_vars j (Yicesx.mk_fresh_bool_var ctx);
    big_and ctx [init_ord fs (j+1) o | o <- [o1; o2]]
  | Dp (Seq os) -> 
   let init_os = [ init_ord ~af:true fs' i o | i,o <- index ~i:(j+2) os] in
   big_and ctx (dp_init :: init_os)
  | Dg (Seq os) ->
   let init_os = [ init_ord ~af:true fs' i o | i,o <- index ~i:(j+3) os] in
   big_and ctx (dp_init :: init_os)
  | DgScc (k, Seq os) ->
   let ios = [ index ~i:(j+3+offset*i) os | i <- Listx.interval 0 (k-1) ] in
   let init_os = [ init_ord ~af:true fs' i o | i,o <- List.concat ios] in
   big_and ctx (Dg.init_with_sccs ctx fs' (j+1) k :: dp_init :: init_os)
  | _ -> failwith "Strategy.init: not implemented"
 in
 require c
;;

(* abbreviations for strict and weak variables *)
let s ctx i rl = C.get_strict_var ctx (i, rl);;
let w ctx i rl = C.get_weak_var ctx (i, rl);;

(* Asserts a termination constraint for stage j and all s -> t in rs if the
   strategy is of the form Orders (Seq os) *)
let orders_constraints ctx j rs os =
 let gt i (l,r) = function
  | LPO -> Lpo.gt (ctx, i) l r
  | KBO -> Kbo.gt (ctx, i) l r
  | Cfs -> Cfs.gt (ctx, i) l r
  | Cfsn -> Cfsn.gt (ctx, i) l r
  | MPol -> MPol.gt (ctx, i) l r
  | _ -> failwith "orient: not implemented"
 in
 let ge i (l,r) = function
  | LPO -> Lpo.ge (ctx,i) l r
  | KBO -> Kbo.ge (ctx, i) l r
  | Cfs -> Cfs.ge (ctx, i) l r
  | Cfsn -> Cfsn.ge (ctx, i) l r
  | MPol -> MPol.ge (ctx, i) l r
  | _ -> failwith "orient: not implemented"
 in 
 let constr ((l,r) as lr) =
  try Hashtbl.find constraints (lr,j) with Not_found -> (
   let cs i o =  (s ctx (i-1) lr) <=>> ((s ctx i lr) <|> (gt i lr o)) in
   let cs = big_and ctx [ cs i o | i,o <- index ~i:(j+1) os ] in
   let cw i o = (w ctx (i-1) lr) <=>> (ge i lr o) in
   let cw = big_and ctx [ cw i o | i,o <- index ~i:(j+1) os ] in
   let cn = !! (s ctx (List.length os + j) lr) in
   let c = cs <&> cw <&> cn in
   Hashtbl.add constraints (lr,j) c; c)
 in big_and ctx [constr rl | rl <- rs ]
;;

let order_choice_constraints ctx j rs (o1, o2) =
 let gt i (l,r) = function
  | LPO -> Lpo.gt (ctx, i) l r
  | KBO -> Kbo.gt (ctx, i) l r
  | Cfs -> Cfs.gt (ctx, i) l r
  | Cfsn -> Cfsn.gt (ctx, i) l r
  | MPol -> MPol.gt (ctx, i) l r
  | _ -> failwith "orient: not implemented"
 in
 let constr lr =
  try Hashtbl.find constraints (lr,j) with Not_found -> (
   let j' = j+1 in
   let choice = try Hashtbl.find choice_vars j with _ -> failwith "no choice var" in
   let c' = (choice <&> (gt j' lr o1)) <|> (!!choice <&> (gt j' lr o2)) in
   let c = (s ctx j lr) <=>> c' in
   Hashtbl.add constraints (lr,j) c; c)
 in big_and ctx [constr rl | rl <- rs ]
;;

(* Asserts a termination constraint for stage j and all s -> t in rs if the
   strategy is of the form Dp (Seq os) *)
let dp_constraints ?dg:(d=false) ctx j rs os =
 let w, s = w ctx, s ctx in
 let gt i (l,r) = function
  | LPO -> Lpo.gt_af (ctx,i) l r
  | KBO -> Kbo.gt (ctx,i) l r
  | Cfs -> Cfs.gt (ctx, i) l r
  | Cfsn -> Cfsn.gt (ctx, i) l r
  | MPol -> MPol.gt (ctx, i) l r
  | _ -> failwith "orient: not implemented"
 in
 let ge i (l,r) = function
  | LPO -> Lpo.ge_af (ctx,i) l r
  | KBO -> Kbo.ge (ctx,i) l r
  | Cfs -> Cfs.ge (ctx, i) l r
  | Cfsn -> Cfsn.ge (ctx, i) l r
  | MPol -> MPol.ge (ctx, i) l r
  | _ -> failwith "orient: not implemented"
 in
 (* rule removal ... only for polynomial-like thing *)
 let rule_removal i (l,r) = function
  | Cfs -> Cfs.gt (ctx, i) l r
  | Cfsn -> Cfsn.gt (ctx, i) l r
  | _ -> mk_false ctx
 in
 let j' = if d then j+1 else j in (* increase if DG used *)
 let c_rule lr =
  try Hashtbl.find constraints (lr,j) with Not_found -> (
   let keep i o = (w i lr <|> (rule_removal i lr o)) in
   let cw i o = (w (i-1) lr) <=>> (ge i lr o <&> (keep i o)) in
   let cw = big_and ctx [ cw i o | i,o <- index ~i:(j'+2) os ] in
   let cdp = Dp.dp_constraint ctx j lr in
   let dc = if d then (s j lr) <=>> (w j' lr) else mk_true ctx in
   let c = big_and1 [cdp; cw; dc; (s j lr) <=>> (w (j'+1) lr)] in
   Hashtbl.add constraints (lr,j) c; c)
 in 
 let cw = big_and ctx [c_rule lr | lr <- rs ] in
 let c_dp lr =
  try Hashtbl.find constraints (lr,j) with Not_found -> (
   let keep lr i o = ge i lr o <&> (s i lr) in
   let cs i o = (s (i-1) lr) <=>> (keep lr i o <|> (gt i lr o)) in
   let c_w = if not d then mk_true ctx else
    let keep i o = (w i lr <|> (rule_removal i lr o)) in
    let cw i o = (w (i-1) lr) <=>> (ge i lr o <&> (keep i o)) in
    big_and ctx [ cw i o | i,o <- index ~i:(j'+2) os ] 
   in
   let c_str = big_and ctx [ cs i o | i,o <- index ~i:(j'+2) os ] in
   let c_fin = !! (s (List.length os + 1 + j') lr) in
   let c = c_str <&> c_fin <&> c_w in
   Hashtbl.add constraints (lr,j) c; c)
 in big_and1 (cw :: [ c_dp st | st,_ <- Dp.cands_trs rs ])
;;

(* Asserts a termination constraint for stage j and all s -> t in rs if the
   strategy is of the form Dg (Seq os) *)
let dg_constraints ctx j rs os =
 let s = s ctx and w = w ctx in
 let j', j'' = j+1, j+2 in
 let x_w = Dg.x_w ctx j' in
 let dpcands = [st | st,_ <- Dp.cands_trs rs ] in
 let c_dg ((l,r) as p,_) =
  let wf,wg = x_w (Term.root l), x_w (Term.root r) in
  let c_s = (wf <>> wg) <|> (s j' p <=>> (s j'' p)) in
  let c_sw = (s j' p) <=>> (w j'' p) in
  c_s <&> c_sw
 in
 let c_dg p = cache t_dg c_dg (p,j) in
 let c_w rl = 
  let c_w (rl,_) = (w j' rl) <=>> (w j'' rl) in cache t_dg c_w (rl,j)
 in
 let cdg = [ c_dg p | p <- dpcands] in
 let cw = [ c_w rl | rl <- rs ] in
 big_and1 (dp_constraints ctx ~dg:true j rs os :: (cw @ cdg))
;;

(* Asserts a termination constraint for stage j and all s -> t in rs if the 
  strategy is of the form Dp (Seq os) *)
let dp_dg_constraints ?dg:(d=false) ?k:(k=1) ctx j rs os =
 let w, s = w ctx, s ctx in
 let gt i (l,r) = function
  | LPO -> Lpo.gt_af (ctx,i) l r
  | KBO -> Kbo.gt (ctx,i) l r
  | Cfs -> Cfs.gt (ctx, i) l r
  | Cfsn -> Cfsn.gt (ctx, i) l r
  | MPol -> MPol.gt (ctx, i) l r
  | _ -> failwith "orient: not implemented"
 in
 let ge i (l,r) = function
  | LPO -> Lpo.ge_af (ctx,i) l r
  | KBO -> Kbo.ge (ctx,i) l r
  | Cfs -> Cfs.ge (ctx, i) l r
  | Cfsn -> Cfsn.ge (ctx, i) l r
  | MPol -> MPol.ge (ctx, i) l r
  | _ -> failwith "orient: not implemented"
 in
 (* rule removal ... only for polynomial-like thing *)
 let rule_removal i (l,r) = function
  | Cfs -> Cfs.gt (ctx, i) l r
  | Cfsn -> Cfsn.gt (ctx, i) l r
  | _ -> mk_false ctx
 in
 let j' = if d then j+1 else j in (* increase if DG used *)
 let c_rule lr =
  try Hashtbl.find constraints (lr,j) with Not_found -> (
   let keep i o = (w i lr) <|> (rule_removal i lr o) in
   let cw i o = (w (i-1) lr) <=>> ((ge i lr o) <&> (keep i o)) in
   let cw = big_and ctx [ cw i o | i,o <- index ~i:(j'+2) os ] in
   let cdp = Dp.dp_constraint ctx j lr in
   let dc = if d then (s j lr) <=>> (w j' lr) else mk_true ctx in
   let c = big_and ctx [cdp; cw; dc; (s j lr) <=>> (w (j'+1) lr)] in
   Hashtbl.add constraints (lr,j) c; c)
 in
 let cw = big_and ctx [ c_rule lr | lr <- rs ] in
 let init i = j+3 + offset*i in
 let c_dp lr ki =
  try Hashtbl.find constraints (lr,init ki) with Not_found -> (
   let keep lr i o = (ge i lr o) <&> (s i lr) in
   let cs i o = (s (i-1) lr) <=>> ((keep lr i o) <|> (gt i lr o)) in
   let c_w = if not d then mk_true ctx else
    let keep i o = (w i lr) <|> (rule_removal i lr o) in
    let cw i o = (w (i-1) lr) <=>> (ge i lr o <&> (keep i o)) in
    big_and ctx [ cw i o | i,o <- index ~i:(init ki) os ] 
   in
   let c_str = big_and ctx [ cs i o | i,o <- index ~i:(init ki) os ] in
   let c_fin = !! (s (List.length os + (init ki) - 1) lr) in
   let c = c_str <&> c_fin <&> c_w in
   Hashtbl.add constraints (lr,init ki) c; c)
 in
 let dpcands = [st | st,_ <- Dp.cands_trs rs ] in
 let is = Listx.interval 0 (k-1) in
 big_and1 (cw :: [ c_dp st i | st <- dpcands; i <- is ])
;;


let dg_scc_constraints ctx j rs (k,os) =
 (* abbreviations *)
 let s = s ctx and w = w ctx and big_and = big_and ctx in
 let j', j'' = j+1, j+2 in
 let is = Listx.interval 0 (k-1) in
 let x_w = Dg.x_w ctx j' and x_scc = Dg.x_scc ctx j' in
 let num = mk_num ctx in
 (* mappings from rules/DPs to constraints *)
 let c_dg ((l,r) as p) =
  (s j' p) <=>> ((x_scc (Term.root l)) <>=> (x_scc (Term.root r)))
 in
 let c_s_i i ((l,r) as p) =
  let xf,xg = x_scc (Term.root l), x_scc (Term.root r) in
  let wf,wg = x_w (Term.root l), x_w (Term.root r) in
  let both_i = (xf <=> (num i)) <&> (xg <=> (num i)) in
  let strict, weak = wf <>> wg, wf <>=> wg in
  let ks = strict <|> (weak <&> ((s j' p) <=>> (s j'' p))) in
  let kw = s j' p <=>> (w j'' p) in
  both_i <=>> (ks <&> kw)
 in
 let c_w lr = big_and [(w j' lr) <=>> (w j'' lr) | i <- is] in
 (* combined constraint for caching *)
 let c_dg p = 
  let c_dg (p,_) = big_and (c_dg p :: [c_s_i i p | i <- is]) in 
  cache t_dg c_dg (p,j)
 in
 let t_dg = big_and [ c_dg p | p,_ <- Dp.cands_trs rs] in
 let t_w = big_and [c_w lr | lr <- rs] in
 (* combine *)
 big_and1 [dp_dg_constraints ctx ~dg:true ~k:k j rs os; t_w; t_dg]
;;


(* Asserts a termination constraint associated with strategy s at stage j
   for all s -> t in rs (flipped rules not considered, they are supposed to be 
   already mirrored). *)
let assert_constraints s j ctx rs =
 let cs = match s with
   | Orders (Seq os) -> orders_constraints ctx j rs os
   | Orders (Choice (o1, o2)) -> order_choice_constraints ctx j rs (o1,o2)
   | Dp (Seq os) -> dp_constraints ctx j rs os
   | Dg (Seq os) -> dg_constraints ctx j rs os
   | DgScc (k,Seq os) -> dg_scc_constraints ctx j rs (k,os)
   | _ -> failwith "Strategy.assert_constraints: order not implemented"
 in require cs
;;

(* Key function setting constraints to orient rules: rules are oriented
   by making them equivalent to the strict variables of stage j.
   This is the only place where the main rule variables (as returned by
   S.find_rule) are constrained. No mirroring. *)
let bootstrap_constraints j ctx rs =
 big_and ctx [ v <=> (C.get_strict_var ctx (j,rl)) | rl,v <- rs ]
;;

(* Decodes termination argument associated with strategy s using model m,
   and outputs relevant information. Stage j is required for lookups. *)
let decode_print j m s = 
 let dec_ord ?(af=false) (i,o) =
  Format.printf "decode strategy %s\n%!" (term_to_string s);
  match o with
  | LPO -> (if af then Lpo.decode_print_af else Lpo.decode_print) i m
  | KBO -> Kbo.decode_print i m
  | Cfs -> Cfs.decode_print i m
  | Cfsn -> Cfsn.decode_print i m
  | MPol -> MPol.decode_print i m
  | _ -> failwith "Strategy.decode_print: order not implemented"
 in
Format.printf "Problem:\n"; Cache.decode_print m 0;
 match s with
    Orders (Seq os) -> List.iter dec_ord (index ~i:(j+1) os)
  | Orders (Choice (o1,o2)) ->
    let choice = try Hashtbl.find choice_vars j with _ -> failwith "no choice var" in
    if eval m choice then dec_ord (j+1,o1)
    else dec_ord (j+1,o2)
  | Dp (Seq os) ->
   (Dp.decode_print j m;
   Cache.decode_print m 1;
   List.iter (fun (i, o) -> dec_ord ~af:true (i,o); Cache.decode_print m (i+1)) (index ~i:(j+2) os))
  | Dg (Seq os) ->
   (Dp.decode_print j m;
    Cache.decode_print m 1;
    Dg.decode_print (j+1) m;
    Cache.decode_print m 2;
    Cache.decode_print m 3;
    List.iter (fun (i, o) -> dec_ord ~af:true (i,o); Cache.decode_print m (i+1)) (index ~i:(j+3) os))
  | DgScc (k,Seq os) ->
   (Dp.decode_print j m;
    Cache.decode_print m 1;
    Cache.decode_print m 2;
    let ios = [ index ~i:(j+3+offset*i) os | i <- Listx.interval 0 (k-1) ] in
    List.iter  (fun (i, o) -> dec_ord ~af:true (i,o); Cache.decode_print m i) (List.concat ios))
  | _ -> failwith "Strategy.decode_print: not implemented"
;;

let decode j m s = 
 let dec_ord ?(af=false) i = function
  | LPO -> Lpo.decode i m
  | KBO -> Kbo.decode i m
  | Cfs -> Cfs.decode i m
  | Cfsn -> Cfsn.decode i m
  | _ -> failwith "Strategy.decode: order not implemented"
 in
 match s with
    Orders (Seq (o :: _)) -> dec_ord (j+1) o
  | Orders (Choice (o1,o2)) ->
    if eval m (Hashtbl.find choice_vars j) then dec_ord (j+1) o1
    else dec_ord (j+1) o2
  | _ -> failwith "Strategy.decod: not implemented"
;;

let get_termination = function
   (ts, _, _, _) :: _ -> ts
  | _ -> failwith "Strategy.get_termination: empty settings list"
;;

let cond_gt o j c cs s t =
  let ocgt = function
      LPO -> Lpo.cond_gt
    | KBO -> Kbo.cond_gt
    | _ -> failwith "Strategy.cond_gt: not implemented"
  in
  match o with
    | Orders(Seq(o :: _)) -> ocgt o j c cs s t
    | Orders (Choice (o1,o2)) ->
      let choice = Hashtbl.find choice_vars j in
      (choice <&> (ocgt o1 j c cs s t)) <|> (!!choice <&> (ocgt o2 j c cs s t))
    | _ -> failwith "Strategy.cond_gt: not implemented"
;;