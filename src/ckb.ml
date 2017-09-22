(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module L = List
module O = Overlap
module R = Rule
module St = Statistics
module S = Settings
module Ac = Theory.Ac
module Commutativity = Theory.Commutativity
module Lit = Literal
module NS = Nodes

(*** OPENS *******************************************************************)
open Prelude
open Yicesx
open Settings

(*** TYPES *******************************************************************)
type rewrite_steps = (Rule.t * Term.pos * Term.t) list
type result = Completion of Rules.t
  | GroundCompletion of (Rules.t * Rules.t * Order.t)
  | Proof of (Rule.t * (rewrite_steps * rewrite_steps) * Subst.t)
  | Disproof of (Rules.t * Rules.t * Order.t * (rewrite_steps * rewrite_steps))

(*** EXCEPTIONS **************************************************************)
exception Success of result
exception Restart of Lit.t list
exception Fail

(*** GLOBALS *****************************************************************)
let settings = Settings.default

let sizes = ref [] (* to check degeneration *)
let last_time = ref 0.0
let start_time = ref 0.0
let last_mem = ref 0

(* caching for search strategies*)
let redc : (int * int, bool) Hashtbl.t = Hashtbl.create 512;;
let reducible : (int, Yicesx.t) Hashtbl.t = Hashtbl.create 512;;
let rl_index : (Rule.t, int) Hashtbl.t = Hashtbl.create 128;;

(* hash values of states *)
let hash_initial = ref 0;;
let hash_iteration = ref [0];;

(* map equation s=t to list of (rs, s'=t') where rewriting s=t with rs yields
   s'=t' *)
let rewrite_trace : (Rule.t, (Rules.t * Rule.t) list) Hashtbl.t =
  Hashtbl.create 512;;

(* maintain list of created nodes to speed up selection by age *)
let all_nodes = ref []

(*** FUNCTIONS ***************************************************************)
(* shorthands for settings *)
let termination_strategy _ = 
 match !(settings.strategy) with 
  | [] -> failwith "no termination strategy found"
  | (s,_, _,_) :: _ -> s
;;

let constraints _ = 
 match !(settings.strategy) with 
  | [] -> failwith "no constraints found"
  | (_,cs,_,_) :: _ -> cs
;;

let max_constraints _ =
 match !(settings.strategy) with
  | [] -> failwith "no max constraints found"
  | (_,_,ms,_) :: _ -> ms
;;

let strategy_limit _ = 
 match !(settings.strategy) with 
  | [] -> failwith "empty strategy list"
  | (_, _, _, i) :: _ -> i
;;

let use_maxsat _ = max_constraints () <> []

let has_comp () = L.mem S.Comp (constraints ())

let debug _ = !(settings.d) >= 1

let pop_strategy _ = 
 if debug () then F.printf "pop strategy\n%!";
 match !(settings.strategy) with
  | [] -> failwith "no strategy left in pop"
  | [s] -> ()
  | _ :: ss -> settings.strategy := ss
;;

let t_strategies _ = L.map (fun (ts,_,_,_) -> ts) !(settings.strategy)

let normalize = Variant.normalize_rule

let ac_eqs () = [ normalize e | e <- Ac.eqs !(settings.ac_syms) ]

let add_nodes ns = all_nodes := !all_nodes @ ns 

let get_oldest_node _ =
  match !all_nodes with
     [] -> failwith "Cache.get_oldest_node: no nodes there"
   | n :: ns -> all_nodes := ns; n 
;;

(* * REWRITING * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let add_rewrite_trace st rls st' =
  if has_comp () then
    begin
    let rdcts = try Hashtbl.find rewrite_trace st with Not_found -> [] in
    Hashtbl.replace rewrite_trace st ((rls, st') :: rdcts)
    end
;;

(* normalization of cs with TRS with index n. Returns pair (cs',ff) where ff
   are newly generated eqs and cs' \subseteq cs is set of irreducible eqs *)
let rewrite rewriter (cs : NS.t) =
 let rewrite n (irrdcbl, news) =
   match Lit.rewriter_nf_with n rewriter with
    | None -> (NS.add n irrdcbl, news) (* no progress here *)
    (* n' is leftover of n (only relevant with constraints *)
    | Some (nnews, rs) -> ((* if terms got equal, nnew is empty *)
        if nnews <> [] then
          add_rewrite_trace (Lit.terms n) rs (Lit.terms (L.hd nnews));
        irrdcbl, NS.add_list nnews news)
 in NS.fold rewrite cs (NS.empty (), NS.empty ())
;;  
   
let rewrite rr = St.take_time St.t_rewrite (rewrite rr)

let reduced rr ns =
  let (irred, news) = rewrite rr ns in NS.add_all news irred
;;

let interreduce rr =
 let rew = new Rewriter.rewriter rr [] Order.default in
 let right_reduce (l,r) =
   let r', rs = rew#nf r in
   if r <> r' then (
     if !(Settings.do_proof) then
       Trace.add_rewrite (normalize (l,r')) (l,r) ([],rs);
     add_rewrite_trace (l,r) (L.map fst rs) (l,r'));
   (l,r')
  in
  let rr_hat = Listx.unique ((L.map right_reduce) rr) in
  [ l,r | l,r <- rr_hat; not (Rewriting.reducible_with (Listx.remove (l,r) rr_hat) l) ]
;;

(* * SELECTION * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let log_select cc ss =
  let plist = Formatx.print_list (fun f n -> Lit.print f n) "\n " in
  F.printf "select %i from %i:\n%a\n%!" (L.length ss) (NS.size cc) plist ss
;;


let select_count i = !(settings.n)

let keep acs n =
  let fs = Rule.functions (Lit.terms n) in
  L.length fs > 1 || not (Listset.subset fs acs) ||
  L.mem (Lit.terms n) (ac_eqs ()) || not (Lit.is_ac_equivalent n acs)
;;

let rec select size_sorted acc n =
  if n <= 0 then L.rev acc
  else
    if Random.int 100 < !(settings.size_age_ratio) then
      match size_sorted with
          [] -> L.rev acc
        | b::bs -> select bs (b::acc) (n-1)
    else if !all_nodes = [] then acc
    else
      let b = get_oldest_node () in
      select size_sorted (b::acc) (n-1)
;;

(* selection of small new nodes *)
let select' ?(only_size=true) k cc thresh =
 let k = if k = 0 then select_count !(St.iterations) else k in
 let acs = !(settings.ac_syms) in
 let small = NS.smaller_than thresh cc in
 let aa = 
   if only_size then
     let aa,_ = L.partition (keep acs) small in
     let aa = NS.sort_size aa in
     fst (Listx.split_at_most k aa)
   else
     let small,_ = L.partition (keep acs) small in
     let size_sorted = NS.sort_size small in
     Random.self_init();
     select size_sorted [] k
 in
 let pp = NS.diff_list cc aa in 
 if debug () then log_select cc aa;
 (* remember smallest terms for divergence estimate, 20 is heuristic value *)
 let m = L.fold_left (fun m n -> min m (R.size (Lit.terms n))) 20 aa in
 sizes := m :: !sizes;
 (aa,pp)
;;

let axs _ = [ Lit.make_axiom e | e <- !(settings.es) ]

let select_for_restart cc =
  let k = !(St.restarts) * 2 in
  fst (select' k (NS.diff_list cc (axs ())) 30)

let select cc =
  let thresh = !(settings.size_bound_equations) in
  St.take_time St.t_select (select' ~only_size:false 0 cc) thresh
;;

let select_goals' k gg thresh =
 let acs = !(settings.ac_syms) in
 let small,_ = L.partition (keep acs) (NS.smaller_than thresh gg) in
 let t = Unix.gettimeofday () in
 let sorted = NS.sort_size_unif small in
 St.t_tmp1 := !St.t_tmp1 +. (Unix.gettimeofday () -. t);
 let gg_a = fst (Listx.split_at_most k sorted) in
 let gg_p = NS.diff_list gg gg_a in 
 if debug () then log_select gg gg_a;
 (gg_a, gg_p)
;;

let select_goals k cc =
  St.take_time St.t_select (select_goals' k cc) !(settings.size_bound_goals)
;;

(* * CRITICAL PAIRS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let eqs_for_overlaps ee =
  let ee' = NS.filter Lit.not_increasing (NS.symmetric ee) in
  NS.variant_free ee'
;;

let cp_cache : (Lit.t * Lit.t, Lit.t list) Hashtbl.t = Hashtbl.create 256

let cps rew n1 n2 =
  if !(settings.pcp) > 0 then Lit.pcps rew n1 n2
  else (
    try Hashtbl.find cp_cache (n1,n2)
    with Not_found -> (
      let cps = Lit.cps n1 n2 in
      Hashtbl.add cp_cache (n1,n2) cps;
    cps))
;;

(* get overlaps for rules rr and active nodes cc *)
let overlaps rew rr aa =
 let ns =
   if not !(settings.unfailing) then rr
   else 
     let t = Unix.gettimeofday () in
     let aa' = NS.ac_equivalence_free !(settings.ac_syms) aa in
     let rr' = NS.ac_equivalence_free !(settings.ac_syms) rr in
     let aa' = NS.c_equivalence_free !(settings.only_c_syms) aa' in
     let rr' = NS.c_equivalence_free !(settings.only_c_syms) rr' in
     St.t_tmp2 := !St.t_tmp2 +. (Unix.gettimeofday () -. t);
     rr' @ aa'
 in
 NS.of_list [ n | n1 <- ns; n2 <- ns; n <- cps rew n1 n2 ]
;;

let overlaps rew rr = St.take_time St.t_overlap (overlaps rew rr)

(* goal only as outer rule *)
let overlaps_on rew rr aa gs =
 let ns = rr @ aa in
 let gs_for_ols = NS.to_list (eqs_for_overlaps gs) in
  NS.of_list [ n | r <- ns; g <- gs_for_ols; n <- cps rew r g ]
;;

(* * SUCCESS CHECKS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let saturated ctx (rr,ee) rewriter cc =
  let ee' = Rules.subsumption_free ee in
  let str = termination_strategy () in
  let d = !(settings.d) in
  let sys = rr,ee',!(settings.ac_syms),!(settings.signature),rewriter#order in
  let xsig = !(settings.extended_signature) in
  (*let ns = if !(settings.unfailing) then rr @ ee else rr in
  let cc' = !(settings.es) @ [ n | n1 <- ns; n2 <- ns; n <- cps n1 n2 ] in*)
  let eqs = [ normalize (Lit.terms n) | n <- NS.to_list cc; Lit.is_equality n ] in
  Ground.all_joinable ctx str sys eqs xsig d
;;

let rewrite_seq rew (s,t) (rss,rst) =
  let rec seq u = function
     [] -> []
   | (rl,p) :: rs ->
     let v = rew#rewrite_at_with u rl p in (rl,p,v) :: (seq v rs)
  in
  seq s rss, seq t rst
;;


let succeeds ctx (rr,ee) rewriter cc gs =
  rewriter#add_more ee;
  let joinable (s,t) = fst (rewriter#nf s) = fst (rewriter#nf t) in
  let fixed g =
    let u,v = Lit.terms g in joinable (u,v) || Subst.unifiable u v
  in
  let sat = saturated ctx (rr,ee) rewriter cc in
  let order = match sat with None -> rewriter#order | Some o -> o in
  if not (NS.is_empty gs) && NS.exists fixed gs then (
    let g = L.find fixed (NS.to_list gs) in
    let s,t = Lit.terms g in
    let (_, rss), (_,rst) = rewriter#nf s, rewriter#nf t in
    if debug () then (
      let str = if joinable (s,t) then "joinable" else "unifiable" in
      F.printf "%s %a\n%!" str (fun f g -> Lit.print f g) g;
      F.printf "rules: {%a} \n{%a}\n" Rules.print [r | r,_ <- rss] Rules.print [r | r,_ <- rst]);
    if joinable (s,t) then
      Some (Proof ((s,t),rewrite_seq rewriter (s,t) (rss,rst),[]))
    else
      (* unifiable *)
      let s',t' = Rule.substitute (Subst.mgu s t) (s,t) in
      Some (Proof ((s,t),rewrite_seq rewriter (s',t') ([],[]),Subst.mgu s t)))
  else if rr @ ee = [] || (sat <> None &&
          (L.for_all (fun g -> Lit.is_ground g) (NS.to_list gs))) then (
    if !(settings.unfailing) && !(Settings.inequalities) = [] then
      Some (GroundCompletion (rr, ee, order))
    else if !(settings.unfailing) then
      let ieqs = !(Settings.inequalities) in
      if L.exists joinable ieqs then
        Some (Proof (L.find joinable ieqs,([],[]),[])) (* UNSAT *)
      else Some (GroundCompletion (rr, ee, order)) (* SAT *)
    else Some (Completion rr)
  ) else None
;;

let succeeds ctx re rew cc =
  St.take_time St.t_success_check (succeeds ctx re rew cc)
;;

(* * FIND TRSS  * * *  * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* logical vars for new TRSs *)
let store_trss ctx =
  let store n _ =
    if not (Hashtbl.mem C.ht_trsvars n) then
      let rr = L.map C.find_rule (C.trs_of_index n) in
      if rr <> [] then (
        let v = mk_fresh_bool_var ctx in
        Hashtbl.add C.ht_trsvars n v;
        require (v <=> (big_and1 rr))
      )
 in Hashtbl.iter store C.ht_itrss
;;

let c_maxcomp ctx cc =
 let oriented (l,r) = C.find_rule (l,r) <|> (C.find_rule (r,l)) in
 L.iter (fun n -> assert_weighted (oriented (Lit.terms n)) 1) cc
;;

let c_not_oriented ctx cc =
 let exp (l,r) = (!! (C.find_rule (l,r))) <&> (!! (C.find_rule (r,l))) in
 L.iter (fun n -> assert_weighted (exp (Lit.terms n)) 1) cc
;;

let idx r = 
  try Hashtbl.find rl_index r
  with Not_found -> 
    let i = Hashtbl.length rl_index in Hashtbl.add rl_index r i; i
;;

(* cc is already symmetric *)
let is_reducible ctx cc (s,t) =
  let j = idx (s,t) in
  try Hashtbl.find reducible j with Not_found -> (
    let reduces_st rl = (
      let red = Rewriting.reducible_with [rl] in
      Rule.is_rule rl && (red t || red s))
    in
    let rs = [ C.find_rule (Lit.terms n) | n <- cc; reduces_st (Lit.terms n) ] in
    let b = big_or ctx rs in
    Hashtbl.add reducible j b;
    b
  )
;;

let rlred ctx cc (s,t) =
  let ccs = L.fold_left (fun ccs n -> Lit.flip n :: ccs) cc cc in
  let j = idx (s,t) in
  let redcbl rl =
    let i = idx rl in (
    let red = Rewriting.reducible_with [rl] in
    let is_rule (l,r) = Rule.is_rule (l,r) && (not (Term.is_subterm l r)) in
    let b = is_rule rl && (red t || red s) in
    Hashtbl.add redc (j, i) b; b)
  in big_or ctx [ C.find_rule (Lit.terms n) | n <- ccs; redcbl (Lit.terms n) ]
;;

let c_red ctx cc =
  L.iter (fun n -> require (rlred ctx cc (Lit.terms n))) cc
;;

let c_red ctx = St.take_time St.t_cred (c_red ctx)

let c_cpred ctx cc =
  Hashtbl.clear reducible;
  let ccsymm = L.fold_left (fun ccs n -> Lit.flip n :: ccs) cc cc in
  let rs = [ Lit.terms n | n <- ccsymm; Rule.is_rule (Lit.terms n) ] in
  let rule, red = C.find_rule, is_reducible ctx ccsymm in
  let c2 = [ rule rl <&> (rule rl') <=>> (red st) | rl <- rs; rl' <- rs;
                                             st <- O.nontrivial_cps rl rl' ] in
  L.iter (fun c -> ignore (assert_weighted c 2)) c2;
;;

let c_cpred ctx = St.take_time St.t_ccpred (c_cpred ctx)

let c_max_red ctx cc =
  L.iter (fun n -> assert_weighted (rlred ctx cc (Lit.terms n)) 1) cc
;;


let c_max_goal_red ctx cc gs =
  NS.iter (fun g -> assert_weighted (rlred ctx cc (Lit.terms g)) 1) gs
;;

let c_comp ctx ns =
 let rule_var, weight_var = C.find_rule, C.find_eq_weight in
 let all_eqs ee = big_and ctx (L.map C.find_eq ee) in
 (* induce order: decrease from e to equations in ee *)
 let dec e ee = big_and ctx [ weight_var e <>> (weight_var e') | e' <- ee] in
 (* encode reducibility of equation st *)
 let red st =
  let es = try Hashtbl.find rewrite_trace st with Not_found -> [] in
  big_or ctx [ C.find_eq e <&> all_eqs ee <&> dec e ee | (ee,e) <- es ] 
 in
 let considered ((s,t) as st) =
   require (C.find_eq st <=>> (big_or1 [rule_var st; rule_var (t,s); red st]));
 in
 (* initial equations have to be considered *)
 require (all_eqs !(settings.es));
 L.iter considered [ Lit.terms n | n <- ns; not (Lit.is_trivial n) ];
;;

let c_comp ctx = St.take_time St.t_ccomp (c_comp ctx)

(* constraints to guide search; those get all retracted *)
let search_constraints ctx cc gs =
 let ccl = NS.to_list cc in
 let assert_c = function
   | S.Red -> c_red ctx ccl
   | S.Empty -> ()
   | S.Comp -> c_comp ctx ccl
 in L.iter assert_c (constraints ());
 let assert_mc = function
   | S.Oriented -> c_maxcomp ctx ccl
   | S.NotOriented -> c_not_oriented ctx ccl
   | S.MaxRed -> c_max_red ctx ccl
   | S.GoalRed -> c_max_goal_red ctx ccl gs
   | S.CPsRed -> c_cpred ctx ccl
   | S.MaxEmpty -> ()
 in L.iter assert_mc (max_constraints ())
;;

(* find k maximal TRSs *)
let max_k ctx cc gs =
  let k = !(settings.k) !(St.iterations) in
  let cc_symm = NS.to_list (NS.symmetric cc) in 
  if debug () then F.printf "K = %i\n%!" k;
  let s = termination_strategy () in
  let rec max_k acc ctx cc n =
    if n = 0 then L.rev acc (* return TRSs in sequence of generation *)
    else (
      let sat_call = if use_maxsat () then max_sat else check in
      if St.take_time St.t_sat sat_call ctx then (
        let m = get_model ctx in
        let c = if use_maxsat () then get_cost m else 0 in
        let is_rl n = eval m (C.find_rule n) && not (Rule.is_dp n) in
        let rr = [ n | n <- cc_symm; is_rl (Lit.terms n) ] in
        let order =
          if !(settings.unfailing) then Strategy.decode 0 m s
          else Order.default
        in
        if !(settings.unfailing) && !Settings.do_assertions then (
          let ord n = let l,r = Lit.terms n in order#gt l r && not (order#gt r l) in
          assert (L.for_all ord rr));
        require (!! (big_and ctx [ C.find_rule (Lit.terms r) | r <- rr ]));
        max_k ((rr, c, order) :: acc) ctx cc (n-1))
     else (
       if debug () then F.printf "no further TRS found\n%!"; 
       if (n = k && L.length !(settings.strategy) > 1) then
         raise (Restart (select_for_restart cc));
       acc))
   in
   let cc_symm = [ Lit.terms c | c <- cc_symm ] in 
   L.iter (fun n -> ignore (C.store_rule_var ctx n)) cc_symm;
   if has_comp () then
     NS.iter (fun n -> ignore (C.store_eq_var ctx (Lit.terms n))) cc;
   (* FIXME: restrict to actual rules?! *)
   St.take_time St.t_orient_constr (Strategy.assert_constraints s 0 ctx)cc_symm;
   push ctx; (* backtrack point for Yices *)
   require (Strategy.bootstrap_constraints 0 ctx cc_symm);
   search_constraints ctx cc gs;
   let trss = max_k [] ctx cc k in
   pop ctx; (* backtrack: get rid of all assertions added since push *)
   trss
;;

let max_k ctx cc = St.take_time St.t_maxk (max_k ctx cc)

(* some logging functions *)
let log_iteration i aa =
 F.printf "Iteration %i\n%!" i;
 F.printf "CC: %i\n%a%!" (NS.size aa) NS.print aa;
 F.printf "\n%!"
;;

let log_max_trs j rr rr' c =
 F.printf "TRS %i - %i (cost %i):\n %a\nreduced:%!\n %a\n@." !St.iterations j c
   Rules.print (Variant.rename_rules rr)
   Rules.print (Variant.rename_rules rr')
;;


(* towards main control loop *)
(* Heuristic to determine whether the state is stuck in that no progress was
   made in the last n iterations. *)
let do_restart es gs =
 (* no progress measure *)
 let h = Hashtbl.hash (NS.size es, es, gs) in
 let rep = L.for_all ((=) h) !hash_iteration in
 hash_iteration := h :: !hash_iteration;
 hash_iteration := Listx.take_at_most 20 !hash_iteration;
 if rep && debug () then F.printf "Restart: repeated iteration state\n%!";
 (* iteration/size bound*)
 let running_time = (Unix.gettimeofday () -. !(start_time)) in
 let limit =
   match strategy_limit () with
    | IterationLimit i when !(St.iterations) > i -> true
    | TimeLimit l when running_time > l -> true
    | _ -> false
 in
 (* estimate exponential blowup *)
 let blow n m = float_of_int n >= 1.5 *. (float_of_int m) in
 let rec is_exp = function n::m::cs -> blow n m && is_exp (m::cs) | _ -> true in
 let eqcounts = Listx.take_at_most 6 !(Statistics.eq_counts) in
 let blowup = !(St.iterations) > 6 && is_exp eqcounts in
 if blowup && debug () then F.printf "Blowup!\n%!";
 if limit && debug () then F.printf "Restart: limit reached\n";
 rep || limit || blowup
;;

let set_iteration_stats aa gs =
  let i = !St.iterations in
  St.iterations := i + 1;
  St.ces := NS.size aa;
  St.goals := NS.size gs;
  let mem_diff = St.memory () - !last_mem in
  let time_diff = Unix.gettimeofday () -. !last_time in
  last_mem := St.memory ();
  last_time := Unix.gettimeofday ();
  St.time_diffs := time_diff :: !(St.time_diffs);
  St.mem_diffs := mem_diff :: !(St.mem_diffs);
  St.eq_counts := NS.size aa :: !(St.eq_counts);
  if debug () then (
   F.printf "Start iteration %i with %i equations:\n %a\n%!"
     !St.iterations (NS.size aa) NS.print aa;
   if !St.goals > 0 then
     let gnd = Rules.is_ground [ Lit.terms g | g <- NS.to_list gs ] in
     F.printf "\nand %i goals:\n%a %i%!\n" !St.goals NS.print gs
       (if gnd then 1 else 0);
   let json = St.json () in
   F.printf "%s\n%!" (Yojson.Basic.pretty_to_string json))
;;

let store_trs ctx j rr c =
  let rr_index = C.store_trs rr in
  (* for rewriting actually reduced TRS is used; have to store *)
  let rr_reduced =
    if !(Settings.do_proof) then interreduce rr else Variant.reduce_encomp rr
  in
  C.store_redtrs rr_reduced rr_index;
  C.store_rule_vars ctx rr_reduced; (* otherwise problems in norm *)
  if has_comp () then C.store_eq_vars ctx rr_reduced;
  if debug () then log_max_trs j rr rr_reduced c;
  rr_index
;;

let non_gjoinable ctx ns rr = NS.subsumption_free ns

let non_gjoinable ctx ns = St.take_time St.t_gjoin_check (non_gjoinable ctx ns)

let rec phi ctx aa gs =
  if do_restart aa gs then
    raise (Restart (select_for_restart aa));
  set_iteration_stats aa gs;
  let aa =
    if !(settings.check_subsumption) == 2 && !St.iterations mod 3 == 0 then
      NS.subsumption_free aa
    else aa
  in
  let process (j, aa, gs) (rr, c, order) =
    let trs_n = store_trs ctx j [ Lit.terms r | r <- rr ] c in
    let rr_red = C.redtrs_of_index trs_n in
    let rew = new Rewriter.rewriter rr_red !(settings.ac_syms) order in
    rew#init ();
    let irred, red = rewrite rew aa in (* rewrite eqs wrt new TRS *)
    let gs = NS.add_all (reduced rew gs) gs in
    let irred = NS.filter Lit.not_increasing (NS.symmetric irred) in
    let irred' =
      if !(settings.check_subsumption) == 1 then NS.subsumption_free irred
      else irred
    in
    let aa_for_ols = NS.to_list (eqs_for_overlaps irred') in
    let cps = reduced rew (overlaps rew rr aa_for_ols) in (* rewrite CPs *)
    let nn = NS.diff (NS.add_all cps red) aa in (* only new ones *)
    let sel, rest = select nn in
    (* FIXME where to move this variable registration stuff? *)
    if has_comp () then
      NS.iter (fun n -> ignore (C.store_eq_var ctx (Lit.terms n))) rest;
    let gcps = reduced rew (overlaps_on rew rr aa_for_ols gs) in (* goal CPs *)
    let gg = fst (select_goals 2 (NS.diff gcps gs)) in
    let rr,ee = [ Lit.terms r | r <- rr], [ Lit.terms e | e <- NS.to_list irred ] in
    add_nodes (NS.sort_size (NS.smaller_than 100 rest));
    match succeeds ctx (rr, ee) rew (NS.add_list (axs ()) cps) gs with
       Some r -> raise (Success r)
     | None ->
       (j+1, NS.add_list sel aa, NS.add_list gg gs)
  in
  try
    let rrs = max_k ctx aa gs in
    let s = Unix.gettimeofday () in
    let _, aa', gs' = L.fold_left process (0, aa, gs) rrs in
    St.t_process := !(St.t_process) +. (Unix.gettimeofday () -. s);
    phi ctx aa' gs'
  with Success r -> r
;;


let detect_shape es gs =
  let shape = St.problem_shape es gs in
  let fs_count = List.length (Rules.signature es) in
  match shape with
    | Piombo
    | Xeno
    | Zolfo -> settings.n := 10
    | Elio when fs_count > 3 -> settings.n := 10
    | Silicio ->
      settings.n := 10;
      settings.size_age_ratio := 85;
      settings.strategy := Strategy.strategy_ordered_lpo
    | Ossigeno -> settings.n := 12
    | Carbonio
    | None -> settings.n := 6
    | Elio -> settings.n := 6;
  if debug () then
    Format.printf "shape: %s%!" (Settings.shape_to_string shape)
;;

let init_settings fs es gs =
 settings.ac_syms := Ac.symbols es;
 let cs = Commutativity.symbols es in
 settings.only_c_syms := Listset.diff cs !(settings.ac_syms);
 if !(settings.only_c_syms) <> [] then
   Format.printf "only C symbols: %s\n%!"
     (List.fold_left (fun s f -> s ^ " " ^ (Signature.get_fun_name f)) ""
      !(settings.only_c_syms));
 settings.signature := Rules.signature (es @ gs);
 settings.d := !(fs.d);
 St.iterations := 0;
 settings.n := !(fs.n);
 settings.strategy := !(fs.strategy);
 settings.tmp := !(fs.tmp);
 settings.es := es;
 settings.gs := gs;
 start_time := Unix.gettimeofday ();
 last_time := Unix.gettimeofday ();
 last_mem := St.memory ();
 Settings.is_ordered := !(settings.unfailing);
 if !(Settings.do_proof) then
   Trace.add_initials es;
 if debug () then
   F.printf "AC syms: %s \n%!"
     (L.fold_left (fun s f -> Signature.get_fun_name f ^ " " ^ s) ""
     (Ac.symbols es));
 if !(fs.tmp) > 0 then detect_shape es gs
;;

let remember_state es gs =
 let h = Hashtbl.hash (termination_strategy (), es,gs) in
 if h = !hash_initial then raise Fail;
 hash_initial := h
;;

(* main ckb function *)
let rec ckb fs (es, gs) =
  (* TODO check positive/negative goals??? *)
 let eq_ok e = Lit.is_equality e || Lit.is_ground e in
 if not (L.for_all eq_ok es) then raise Fail
 else
 let gs  : Lit.t list = 
   if L.length gs <= 1 then gs
   else
     let gs = [ Lit.terms g | g <- gs ] in
     let g = Term.F(-1, L.map fst gs), Term.F(-1, L.map snd gs) in 
     [ Lit.make_goal g ]
 in
 (*if gs = [] then settings.strategy := Strategy.strategy_ordered_sat;*)
 (* store initial state to capture*)
 remember_state es gs;
 (* init state *)
 let ctx = mk_context () in
 let es0 = L.map Lit.normalize es in
 let gs0 = L.map Lit.normalize gs in
 all_nodes := es0;
 try
  init_settings fs [ Lit.terms e | e <- es0] [ Lit.terms g | g <- gs0 ];
  let cas = [ Ac.cassociativity f | f <- !(settings.ac_syms)] in
  let es0 = [ Lit.make_axiom (Variant.normalize_rule rl) | rl <- cas ] @ es0 in
  let ctx = mk_context () in
  let ns0 = NS.of_list es0 in
  let ss = Listx.unique (t_strategies ()) in
  L.iter (fun s -> Strategy.init s 0 ctx [ Lit.terms n | n <- gs0@es0 ]) ss;
  (if !(settings.keep_orientation) then
    let es = [ Variant.normalize_rule_dir (Lit.terms e) | e <- es ] in
    let es' = [ if d then e else R.flip e | e,d <- es ] in
    require (big_and ctx [ !! (C.rule_var ctx (R.flip r)) | r <- es' ]);
    List.iter (fun r -> assert_weighted (C.rule_var ctx r) 27) es'
    );
  let res = phi ctx ns0 (NS.of_list gs0) in
  del_context ctx;
  res
 with Restart es_new -> (
  if debug () then Format.printf "restart\n%!";
  pop_strategy ();
  Strategy.clear ();
  Cache.clear ();
  St.restarts := !St.restarts + 1;
  Hashtbl.reset rewrite_trace;
  del_context ctx;
  Hashtbl.reset cp_cache;
  sizes := [];
  St.mem_diffs := [];
  St.time_diffs := [];
  St.eq_counts := [];
  ckb fs ((if gs = [] then es0 else es_new @ es0), gs))
