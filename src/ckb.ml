(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module L = List
module O = Overlap
module R = Rule
module A = Analytics
module S = Settings
module St = Strategy
module Ac = Theory.Ac
module Commutativity = Theory.Commutativity
module Lit = Literal
module NS = Nodes
module Logic = Settings.Logic

(*** OPENS *******************************************************************)
open Prelude
open Settings

(*** EXCEPTIONS **************************************************************)
exception Success of result
exception Restart of Lit.t list
exception Fail

(*** GLOBALS *****************************************************************)
let settings = ref Settings.default
let heuristic = ref Settings.default_heuristic

(* caching for search strategies*)
let redc : (int * int, bool) Hashtbl.t = Hashtbl.create 512;;
let reducible : (int, Logic.t) Hashtbl.t = Hashtbl.create 512;;
let rl_index : (Rule.t, int) Hashtbl.t = Hashtbl.create 128;;

(* hash values of states *)
let hash_initial = ref 0;;
let hash_iteration = ref [0];;

(* map equation s=t to list of (rs, s'=t') where rewriting s=t with rs yields
   s'=t' *)
let rewrite_trace : (Rule.t, (Rules.t * Rule.t) list) Hashtbl.t =
  Hashtbl.create 512

let acx_rules = ref []

let incomplete = ref false

(*** FUNCTIONS ***************************************************************)
(* shorthands for settings *)
let termination_strategy _ = 
  match !heuristic.strategy with 
  | [] -> failwith "no termination strategy found"
  | (s, _, _, _, _) :: _ -> s
;;

let dps_used _ = St.has_dps (termination_strategy ())

let constraints _ =
  match !heuristic.strategy with
  | [] -> failwith "no constraints found"
  | (_, cs, _, _, _) :: _ -> cs
;;

let max_constraints _ =
 match !heuristic.strategy with
  | [] -> failwith "no max constraints found"
  | (_, _, ms, _, _) :: _ -> ms
;;

let strategy_limit _ =
 match !heuristic.strategy with
  | [] -> failwith "empty strategy list"
  | (_, _, _, i, _) :: _ -> i
;;

let selection_mode _ =
 match !heuristic.strategy with
  | [] -> failwith "empty strategy list"
  | (_, _, _, _, s) :: _ -> s
;;

let use_maxsat _ = max_constraints () <> []

let has_comp () = L.mem S.Comp (constraints ())

let debug d = !settings.debug >= d

let check_subsumption n = !heuristic.check_subsumption >= n

let nth_iteration n = !A.iterations mod n == 0

let pop_strategy _ = 
 if debug 2 then F.printf "pop strategy\n%!";
 match !heuristic.strategy with
  | [] -> failwith "no strategy left in pop"
  | [s] -> ()
  | _ :: ss -> heuristic := { !heuristic with strategy = ss }
;;

let t_strategies _ = L.map (fun (ts,_,_,_,_) -> ts) !heuristic.strategy 

let normalize = Variant.normalize_rule

let ac_eqs () = [ normalize e | e <- Ac.eqs !settings.ac_syms ]

(* TODO: there might be inequalities *)
let axs _ = !settings.axioms

let store_remaining_nodes ctx ns =
  if has_comp () then
    NS.iter (fun n -> ignore (C.store_eq_var ctx (Lit.terms n))) ns;
  let ns = NS.smaller_than !heuristic.soft_bound_equations ns in
  let tt = Unix.gettimeofday () in
  let ns' = [n | n <- ns; not (NS.mem Select.all_nodes_set n)] in 
  A.t_tmp1 := !A.t_tmp1 +. (Unix.gettimeofday () -. tt);
  (*Format.printf "store %d (%d new), in total %d\n%!"
    (List.length ns) (List.length ns') (NS.size all_nodes_set);*)
  let ns_sized = [n, Lit.size n | n <- NS.sort_size ns' ] in
  Select.all_nodes := L.rev_append (L.rev !Select.all_nodes) ns_sized;
  ignore (NS.add_list ns' Select.all_nodes_set)
;;

let store_remaining_goals ctx ns =
  let ns = NS.smaller_than !heuristic.soft_bound_goals ns in
  let ns_sized = [n, Lit.size n | n <- NS.sort_size ns] in
  Select.all_goals := L.rev_append (L.rev !Select.all_goals) ns_sized
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
let rewrite ?(max_size=0) rewriter (cs : NS.t) =
  let t = Unix.gettimeofday () in
  (* skip exponential rewrite sequences with unfortunate orders *)
  let nf n =
    try Lit.rewriter_nf_with ~max_size:max_size n rewriter
    with Rewriter.Max_term_size_exceeded ->
      incomplete := true;
      None
  in
  let rewrite n (irrdcbl, news) =
    match nf n with
      | None -> (NS.add n irrdcbl, news) (* no progress here *)
      | Some (nnews, rs) -> ((* if terms got equal, nnew is empty *)
          if !(Settings.do_proof) <> None && nnews <> [] then
            add_rewrite_trace (Lit.terms n) rs (Lit.terms (L.hd nnews));
          irrdcbl, NS.add_list nnews news)
  in
  let res = NS.fold rewrite cs (NS.empty (), NS.empty ()) in
  A.t_rewrite := !A.t_rewrite +. (Unix.gettimeofday () -. t);
  res
;;

let reduced ?(max_size=0) rr ns =
  let (irred, news) = rewrite ~max_size:max_size rr ns in NS.add_all news irred
;;

let interreduce rr =
 let rew = new Rewriter.rewriter !heuristic rr [] Order.default in
 let right_reduce (l,r) =
   let r', rs = rew#nf r in
   if r <> r' then (
     if !(Settings.do_proof) <> None then
       Trace.add_rewrite (normalize (l,r')) (l, r) ([],rs);
     add_rewrite_trace (l, r) (L.map fst rs) (l, r'));
   (l,r')
  in
  let rr' = Listx.unique ((L.map right_reduce) rr) in
  let reducible rl = Rewriting.reducible_with (Listx.remove rl rr') (fst rl) in
  [ rl | rl <- rr'; not (reducible rl)]
;;

(* * CRITICAL PAIRS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let eqs_for_overlaps ee =
  let ee' = NS.filter Lit.not_increasing (NS.symmetric ee) in
  NS.variant_free ee'
;;

let cp_cache : (Lit.t * Lit.t, Lit.t list) Hashtbl.t = Hashtbl.create 256

let cps rew n1 n2 =
  if !heuristic.pcp > 0 then Lit.pcps rew n1 n2
  else (
    try Hashtbl.find cp_cache (n1,n2)
    with Not_found -> (
      let cps = Lit.cps !heuristic n1 n2 in
      if debug 2 && L.length cps > 0 then
        Format.printf "CPs between %a and %a: %a\n%!" Lit.print n1 Lit.print n2
          NS.print_list cps;
      Hashtbl.add cp_cache (n1,n2) cps;
      cps))
;;

(* get overlaps for rules rr and equations aa *)
let overlaps rr aa =
 let ns =
   if not !settings.unfailing then rr
   else
     let acs, cs = !settings.ac_syms, !settings.only_c_syms in
     let aa' = (*if List.length aa < 10 then aa else*) Listset.diff aa !acx_rules in
     let aa' = NS.ac_equivalence_free acs aa' in
     let rr' = NS.ac_equivalence_free acs rr in
     let aa' = NS.c_equivalence_free cs aa' in
     let is_large_state = A.last_cp_count () < 1000 in
     let rr' = if is_large_state then rr' else NS.c_equivalence_free cs rr' in
     rr' @ aa'
 in
 (* only proper overlaps with rules*)
 let ovl = new Overlapper.overlapper !heuristic ns in
 ovl#init ();
 let cpl = [cp | n <- ns; cp <- ovl#cps n] in
 let cps = NS.of_list cpl in
 cps, ovl
;;

let overlaps rr = A.take_time A.t_overlap (overlaps rr)

(* Goal only as outer rule, compute CPs with equations.
   Use rr only if the goals are not ground (otherwise, goals with rr are
   covered by rewriting). *)
let overlaps_on rr aa _ gs =
  let gs_for_ols = NS.to_list (eqs_for_overlaps gs) in
  let goals_ground = List.for_all Rule.is_ground !settings.gs in
  let acs, cs = !settings.ac_syms, !settings.only_c_syms in
  let ns = if goals_ground then aa else rr @ aa in
  let ns' = NS.ac_equivalence_free acs (Listset.diff ns !acx_rules) in
  let ns' = NS.c_equivalence_free cs ns' in
  let ovl = new Overlapper.overlapper !heuristic [eq | eq <- ns'] in
  ovl#init ();
  let cps2 = NS.of_list [cp | g <- gs_for_ols; cp <- ovl#cps g] in
  cps2
;;

(* * SUCCESS CHECKS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let saturated ctx (rr, ee) rewriter (axs, cps, cps') =
  let ee' = Rules.subsumption_free ee in
  let str = termination_strategy () in
  let sys = rr, ee', rewriter#order in
  let cc = axs @ (NS.to_list cps @ (NS.to_list cps')) in
  let eqs = [ Lit.terms n | n <- cc; Lit.is_equality n ] in
  let eqs' = L.filter (fun e -> not (L.mem e rr)) eqs in
  Ground.all_joinable !settings ctx str sys eqs'
;;

let rewrite_seq rew (s,t) (rss,rst) =
  let rec seq u = function
     [] -> []
   | (rl,p) :: rs ->
     let v = rew#rewrite_at_with u rl p in (rl,p,v) :: (seq v rs)
  in
  seq s rss, seq t rst
;;

let solved_goal rewriter gs =
  let try_to_solve g =
    try
      let s,t = Lit.terms g in
      let s',rss = rewriter#nf s in
      let t',rst = rewriter#nf t in
      if s' = t' then Some ((s,t), rewrite_seq rewriter (s,t) (rss,rst), [])
      else if Subst.unifiable s t then Some ((s,t), ([],[]), Subst.mgu s t)
      else None
    with Rewriter.Max_term_size_exceeded -> None
  in
  let r = NS.fold (fun g -> function None -> try_to_solve g | r -> r) gs None in
  r
;;

let succeeds ctx (rr,ee) rewriter cc ieqs gs =
  let rr = [ Lit.terms r | r <- rr] in
  let ee = [ Lit.terms e | e <- NS.to_list ee; Lit.is_equality e] in
  rewriter#add_more ee;
  match solved_goal rewriter gs with
    | Some (st, rseq,sigma) -> Some (UNSAT, Proof (st, rseq, sigma))
    | None -> (
      let joinable (s,t) =
        try fst (rewriter#nf s) = fst (rewriter#nf t)
        with Rewriter.Max_term_size_exceeded -> false  
      in
      if L.exists joinable ieqs then (* joinable inequality axiom *)
        Some (UNSAT, Proof (L.find joinable ieqs,([],[]),[]))
      else if List.length ee > 40 then
        None (* saturation too expensive, or goals have been discarded *)
      else match saturated ctx (rr,ee) rewriter cc with
        | None when rr @ ee = [] && not !incomplete -> Some (SAT, Completion [])
        | Some order ->
          let gs_ground = L.for_all Lit.is_ground (NS.to_list gs) in
          let ee_nonground = L.for_all (fun e -> not (Rule.is_ground e)) ee in
          let orientable (s,t) = order#gt s t || order#gt t s in
          (* if an equation is orientable, wait one iteration ... *)
          let ee_sym = ee @ [s, t| t, s <- ee ] in
          if not gs_ground && L.for_all (fun e -> not (orientable e)) ee &&
            !(Settings.do_proof) = None then (* no narrowing proof output yet *)
            Narrow.decide_goals !settings rr ee_sym order !incomplete
          else if not (rr @ ee = [] || gs_ground) then None
          else (
            if ee = [] && not !incomplete then Some (SAT, Completion rr)
            else if ieqs = [] && ee_nonground && not !incomplete then
              Some (SAT, GroundCompletion (rr, ee, order))
            else if L.length ieqs = 1 && NS.is_empty gs &&
              !(Settings.do_proof) = None then
              Narrow.decide !settings rr ee_sym order ieqs !incomplete
            else None
          )
        | _ -> None
    )
;;

let succeeds ctx re rew cc ie =
  A.take_time A.t_success_check (succeeds ctx re rew cc ie)
;;

(* * FIND TRSS  * * *  * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let (<|>) = Logic.(<|>)
let (<&>) = Logic.(<&>)
let (!!) = Logic.(!!)
let (<=>>) = Logic.(<=>>)
let (<>>) = Logic.(<>>)

let c_maxcomp ctx cc =
 let oriented ((l,r),v) = v <|> (C.find_rule (r,l)) in
 L.iter (fun ((l,r),v) ->
   if l > r then Logic.assert_weighted (oriented ((l,r),v)) 1) cc
;;

let c_not_oriented ctx cc =
 let exp (l,r) = (!! (C.find_rule (l,r))) <&> (!! (C.find_rule (r,l))) in
 L.iter (fun rl -> Logic.assert_weighted (exp rl) 1) cc
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
    let b = Logic.big_or ctx rs in
    Hashtbl.add reducible j b;
    b
  )
;;

let rlred ctx cc (s,t) =
  let ccs = L.fold_left (fun ccs (l,r) -> (r,l) :: ccs) cc cc in
  let j = idx (s,t) in
  let redcbl rl =
    let i = idx rl in (
    try Hashtbl.find redc (j, i)
    with Not_found ->
      let red = Rewriting.reducible_with [rl] in
      let is_rule (l,r) = Rule.is_rule (l,r) && (not (Term.is_subterm l r)) in
      let b = is_rule rl && (red t || red s) in
      Hashtbl.add redc (j, i) b; b)
  in
  Logic.big_or ctx [ C.rule_var ctx rl | rl <- ccs; redcbl rl ]
;;

let c_red ctx cc = L.iter (fun rl -> Logic.require (rlred ctx cc rl)) cc
let c_red ctx = A.take_time A.t_cred (c_red ctx)

(* this heuristic uses rules only in a non-increasing way *)
let c_red_size ctx ccr cc_vs =
  let ccsym' = [ (l,r),v | (l,r),v <- cc_vs; Term.size l >= Term.size r ] in
  let rdc = new Rewriter.reducibility_checker ccsym' in
  rdc#init None;
  let require_red st =
    let r = Logic.big_or ctx [ rl | rl <- rdc#reducible_rule st ] in
    Logic.require r
  in
  L.iter require_red ccr
;;

let c_red_size ctx ccr = A.take_time A.t_cred (c_red_size ctx ccr)

(* globals to create CPred constraints faster *)
let new_nodes = ref [];;
let reducibility_checker = ref (new Rewriter.reducibility_checker []);;

let c_cpred ctx cc_vs =
  (* create indices, cc_vs is already symmetric *)
  let rls = [ Lit.terms n | n <- !new_nodes; Lit.is_equality n ] in
  let nn_vs = [ rl, C.find_rule rl | rl <- rls @ [ r,l | l,r <- rls ] ] in
  let rdc = new Rewriter.reducibility_checker nn_vs in
  rdc#init (Some !reducibility_checker);

  let ovl = new Overlapper.overlapper_with cc_vs in
  ovl#init ();
  (* create constraints *)
  let red st = Logic.big_or ctx (rdc#reducible_rule st) in
  let c2 (rl,rl_var) =
    let red_cp (st,rl_var') = rl_var <&> rl_var' <=>> (red st) in
    L.rev_map red_cp (ovl#cps rl)
  in
  let cs = L.fold_left (fun cs rlv -> L.rev_append (c2 rlv) cs) [] cc_vs in
  L.iter (fun c -> Logic.assert_weighted c 1) cs;
  reducibility_checker := rdc;
;;

let c_cpred ctx = A.take_time A.t_ccpred (c_cpred ctx)

let c_min_cps ctx cc =
  let ccsymm = L.fold_left (fun ccs (l,r) -> (r,l) :: ccs) cc cc in
  let rs = [ rl | rl <- ccsymm; Rule.is_rule rl ] in
  let rule = C.find_rule in
  let c2 = [ !! (rule rl <&> (rule rl')) | rl <- rs; rl' <- rs;
                                            st <- O.nontrivial_cps rl rl' ] in
  L.iter (fun c -> Logic.assert_weighted c 1) c2;
;;

let check_equiv ctx a b =
  Logic.push ctx;
  Logic.require (!! (Logic.(<<=>>) a b));
  assert (not (Logic.check ctx));
  Logic.pop ctx
;;

let c_max_red_pre ctx cc =
  let update_rdcbl_constr st cc' =
    let constr =
      try let c = Hashtbl.find C.ht_rdcbl_constr st in c <|> rlred ctx cc' st
      with Not_found -> rlred ctx cc' st
    in
    Hashtbl.replace C.ht_rdcbl_constr st constr;
    ignore (C.get_rdcbl_var ctx st)
  in
  let cc_newl = [ Lit.terms n |  n <- !new_nodes; Lit.is_equality n ] in
  let cc_old = [ n |  n <- cc; not (List.mem n cc_newl) ] in
  L.iter (fun st -> update_rdcbl_constr st cc) cc_newl;
  L.iter (fun st -> update_rdcbl_constr st cc_newl) cc_old
;;

let c_max_red_pre ctx = A.take_time A.t_cred (c_max_red_pre ctx)

let c_max_red ctx cc =
  Hashtbl.iter (fun st c ->
  let r = (C.get_rdcbl_var ctx st) <=>> c in
  Logic.require r;
  if !(A.shape) = Boro || !(A.shape) = Ossigeno then (
    Logic.assert_weighted (C.get_rdcbl_var ctx st) 30;
    Logic.assert_weighted (C.find_rule st) 6)
  else 
    Logic.assert_weighted (C.get_rdcbl_var ctx st) 6;
  ) C.ht_rdcbl_constr;
;;

let c_max_red ctx = A.take_time A.t_cred (c_max_red ctx)

let c_max_goal_red ctx cc gs =
  NS.iter (fun g -> Logic.assert_weighted (rlred ctx cc (Lit.terms g)) 1) gs
;;

let c_comp ctx ns =
 let rule_var, weight_var = C.find_rule, C.find_eq_weight in
 let all_eqs ee = Logic.big_and ctx (L.map C.find_eq ee) in
 (* induce order: decrease from e to equations in ee *)
 let dec e ee = Logic.big_and ctx [ weight_var e <>> weight_var f | f <- ee] in
 (* encode reducibility of equation st *)
 let red st =
  let es = try Hashtbl.find rewrite_trace st with Not_found -> [] in
  Logic.big_or ctx [ C.find_eq e <&> all_eqs ee <&> dec e ee | (ee,e) <- es ] 
 in
 let considered ((s,t) as st) =
   let c = Logic.big_or1 [rule_var st; rule_var (t,s); red st] in
   Logic.require (C.find_eq st <=>> c);
 in
 (* initial equations have to be considered *)
 let axs = !settings.axioms in
 Logic.require (all_eqs [Lit.terms l | l <- axs; Lit.is_equality l]);
 L.iter considered [ l,r | l,r <- ns; not (l=r) ];
;;

let c_comp ctx = A.take_time A.t_ccomp (c_comp ctx)

(* constraints to guide search; those get all retracted *)
let search_constraints ctx (ccl, ccsymlvs) gs =
 (* orientable equations are used for CPs in CeTA ... *)
 let take_max = nth_iteration !heuristic.max_oriented (*|| !(S.do_proof)*) in
 (* A.little_progress 5 && !A.equalities < 500 *)
 let assert_c = function
   | S.Red -> c_red ctx ccl
   | S.Empty -> ()
   | S.Comp -> c_comp ctx ccl
   | S.RedSize -> c_red_size ctx ccl ccsymlvs
 in L.iter assert_c (constraints ());
 let assert_mc = function
   | S.Oriented -> c_maxcomp ctx ccsymlvs
   | S.NotOriented -> c_not_oriented ctx ccl
   | S.MaxRed -> c_max_red ctx ccl
   | S.MinCPs -> c_min_cps ctx ccl
   | S.GoalRed -> c_max_goal_red ctx ccl gs
   | S.CPsRed -> c_cpred ctx ccsymlvs
   | S.MaxEmpty -> ()
 in L.iter assert_mc (if take_max then [S.Oriented] else max_constraints ())
;;

(* find k maximal TRSs *)
let max_k ctx cc gs =
  let k = !heuristic.k !(A.iterations) in
  let cc_eq = [ Lit.terms n | n <- NS.to_list cc; Lit.is_equality n ] in
  let cc_symm = [n | n <- NS.to_list (NS.symmetric cc); Lit.is_equality n] in 
  let cc_symml = [Lit.terms c | c <- cc_symm] in
  L.iter (fun n -> ignore (C.store_rule_var ctx n)) cc_symml;
  (* lookup is not for free: get these variables only once *)
  let cc_symm_vars = [ n, C.find_rule (Lit.terms n) | n <- cc_symm; Rule.is_rule (Lit.terms n)  ] in
  let cc_symml_vars = [ Lit.terms n,v | n,v <- cc_symm_vars] in
  if debug 2 then F.printf "K = %i\n%!" k;
  let s = termination_strategy () in
  let no_dps = not (dps_used ()) in
  let rec max_k acc ctx n =
    if n = 0 then L.rev acc (* return TRSs in sequence of generation *)
    else (
      let sat_call = if use_maxsat () then Logic.max_sat else Logic.check in
      A.smt_checks := !A.smt_checks + 1;
      if A.take_time A.t_sat sat_call ctx then (
        let m = Logic.get_model ctx in
        let c = if use_maxsat () then Logic.get_cost ctx m else 0 in

        let add_rule (n,v) rls =
          if Logic.eval m v && (no_dps || not (Rule.is_dp (Lit.terms n))) then
            (n,v) :: rls
          else rls
        in
        let rr = L.fold_right add_rule cc_symm_vars []  in
        let order =
          if !settings.unfailing then St.decode 0 m s
          else Order.default
        in
        if !S.generate_order then order#print_params ();
        if debug 2 then order#print ();
        if !settings.unfailing && !Settings.do_assertions then (
          let ord n =
            let l, r = Lit.terms n in order#gt l r && not (order#gt r l)
          in
          assert (L.for_all ord (L.map fst rr)));
        Logic.require (!! (Logic.big_and ctx [ v | _,v <- rr ]));
        max_k ((L.map fst rr, c, order) :: acc) ctx (n-1))
     else (
       if (n = k && L.length !heuristic.strategy > 1) then (
         if debug 2 then F.printf "restart (no further TRS found)\n%!";
         raise (Restart (Select.select_for_restart cc)));
       acc))
   in
   if has_comp () then
     NS.iter (fun n -> ignore (C.store_eq_var ctx (Lit.terms n))) cc;
   (* FIXME: restrict to actual rules?! *)
   A.take_time A.t_orient_constr (St.assert_constraints s 0 ctx) cc_symml;
   c_max_red_pre ctx cc_eq;
   Logic.push ctx; (* backtrack point for Yices *)
   Logic.require (St.bootstrap_constraints 0 ctx cc_symml_vars);
   search_constraints ctx (cc_eq, cc_symml_vars) gs;
   if !(Settings.generate_benchmarks) && A.runtime () > 100. then (
     let rs,is = !(A.restarts), !(A.iterations) in
     Smtlib.benchmark (string_of_int rs ^ "_" ^ (string_of_int is)));
   let trss = max_k [] ctx k in
   Logic.pop ctx; (* backtrack: get rid of all assertions added since push *)
   trss
;;

let max_k ctx cc = A.take_time A.t_maxk (max_k ctx cc)

(* some logging functions *)
let log_max_trs j rr rr' c =
 F.printf "TRS %i - %i (cost %i):\n %a\nreduced:%!\n %a\n@." !A.iterations j c
   Rules.print (Variant.rename_rules rr)
   Rules.print (Variant.rename_rules rr')
;;

let limit_reached t =
  match strategy_limit () with
    | IterationLimit i when !(A.iterations) > i(* && not (A.some_progress ()) *)-> true
    | TimeLimit l when t > l -> true
    | _ -> false
;;

(* towards main control loop *)
(* Heuristic to determine whether the state is stuck in that no progress was
   made in the last n iterations. *)
let do_restart es gs =
if A.memory () > 6000 then (
  if debug 1 then F.printf "restart (memory limit of 6GB reached)\n%!";
  true)
else
  (* no progress measure *)
  let h = Hashtbl.hash (NS.size es, es, gs) in
  let rep = L.for_all ((=) h) !hash_iteration in
  hash_iteration := h :: !hash_iteration;
  hash_iteration := Listx.take_at_most 20 !hash_iteration;
  if rep && debug 1 then F.printf "restart (repeated iteration state)\n%!";
  (* iteration/size bound*)
  (* estimate exponential blowup *)
  let blow n m = float_of_int n >= 1.5 *. (float_of_int m) in
  let rec is_exp = function n::m::cs -> blow n m && is_exp (m::cs) | _ -> true in
  let eqcounts = Listx.take_at_most 6 !(A.eq_counts) in
  let blowup = !(A.iterations) > 6 && is_exp eqcounts in
  if blowup && debug 1 then F.printf "restart (blowup)\n%!";
  if limit_reached (A.runtime ()) && debug 1 then
    F.printf "restart (limit reached)\n";
  rep || limit_reached (A.runtime ()) || blowup
;;


let detect_shape es =
  let shape = A.problem_shape es in
  A.shape := shape;
  let fs_count = L.length (Rules.signature es) in
  if debug 1 then
    F.printf "detected shape %s %i\n%!" (Settings.shape_to_string shape) fs_count;
  let h = {!heuristic with hard_bound_equations = 200;hard_bound_goals = 100} in
  let emax k = L.fold_left max k [ Lit.size l  | l <- !settings.axioms] in
  let gmax k = L.fold_left max k [ Rule.size l  | l <- !settings.gs] in
  let h' =
    match shape with
    | Piombo -> { h with
        hard_bound_equations = 4000;
        hard_bound_goals = 200;
        n = 10;
        strategy = St.strategy_ordered_lpo
      }
    | Zolfo -> { h with
        n = 10;
        restart_carry = 2
      }
    | Xeno -> { h with
        n = 10;
        n_goals = 1;
        reduce_AC_equations_for_CPs = true;
        hard_bound_equations = 90;
        hard_bound_goals = 120;
        size_age_ratio = 60;
        soft_bound_equations = emax 70;
        soft_bound_goals = gmax 100
      }
    | Elio when fs_count > 3 -> { h with n = 10;
        hard_bound_equations = 45;
        hard_bound_goals = 45;
        soft_bound_equations = emax 30;
        soft_bound_goals = gmax 30
    }
    | Silicio -> { h with
        n = 10;
        n_goals = 1;
        size_age_ratio = 80;
        strategy = St.strategy_ordered_lpo;
        hard_bound_equations = 45;
        hard_bound_goals = 45;
        soft_bound_equations = emax 30;
        soft_bound_goals = gmax 30
      }
    | Ossigeno -> { h with
        n = 12;
        size_age_ratio = 80;
        hard_bound_equations = 45;
        hard_bound_goals = 45;
        soft_bound_equations = emax 30;
        soft_bound_goals = gmax 30
      }
    | Carbonio -> { h with
        full_CPs_with_axioms = true;
        hard_bound_equations = 360;
        hard_bound_goals = 270;
        n = 10;
        n_goals = 3;
        size_age_ratio = 60;
        soft_bound_equations = emax 40;
        soft_bound_goals = gmax 100;
      }
    | Calcio -> { h with n = 6 }
    | Magnesio -> { h with n = 6;
      hard_bound_equations = 40;
      hard_bound_goals = 45;
      soft_bound_equations = emax 25;
      soft_bound_goals = gmax 37
      }
    | NoShape -> { h with n = 6;
      hard_bound_equations = 60;
      hard_bound_goals = 90;
      soft_bound_equations = emax 40;
      soft_bound_goals = gmax 70
      }
    | Elio -> { h with 
      hard_bound_equations = 65;
      n = 6;
      soft_bound_equations = 45;
      strategy = St.strategy_ordered_lpo
      }
    | Boro -> { h with
        hard_bound_equations = 20;
        hard_bound_goals = 20;
        n = 14;
        size_age_ratio = 70;
        soft_bound_equations = emax 16;
        strategy = St.strategy_ordered_kbo
      }
  in
  heuristic := h'
;;


let set_iteration_stats aa gs =
  let i = !A.iterations in
  A.iterations := i + 1;
  A.equalities := NS.size aa;
  A.goals := NS.size gs;
  A.set_time_mem ();
  A.eq_counts := NS.size aa :: !(A.eq_counts);
  A.goal_counts := NS.size gs :: !(A.goal_counts);
  if debug 1 then (
    if debug 2 then 
   F.printf "Start iteration %i with %i equations:\n %a\n%!"
     !A.iterations (NS.size aa) NS.print aa;
   if !A.goals > 0 then
     let gnd = Rules.is_ground [ Lit.terms g | g <- NS.to_list gs ] in
     F.printf "\nand %i goals:\n%a %i%!\n" !A.goals NS.print gs
       (if gnd then 1 else 0));
  if debug 1 then (
    A.print ();
    A.show_proof_track !settings Select.all_nodes);
  (* re-evaluate symbols status not every iteration, too expensive *)
  if i mod 2 = 0 then (
    let rs = [Lit.terms e | e <- NS.to_list aa] in
    let cs = Commutativity.symbols rs in
    let acs = Ac.symbols rs in
    if debug 1 && (acs <> !settings.ac_syms || cs <> !settings.only_c_syms) then
      Format.printf "discovered %s symbols\n%!"
        (if acs <> !settings.ac_syms then "AC" else "C");
    let s = {!settings with ac_syms = acs; only_c_syms = cs} in
    settings := s;
    Select.settings := s)
;;


let store_trs ctx j rr cost =
  let rr = [ Lit.terms r | r <- rr ] in
  let rr_index = C.store_trs rr in
  (* for rewriting actually reduced TRS may be used; have to store *)
  let rr_reduced =
    if not !heuristic.reduce_trss then rr
    else if !(Settings.do_proof) <> None then interreduce rr
    else Variant.reduce_encomp rr
  in
  C.store_redtrs rr_reduced rr_index;
  C.store_rule_vars ctx rr_reduced; (* otherwise problems in norm *)
  if has_comp () then C.store_eq_vars ctx rr_reduced;
  if debug 2 then log_max_trs j rr rr_reduced cost;
  rr_index
;;

let subsumption_ratios : float list ref = ref []

let equations_for_overlaps irr all =
  if !A.iterations < 3 && !heuristic.full_CPs_with_axioms then
    NS.to_list (eqs_for_overlaps all)
  else
    let last3 =
      match !subsumption_ratios with
      | a :: b :: c :: d :: _ -> a +. b +. c +. d <= 3.6
      | _ -> false
    in
    let check = check_subsumption 1 && (!A.iterations < 9 || last3) in
    let irr' = if check then NS.subsumption_free irr else irr in
    let r = float_of_int (NS.size irr') /. (float_of_int (NS.size irr)) in
    if debug 1 then
      Format.printf "subsumption check (ratio %.2f)\n%!" r;
    subsumption_ratios := r :: !subsumption_ratios;
    (*if r <= 0.3 then (* might be useful for GRP505 - GRP508 *)
      heuristic := {!heuristic with check_subsumption = 2};*)
    NS.to_list (eqs_for_overlaps irr')
;;

let check_order_generation success order =
  if !S.generate_order &&
      (success || limit_reached (A.runtime ()) || A.runtime () > 30.) then (
    order#print_params ();
    exit 0)
;;

let rec phi ctx aa gs =
  if do_restart aa gs then raise (Restart (Select.select_for_restart aa));
  let redcount, cp_count = ref 0, ref 0 in
  set_iteration_stats aa gs;
  let aa =
    if check_subsumption 2 && nth_iteration 3 then NS.subsumption_free aa
    else aa
  in
  let process (j, aa, gs, aa_new) (rr, c, order) =
    let n = store_trs ctx j rr c in
    let rr_red = C.redtrs_of_index n in (* interreduce *)
    let rew = new Rewriter.rewriter !heuristic rr_red !settings.ac_syms order in
    check_order_generation false order;
    rew#init ();
    (* TODO: red is often very small, is this rewriting necessary? *)
    let irred, red = rewrite rew aa in (* rewrite eqs wrt new TRS *)
    redcount := !redcount + (NS.size red);

    let thresh = NS.avg_size gs + 8 in
    let t = Unix.gettimeofday () in
    let gs_red = reduced ~max_size:!heuristic.hard_bound_goals rew gs in
    A.t_rewrite_goals := !A.t_rewrite_goals +. (Unix.gettimeofday () -. t);
    let gs_red', gs_big =
      if NS.size gs_red < 10 then gs_red, NS.empty ()
      else NS.filter_out (fun n -> Lit.size n > thresh) gs_red
    in
    let gs = NS.add_all gs_red' gs in

    let irr = NS.filter Lit.not_increasing (NS.symmetric irred) in
    let aa_for_ols = equations_for_overlaps irr aa in
    let cps', ovl = overlaps rr aa_for_ols in
    cp_count := !cp_count +  (NS.size cps');
    let eq_bound = !heuristic.hard_bound_equations in
    let cps = NS.filter (fun cp -> Lit.size cp < eq_bound) cps' in
    let cps_large = NS.filter (fun cp -> Lit.size cp >= eq_bound) cps' in
    let cps = reduced rew cps in
    let nn = NS.diff (NS.add_all cps red) aa in (* new equations *)
    let sel, rest = Select.select (aa,rew) nn in
    if !(Settings.track_equations) <> [] then
      A.update_proof_track sel (NS.to_list rest) !(A.iterations);
    let gos = overlaps_on rr aa_for_ols ovl gs in
    let g_bound = !heuristic.hard_bound_goals in
    let gcps = NS.filter (fun g -> Lit.size g < g_bound) gos in
    if NS.exists (fun g -> Lit.size g < g_bound) gos then
      incomplete := true;
    let t = Unix.gettimeofday () in
    let gcps = reduced ~max_size:g_bound rew gcps in
    A.t_rewrite_goals := !A.t_rewrite_goals +. (Unix.gettimeofday () -. t);
    let gs' = NS.diff (NS.add_all gs_big gcps) gs in
    let gg, grest = Select.select_goals (gs,rew) aa !heuristic.n_goals gs' in
    if !(Settings.track_equations) <> [] then
      A.update_proof_track gg (NS.to_list grest) !(A.iterations);
    store_remaining_nodes ctx rest;
    store_remaining_goals ctx grest;
    let ieqs = NS.to_rules (NS.filter Lit.is_inequality aa) in
    let cc = (axs (), cps, cps_large) in
    match succeeds ctx (rr, irr) rew cc ieqs gs with
       Some r ->
       if !(Settings.generate_benchmarks) then
         Smtlib.benchmark "final";
       if !S.generate_order then
         (check_order_generation true order; failwith "order generated")
       else raise (Success r)
     | None -> (j+1, NS.add_list sel aa, NS.add_list gg gs, sel @ aa_new)
  in
  try
    let rrs = max_k ctx aa gs in
    let s = Unix.gettimeofday () in
    let _, aa', gs', aa_new = L.fold_left process (0, aa, gs,[]) rrs in
    let sz = match rrs with (trs,c,_) :: _ -> List.length trs,c | _ -> 0,0 in
    let cp_count = if rrs = [] then 0 else !cp_count / (List.length rrs) in
    A.add_state !redcount (fst sz) (snd sz) cp_count;
    new_nodes := aa_new;
    A.t_process := !(A.t_process) +. (Unix.gettimeofday () -. s);
    phi ctx aa' gs'
  with Success r -> r
;;

let init_settings (settings_flags, heuristic_flags) axs gs =
  A.restart ();
  A.iterations := 0;
  let axs_eqs = [ Lit.terms a | a <- axs ] in
  let acs = Ac.symbols axs_eqs in
  let cs = Commutativity.symbols axs_eqs in
  let is_large = L.length axs_eqs >= 90 in
  let s =
    { !settings with
      ac_syms = acs;
      auto = if is_large then false else settings_flags.auto;
      axioms = axs;
      debug = settings_flags.debug;
      gs = gs;
      only_c_syms = Listset.diff cs acs;
      signature = Rules.signature (axs_eqs @ gs);
      tmp = settings_flags.tmp;
      unfailing = settings_flags.unfailing
    }
  in
  let h =
    if is_large then
      let saql = St.strategy_aql in
      { !heuristic with k = (fun _ -> 4); reduce_trss = false; strategy = saql }
    else
      { !heuristic with
        n = heuristic_flags.n;
      }
  in
  settings := s;
  Select.settings := s;
  heuristic := h;
  Select.heuristic := h;
  if settings_flags.auto && not is_large then detect_shape axs_eqs;
  if !(Settings.do_proof) <> None then Trace.add_initials axs_eqs;
  if !heuristic.reduce_AC_equations_for_CPs then (
    let acx = [ Lit.make_axiom (normalize (Ac.cassociativity f)) | f <- acs ] in
    acx_rules := [ Lit.flip r | r <- acx ] @ acx);
  A.init_proof_track !(Settings.track_equations);
  A.update_proof_track axs [] 0
;;

let remember_state es gs =
 let h = Hashtbl.hash (termination_strategy (), es,gs) in
 if h = !hash_initial then
   heuristic := { !heuristic with n = Pervasives.max (!heuristic.n + 1) 15};
 hash_initial := h
;;


let ckb ((settings_flags, heuristic_flags) as flags) input =
  settings := settings_flags;
  heuristic := heuristic_flags;
  Select.settings := settings_flags;
  Select.heuristic := heuristic_flags;
  let rec ckb (es, gs) =
    (* TODO check positive/negative goals??? *)
    let eq_ok e = Lit.is_equality e || Lit.is_ground e in
    if not (L.for_all eq_ok es) then
      raise Fail;
    (*if gs = [] then heuristic.strategy := St.strategy_ordered_sat;*)
    (* store initial state to capture*)
    (* init state *)
    let est =
      if !(S.do_proof) <> None then [e | e <- es;not (Lit.is_trivial e)] else es
    in
    let es' = L.map Lit.normalize est in
    let es0 = L.sort Pervasives.compare es' in
    let gs0 = L.map Lit.normalize gs in
    Select.all_nodes := [ e, Lit.size e | e <- es0 ];
    Hashtbl.clear Select.all_nodes_set;
    ignore (NS.add_list es0 Select.all_nodes_set);
    init_settings flags es0 [ Lit.terms g | g <- gs0 ];
    remember_state es gs;
    try
      let cas = [ Ac.cassociativity f | f <- !settings.ac_syms ] in
      let es0 = [ Lit.make_axiom (Variant.normalize_rule r) | r <- cas ] @ es0 in
      let ctx = Logic.mk_context () in
      let ns0 = NS.of_list es0 in
      new_nodes := es0;
      let ss = Listx.unique (t_strategies ()) in
      L.iter (fun s -> St.init s 0 ctx [ Lit.terms n | n <- gs0 @ es0 ]) ss;
      if !settings.keep_orientation then (
        let es = [ Variant.normalize_rule_dir (Lit.terms e) | e <- es ] in
        let es' = [ if d then e else R.flip e | e,d <- es ] in
        let oriented = [ !!(C.rule_var ctx (R.flip r)) | r <- es' ] in
        let keep = Logic.big_and ctx oriented in
        Logic.require keep;
        L.iter (fun r -> Logic.assert_weighted (C.rule_var ctx r) 27) es'
      );
      let res = phi ctx ns0 (NS.of_list gs0) in
      Logic.del_context ctx;
      res
    with Restart es_new -> (
      pop_strategy ();
      St.clear ();
      Cache.clear ();
      A.restarts := !A.restarts + 1;
      Hashtbl.reset rewrite_trace;
      Hashtbl.reset cp_cache;
      NS.reset_age ();
      A.mem_diffs := [];
      A.time_diffs := [];
      ckb ((if gs = [] then es0 else es_new @ es0), gs))
  in
  ckb input
;;
