(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module L = List
module O = Overlap
module R = Rule
module A = Analytics
module S = Settings
module Ac = Theory.Ac
module Commutativity = Theory.Commutativity
module Lit = Literal
module NS = Nodes

(*** OPENS *******************************************************************)
open Prelude
open Yicesx
open Settings

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

let acx_rules = ref []

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

let check_subsumption n = !(settings.check_subsumption) == n

let nth_iteration n = !A.iterations mod n == 0

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

let store_remaining_nodes ctx ns =
  if has_comp () then
    NS.iter (fun n -> ignore (C.store_eq_var ctx (Lit.terms n))) ns;
  if !(settings.size_age_ratio) < 100 then
    let ns = NS.smaller_than !(settings.size_bound_equations) ns in
    all_nodes := L.rev_append (L.rev !all_nodes) (NS.sort_size ns)
;;

let rec get_oldest_node (aa,rew) =
  match !all_nodes with
     [] -> None
   | n :: ns ->
     all_nodes := ns;
     let s,t = Lit.terms n in
     if fst (rew#nf s) = fst (rew#nf t) || NS.mem aa n then (
       (*if fst (rew#nf s) = fst (rew#nf t) then
         F.printf " ... discard/joinable %a \n" Lit.print n
       else
         F.printf " ... discard/present %a \n" Lit.print n;*)
       get_oldest_node (aa,rew))
     else Some n
;;

let shape_changed es =
  let shape = A.problem_shape (List.map Lit.terms (NS.to_list es)) in
  !(settings.auto) && shape <> !(A.shape) && shape <> NoShape
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
    | Some (nnews, rs) -> ((* if terms got equal, nnew is empty *)
        if nnews <> [] then
          add_rewrite_trace (Lit.terms n) rs (Lit.terms (L.hd nnews));
        irrdcbl, NS.add_list nnews news)
 in NS.fold rewrite cs (NS.empty (), NS.empty ())
;;  
   
let rewrite rr = A.take_time A.t_rewrite (rewrite rr)

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
  let pnode f n =
    F.fprintf f "%a  (%i) (%i)" Lit.print n (Nodes.age n) (Lit.size n)
  in
  let plist = Formatx.print_list pnode "\n " in
  F.printf "select %i from %i:\n%a\n%!" (L.length ss) (NS.size cc) plist ss;
  F.printf "all:\n%a\n%!" plist (NS.sort_size (NS.to_list cc))
;;


let select_count i = !(settings.n)

let keep acs n =
  let fs = Rule.functions (Lit.terms n) in
  L.length fs > 1 || not (Listset.subset fs acs) ||
  L.mem (Lit.terms n) (ac_eqs ()) || not (Lit.is_ac_equivalent n acs)
;;

let select_goal_similar (_,_) ns =
  let sim = Term.similarity !(settings.ac_syms) !(settings.only_c_syms) in
  let rsim (s,t) (s',t') = sim s s' +. sim t t' in
  let msim r = L.fold_left (fun m q -> m +. (rsim r q)) 0. !(settings.gs) in
  let ns' = [ n, msim (Lit.terms n) | n <- ns ] in
  let cmp m k = if m -. k < 0. then 1 else if m -. k > 0. then -1 else 0 in
  let ns' = L.sort (fun (_,m) (_,k) -> cmp m k) ns' in
  let n,d = L.hd ns' in
  if debug () then
    F.printf "selected for goal similarity: %a  (%i) %.3f\n%!"
      Lit.print n (Nodes.age n) d;
  n
;;

let selections = ref 0

(* ns is assumed to be size sorted *)
let select_size_age aarew ns_sorted all n =
  let rec select ns acc n =
    (* if ns is empty then there is also no interesting old node*)
    if n <= 0 || ns = [] then L.rev acc
    else (
      selections := !selections + 1;
      if !selections mod (!(settings.size_age_ratio) / 10) <> 0 then
        select (L.tl ns) (L.hd ns :: acc) (n-1)
      else if !selections mod 26 = 0 && all <> [] then
        let b = select_goal_similar aarew all in
        select ns (b::acc) (n-1)
      else (
        match get_oldest_node aarew with
        | Some b ->
          if debug () then
            F.printf "age selected: %a  (%i) (%i)\n%!"
              Lit.print b (Nodes.age b) (Lit.size b);
          select ns (b::acc) (n-1)
        | None -> select (L.tl ns) (L.hd ns :: acc) (n-1)))
   in select ns_sorted [] n
;;

let split k ns =
  let rec split acc k size = function
    [] -> L.rev acc,[]
    | n :: ns ->
      let s = Lit.size n in
      if k > 0 || s = size then (split (n::acc) (Pervasives.max 0 (k - 1)) s ns)
      else L.rev acc,ns
  in
  let about_k, _ = split [] k 0 ns in
  fst (Listx.split_at_most k (NS.sort_size_age about_k))
;;

(* selection of small new nodes *)
let select' ?(only_size=true) aarew k cc thresh =
 let k = if k = 0 then select_count !(A.iterations) else k in
 let acs = !(settings.ac_syms) in
 let small = NS.smaller_than thresh cc in
 let aa = 
   if only_size || !(settings.size_age_ratio) = 100 then
     let aa,_ = L.partition (keep acs) small in
     let aa = NS.sort_size aa in
     fst (Listx.split_at_most k aa)
   else
     let small,_ = L.partition (keep acs) small in
     let size_sorted = NS.sort_size small in
     let size_sorted' = split k size_sorted in
     Random.self_init();
     select_size_age aarew size_sorted' (NS.smaller_than 16 cc) k
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
  let k = !(A.restarts) * 2 in
  let rew = new Rewriter.rewriter [] [] Order.default in
  let ths = Listset.diff (A.theory_equations (NS.to_list cc)) (axs ()) in
  let ths' = if shape_changed cc then ths else [] in
  fst (select' (NS.empty (),rew) k (NS.diff_list cc (axs () @ ths)) 30) @ ths'

let select rew cc =
  let thresh = !(settings.size_bound_equations) in
  A.take_time A.t_select (select' ~only_size:false rew 0 cc) thresh
;;

let select_goals' k gg thresh =
 let acs = !(settings.ac_syms) in
 let small,_ = L.partition (keep acs) (NS.smaller_than thresh gg) in
 let sorted = NS.sort_size_unif small in
 let gg_a = fst (Listx.split_at_most k sorted) in
 let gg_p = NS.diff_list gg gg_a in 
 if debug () then log_select gg gg_a;
 (gg_a, gg_p)
;;

let select_goals k cc =
  A.take_time A.t_select (select_goals' k cc) !(settings.size_bound_goals)
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
     let acs, cs = !(settings.ac_syms), !(settings.only_c_syms) in
     let aa' = NS.ac_equivalence_free acs (Listset.diff aa !acx_rules) in
     let rr' = NS.ac_equivalence_free !(settings.ac_syms) rr in
     let aa' = NS.c_equivalence_free cs aa' in
     (*let rr' = NS.c_equivalence_free cs rr' in*)
     rr' @ aa'
 in
 let ns = [ Lit.terms n | n <- ns ] in
 let ovl = new Overlapper.overlapper ns in
 ovl#init ();
 let cps2 = NS.of_list [ cp | n <- ns; cp <- ovl#cps n ] in
 cps2, ovl
;;

let overlaps rew rr = A.take_time A.t_overlap (overlaps rew rr)

(* goal only as outer rule *)
let overlaps_on rew rr aa overlapper gs =
 let ns = rr @ aa in
 let gs_for_ols = NS.to_list (eqs_for_overlaps gs) in
 let cps1 = NS.of_list [ n | r <- ns; g <- gs_for_ols; n <- cps rew r g ] in
 (*let cps2 = NS.of_list [ cp | g <- gs_for_ols; cp <- overlapper#cps (Lit.terms g) ] in
 assert (NS.subset cps1 cps2);*)
 cps1
;;

(* * SUCCESS CHECKS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let saturated ctx (rr,ee) rewriter cc =
  let ee' = Rules.subsumption_free ee in
  let str = termination_strategy () in
  let d = !(settings.d) in
  let sys = rr,ee',!(settings.ac_syms),!(settings.signature),rewriter#order in
  let xsig = !(settings.extended_signature) in
  let eqs = [(*normalize*) (Lit.terms n) | n <- NS.to_list cc; Lit.is_equality n] in
  (*let eqs' = Listset.diff eqs ([ t,s | s,t <- ee ] @ ee) in*)
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

let succeeds ctx (rr,ee) rewriter cc ieqs gs =
  if debug () then
    Format.printf "start success check\nRR:\n%a\nCC:\n%a\n%!"
      Rules.print [ Lit.terms r | r <- rr] NS.print cc;
  let rr,ee = [ Lit.terms r | r <- rr],[ Lit.terms e | e <- NS.to_list ee] in
  rewriter#add_more ee;
  let joinable (s,t) = fst (rewriter#nf s) = fst (rewriter#nf t) in
  let ok g = let u,v = Lit.terms g in joinable (u,v) || Subst.unifiable u v in
  if NS.exists ok gs then (
    let g = L.find ok (NS.to_list gs) in
    assert (Lit.is_inequality g); (* equality goals are used as axioms *)
    let s,t = Lit.terms g in
    let (_, rss), (_,rst) = rewriter#nf s, rewriter#nf t in
    if debug () then (
      let str = if joinable (s,t) then "joinable" else "unifiable" in
      F.printf "%s: %a\n%!" str (fun f g -> Lit.print f g) g;
      F.printf "rules: {%a} \n{%a}\n" Rules.print [r | r,_ <- rss]
        Rules.print [r | r,_ <- rst]);
    if joinable (s,t) then
      Some (UNSAT, Proof ((s,t),rewrite_seq rewriter (s,t) (rss,rst),[]))
    else
      (* unifiable *)
      let sigma = Subst.mgu s t in
      let s',t' = Rule.substitute sigma (s,t) in
      Some (UNSAT, Proof ((s,t),rewrite_seq rewriter (s',t') ([],[]), sigma)))
  else (
    let sat = saturated ctx (rr,ee) rewriter cc in
    let order = match sat with None -> rewriter#order | Some o -> o in
    let goals_ground = L.for_all (fun g -> Lit.is_ground g) (NS.to_list gs) in
    let orientable (s,t) = order#gt s t || order#gt t s in
    if L.exists joinable ieqs then (* joinable inwquality axiom *)
      Some (UNSAT, Proof (L.find joinable ieqs,([],[]),[]))
    (* if an equation is orientable, wait one iteration ... *)
    else if sat <> None && not goals_ground &&
      List.for_all (fun e -> not (orientable e)) ee then
      Narrow.decide rr (ee @ [s,t| t,s <- ee ]) order !(settings.gs)
    else if rr @ ee = [] || (sat <> None && goals_ground) then (
      if ee = [] then
        Some (SAT, Completion rr)
      else if ieqs = [] then
        Some (SAT, GroundCompletion (rr, ee, order))
      else None
    )
    else None)
;;

let succeeds ctx re rew cc =
  A.take_time A.t_success_check (succeeds ctx re rew cc)
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
    try Hashtbl.find redc (j, i)
    with Not_found ->
      let red = Rewriting.reducible_with [rl] in
      let is_rule (l,r) = Rule.is_rule (l,r) && (not (Term.is_subterm l r)) in
      let b = is_rule rl && (red t || red s) in
      Hashtbl.add redc (j, i) b; b)
  in big_or ctx [ C.find_rule (Lit.terms n) | n <- ccs; redcbl (Lit.terms n) ]
;;

let c_red ctx cc = L.iter (fun n -> require (rlred ctx cc (Lit.terms n))) cc

let c_red ctx = A.take_time A.t_cred (c_red ctx)

let c_cpred ctx cc =
  Hashtbl.clear reducible;
  let ccsymm = L.fold_left (fun ccs n -> Lit.flip n :: ccs) cc cc in
  let rs = [ Lit.terms n | n <- ccsymm; Rule.is_rule (Lit.terms n) ] in
  let rule, red = C.find_rule, is_reducible ctx ccsymm in
  let c2 = [ rule rl <&> (rule rl') <=>> (red st) | rl <- rs; rl' <- rs;
                                             st <- O.nontrivial_cps rl rl' ] in
  L.iter (fun c -> ignore (assert_weighted c 2)) c2;
;;

let c_cpred ctx = A.take_time A.t_ccpred (c_cpred ctx)

let c_max_red ctx cc =
  L.iter (fun n -> assert_weighted (rlred ctx cc (Lit.terms n)) 1) cc
;;

let c_max_red ctx = A.take_time A.t_cred (c_max_red ctx)


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

let c_comp ctx = A.take_time A.t_ccomp (c_comp ctx)

(* constraints to guide search; those get all retracted *)
let search_constraints ctx cc gs =
 let ccl = NS.to_list cc in
 let take_max = nth_iteration !(settings.max_oriented) in
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
 in L.iter assert_mc (if take_max then [S.Oriented] else max_constraints ())
;;

(* find k maximal TRSs *)
let max_k ctx cc gs =
  let k = !(settings.k) !(A.iterations) in
  let cc_symm = NS.to_list (NS.symmetric cc) in 
  if debug () then F.printf "K = %i\n%!" k;
  let s = termination_strategy () in
  let rec max_k acc ctx cc n =
    if n = 0 then L.rev acc (* return TRSs in sequence of generation *)
    else (
      let sat_call = if use_maxsat () then max_sat else check in
      if A.take_time A.t_sat sat_call ctx then (
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
   A.take_time A.t_orient_constr (Strategy.assert_constraints s 0 ctx)cc_symm;
   push ctx; (* backtrack point for Yices *)
   require (Strategy.bootstrap_constraints 0 ctx cc_symm);
   search_constraints ctx cc gs;
   let trss = max_k [] ctx cc k in
   pop ctx; (* backtrack: get rid of all assertions added since push *)
   trss
;;

let max_k ctx cc = A.take_time A.t_maxk (max_k ctx cc)

(* some logging functions *)
let log_iteration i aa =
 F.printf "Iteration %i\n%!" i;
 F.printf "CC: %i\n%a%!" (NS.size aa) NS.print aa;
 F.printf "\n%!"
;;

let log_max_trs j rr rr' c =
 F.printf "TRS %i - %i (cost %i):\n %a\nreduced:%!\n %a\n@." !A.iterations j c
   Rules.print (Variant.rename_rules rr)
   Rules.print (Variant.rename_rules rr')
;;

(* towards main control loop *)
(* Heuristic to determine whether the state is stuck in that no progress was
   made in the last n iterations. *)
let do_restart es gs =
 if A.memory () > 6000 then (
   if debug () then F.printf "restart (memory limit of 6GB reached)\n%!";
   true)
 else
   let to_eqs ns = List.map Lit.terms (NS.to_list ns) in
   let shape = A.problem_shape (to_eqs es) in
   if !(settings.auto) && shape <> !(A.shape) && shape <> NoShape then (
     if debug () then
       Format.printf "restart (new shape detected)\n%!";
     true)
 else
  (* no progress measure *)
  let h = Hashtbl.hash (NS.size es, es, gs) in
  let rep = L.for_all ((=) h) !hash_iteration in
  hash_iteration := h :: !hash_iteration;
  hash_iteration := Listx.take_at_most 20 !hash_iteration;
  if rep && debug () then F.printf "restart (repeated iteration state)\n%!";
  (* iteration/size bound*)
  let running_time = (Unix.gettimeofday () -. !(start_time)) in
  let limit =
    match strategy_limit () with
      | IterationLimit i when !(A.iterations) > i -> true
      | TimeLimit l when running_time > l -> true
      | _ -> false
  in
  (* estimate exponential blowup *)
  let blow n m = float_of_int n >= 1.5 *. (float_of_int m) in
  let rec is_exp = function n::m::cs -> blow n m && is_exp (m::cs) | _ -> true in
  let eqcounts = Listx.take_at_most 6 !(A.eq_counts) in
  let blowup = !(A.iterations) > 6 && is_exp eqcounts in
  if blowup && debug () then F.printf "restart (blowup)\n%!";
  if limit && debug () then F.printf "restart (limit reached)\n";
  rep || limit || blowup
;;


let detect_shape es =
  let shape = A.problem_shape es in
  A.shape := shape;
  if debug () then
    F.printf "detected shape %s\n%!" (Settings.shape_to_string shape);
  let fs_count = L.length (Rules.signature es) in
  match shape with
    | Piombo
    | Zolfo -> settings.n := 10
    | Xeno -> (
      settings.reduce_AC_equations_for_CPs := true;
      settings.n := 10
    )
    | Elio when fs_count > 3 -> settings.n := 10
    | Silicio ->
      settings.n := 10;
      settings.size_age_ratio := 85;
      settings.strategy := Strategy.strategy_ordered_lpo
    | Ossigeno ->
      settings.n := 12;
      settings.size_age_ratio := 80;
    | Carbonio
    | NoShape -> settings.n := 6
    | Elio -> settings.n := 6
    | Boro -> (
      settings.n := 14;
      settings.size_age_ratio := 70;
      settings.size_bound_equations := 16;
      settings.strategy := Strategy.strategy_ordered_kbo)
;;


let set_iteration_stats aa gs =
  let i = !A.iterations in
  A.iterations := i + 1;
  A.ces := NS.size aa;
  A.goals := NS.size gs;
  let mem_diff = A.memory () - !last_mem in
  let time_diff = Unix.gettimeofday () -. !last_time in
  last_mem := A.memory ();
  last_time := Unix.gettimeofday ();
  A.time_diffs := time_diff :: !(A.time_diffs);
  A.mem_diffs := mem_diff :: !(A.mem_diffs);
  A.eq_counts := NS.size aa :: !(A.eq_counts);
  if debug () then (
   F.printf "Start iteration %i with %i equations:\n %a\n%!"
     !A.iterations (NS.size aa) NS.print aa;
   if !A.goals > 0 then
     let gnd = Rules.is_ground [ Lit.terms g | g <- NS.to_list gs ] in
     F.printf "\nand %i goals:\n%a %i%!\n" !A.goals NS.print gs
       (if gnd then 1 else 0);
   let json = A.json () in
   F.printf "%s\n%!" (Yojson.Basic.pretty_to_string json))
;;


let store_trs ctx j rr cost =
  let rr = [ Lit.terms r | r <- rr ] in
  let rr_index = C.store_trs rr in
  (* for rewriting actually reduced TRS is used; have to store *)
  let rr_reduced =
    if !(Settings.do_proof) then interreduce rr else Variant.reduce_encomp rr
  in
  C.store_redtrs rr_reduced rr_index;
  C.store_rule_vars ctx rr_reduced; (* otherwise problems in norm *)
  if has_comp () then C.store_eq_vars ctx rr_reduced;
  if debug () then log_max_trs j rr rr_reduced cost;
  rr_index
;;

let equations_for_overlaps irr all =
  if !A.iterations < 3 && !(settings.full_CPs_with_axioms) then
    NS.to_list (eqs_for_overlaps all)
  else
    let irr' = if check_subsumption 1 then NS.subsumption_free irr else irr in
    NS.to_list (eqs_for_overlaps irr')
;;

let rec phi ctx aa gs =
  if do_restart aa gs then raise (Restart (select_for_restart aa));
  set_iteration_stats aa gs;
  let aa =
    if check_subsumption 2 && nth_iteration 3 then NS.subsumption_free aa
    else aa
  in
  let process (j, aa, gs) (rr, c, order) =
    let rr_red = C.redtrs_of_index (store_trs ctx j rr c) in (* interreduce *)
    let rew = new Rewriter.rewriter rr_red !(settings.ac_syms) order in
    rew#init ();
    let irred, red = rewrite rew aa in (* rewrite eqs wrt new TRS *)
    let gs = NS.add_all (reduced rew gs) gs in (* rewrite goals wrt new TRS *)
    let irr = NS.filter Lit.not_increasing (NS.symmetric irred) in
    (*let irr' = if check_subsumption 1 then NS.subsumption_free irr else irr in
    let aa_for_ols = NS.to_list (eqs_for_overlaps irr') in*)
    let aa_for_ols = equations_for_overlaps irr aa in
    let cps, ovl = overlaps rew rr aa_for_ols in
    let cps = reduced rew cps in (* rewrite CPs *)
    let nn = NS.diff (NS.add_all cps red) aa in (* new equations *)
    let sel, rest = select (aa,rew) nn in
    let gcps = reduced rew (overlaps_on rew rr aa_for_ols ovl gs) in (* goal CPs *)
    let gg = fst (select_goals 2 (NS.diff gcps gs)) in
    store_remaining_nodes ctx rest;
    let ieqs = NS.to_rules (NS.filter Lit.is_inequality aa) in
    match succeeds ctx (rr, irr) rew (NS.add_list (axs ()) cps) ieqs gs with
       Some r -> raise (Success r)
     | None -> (j+1, NS.add_list sel aa, NS.add_list gg gs)
  in
  try
    let rrs = max_k ctx aa gs in
    let s = Unix.gettimeofday () in
    let _, aa', gs' = L.fold_left process (0, aa, gs) rrs in
    A.t_process := !(A.t_process) +. (Unix.gettimeofday () -. s);
    phi ctx aa' gs'
  with Success r -> r
;;


let init_settings fs es gs =
 let acs = Ac.symbols es in
 settings.ac_syms := acs;
 let cs = Commutativity.symbols es in
 settings.only_c_syms := Listset.diff cs acs;
 settings.signature := Rules.signature (es @ gs);
 settings.d := !(fs.d);
 A.iterations := 0;
 settings.n := !(fs.n);
 settings.strategy := !(fs.strategy);
 settings.auto := !(fs.auto);
 settings.tmp := !(fs.tmp);
 settings.es := es;
 settings.gs := gs;
 start_time := Unix.gettimeofday ();
 last_time := Unix.gettimeofday ();
 last_mem := A.memory ();
 Settings.is_ordered := !(settings.unfailing);
 if !(Settings.do_proof) then
   Trace.add_initials es;
 if debug () then
   F.printf "AC syms: %s \n%!"
     (L.fold_left (fun s f -> Signature.get_fun_name f ^ " " ^ s) ""
     (Ac.symbols es));
 if !(settings.reduce_AC_equations_for_CPs) then (
   let acxs = [ Lit.make_axiom (normalize (Ac.cassociativity f)) | f <- acs ] in
   acx_rules := [ Lit.flip r | r <- acxs ] @ acxs);
 if !(fs.auto) then detect_shape es
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
 (*if gs = [] then settings.strategy := Strategy.strategy_ordered_sat;*)
 (* store initial state to capture*)
 remember_state es gs;
 (* init state *)
 let ctx = mk_context () in
 let es' = L.map Lit.normalize [e | e <- es; not (Lit.is_trivial e)] in
 let es0 = L.sort Pervasives.compare es' in
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
    L.iter (fun r -> assert_weighted (C.rule_var ctx r) 27) es'
    );
  let res = phi ctx ns0 (NS.of_list gs0) in
  del_context ctx;
  res
 with Restart es_new -> (
  if debug () then F.printf "restart\n%!";
  pop_strategy ();
  Strategy.clear ();
  Cache.clear ();
  A.restarts := !A.restarts + 1;
  Hashtbl.reset rewrite_trace;
  del_context ctx;
  Hashtbl.reset cp_cache;
  sizes := [];
  A.mem_diffs := [];
  A.time_diffs := [];
  A.eq_counts := [];
  ckb fs ((if gs = [] then es0 else es_new @ es0), gs))
