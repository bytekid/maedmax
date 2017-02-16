(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module L = List
module O = Overlap
module R = Rule
module St = Statistics
module S = Strategy

(*** OPENS *******************************************************************)
open Prelude
open Yicesx
open Settings
open Node

(*** MODULES *****************************************************************)
module N = Equation
module NS = Nodes.Make(N)

(*** TYPES *******************************************************************)
type result = Completion of Rules.t
  | GroundCompletion of (Rules.t * Rules.t)
  | Proof

(*** EXCEPTIONS **************************************************************)
exception Success of result
exception Restart of N.t list
exception Fail

(*** GLOBALS *****************************************************************)
let settings = Settings.default

let sizes = ref [] (* to check degeneration *)
let last_time = ref 0.0
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

(*** FUNCTIONS ***************************************************************)
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

let max_iterations _ = 
 match !(settings.strategy) with 
  | [] -> failwith "empty strategy list"
  | (_, _, _, i) :: _ -> i
;;

let use_maxsat _ = max_constraints () <> []

let has_comp () = L.mem S.Comp (constraints ())

let pop_strategy _ = 
 if !(settings.d) then F.printf "pop strategy\n%!";
 match !(settings.strategy) with
  | [] -> failwith "no strategy left in pop"
  | [s] -> ()
  | _ :: ss -> settings.strategy := ss
;;

let t_strategies _ = L.map (fun (ts,_,_,_) -> ts) !(settings.strategy)

(* * REWRITING * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let add_rewrite_trace st rls st' =
  if has_comp () then
    begin
    let reducts = try Hashtbl.find rewrite_trace st with Not_found -> [] in
    Hashtbl.replace rewrite_trace st ((rls, st') :: reducts)(*;
    Format.printf "%a reduces to %a\n" Rule.print st Rule.print st'*)
    end
;;

(* normalization of cs with TRS with index n. Returns pair (cs',ff) where ff
   are newly generated eqs and cs' \subseteq cs is set of irreducible eqs *)
let rewrite rewriter cs =
 let rewrite n (irrdcbl, news) =
   match N.rewriter_nf_with rewriter n with
    | None -> (NS.add n irrdcbl, news) (* no progress here *)
    (* n' is leftover of n (only relevant with constraints *)
    | Some (n', nnew, rs) -> (* if terms got equal, nnew is empty *)
        let nnew' = List.map N.normalize nnew in (
        if nnew <> [] then add_rewrite_trace n rs (L.hd nnew');
        (NS.add_list n' irrdcbl, NS.add_list nnew' news)
    )
 in NS.fold rewrite cs (NS.empty (), NS.empty ())
;;  
   
let rewrite rr = St.take_time St.t_rewrite (rewrite rr)

let reduced rr ns =
  let (irred, news) = rewrite rr ns in NS.add_all news irred
;;

(* * SUCCESS CHECKS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let saturated ctx (rr,ee) cc =
 let covered n =
  let s,t = N.rule n in
  let s',t' = Rewriting.nf rr s, Rewriting.nf rr t in
  if not !(settings.unfailing) then s' = t'
  else
    let str = termination_strategy () in
    let d = !(settings.d) in
    s' = t' || Ground.joinable ctx str (rr, ee, !(settings.ac_syms)) (s',t') d
 in NS.for_all covered cc
;;

let succeeds ctx (rr,ee) cc gs =
  let joinable (s,t) = Rewriting.nf rr s = (Rewriting.nf rr t) in
  if not (NS.is_empty gs) then (
    let fixed (u,v) = joinable (u,v) || Subst.unifiable u v in
    if NS.exists fixed gs then (
      if !(settings.d) then (
        let g = List.find fixed (NS.to_list gs) in
        Format.printf "joined goal %a\n" Rule.print g);
      Some Proof)
    else None)
  else if not (saturated ctx (rr,ee) cc) then None
  else
    if !(settings.unfailing) then
      Some (GroundCompletion (rr, Ground.add_ac ee !(settings.ac_syms)))
    else Some (Completion rr)
;;

let succeeds ctx re cc = St.take_time St.t_success_check (succeeds ctx re cc)

(* * SELECTION * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let log_select cc ss =
  F.printf "select %i from %i:\n%a\n%!" (List.length ss) (NS.size cc)
     Rules.print ss

let select_count i = !(settings.n)

(* selection of small new nodes *)
let select k cc thresh =
 let k = if k = 0 then select_count !(St.iterations) else k in
 let aa = NS.sort_smaller_than thresh cc in
 let aa,aa' = Listx.split_at_most k aa in 
 let pp = NS.diff_list cc aa in 
 if !(settings.d) then log_select cc aa;
 (* remember smallest terms for divergence estimate *)
 let m = L.fold_left (fun m n -> min m (R.size (N.rule n))) 20 aa in
 sizes := m :: !sizes;
 (aa,pp)
;;

let select_for_restart cc =
  let k = !(St.restarts) * 2 in
  fst (select k (NS.diff_list cc !(settings.es)) 30)

let select ?(k=0) cc =
  St.take_time St.t_select (select k cc)

(* * CRITICAL PAIRS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let eqs_for_overlaps ee =
  let use_for_overlaps n = let s,t = N.rule n in not (Term.is_subterm s t) in
  let ee' = NS.filter use_for_overlaps (NS.symmetric ee) in
  NS.variant_free ee'
;;

let cp_cache : (Rule.t * Rule.t, Rules.t) Hashtbl.t = Hashtbl.create 256

let cps n1 n2 =
  try Hashtbl.find cp_cache (n1,n2)
  with Not_found -> (
    let cps = List.map N.normalize (N.cps n1 n2) in
    Hashtbl.add cp_cache (n1,n2) cps;
    cps)
;;

(* get overlaps for rules rr and active nodes cc *)
let overlaps rr aa =
 let aa_for_ols = NS.to_list (eqs_for_overlaps aa) in
 let ns = if !(settings.unfailing) then rr @ aa_for_ols else rr in
 NS.of_list [ n | n1 <- ns; n2 <- ns; n <- cps n1 n2 ]
;;

let overlaps rr = St.take_time St.t_overlap (overlaps rr)

(* goal only as outer rule *)
let overlaps_on rr aa gs =
 let ns = rr @ (NS.to_list (eqs_for_overlaps aa)) in
 let gs_for_ols = NS.to_list (eqs_for_overlaps gs) in
  NS.of_list [ n | r <- ns; g <- gs_for_ols; n <- cps r g ]
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
 L.iter (fun n -> assert_weighted (oriented (N.rule n)) 1) cc
;;

let c_not_oriented ctx cc =
 let exp (l,r) = (!! (C.find_rule (l,r))) <&> (!! (C.find_rule (r,l))) in
 L.iter (fun n -> assert_weighted (exp (N.rule n)) 1) cc
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
    let b = big_or ctx [ C.find_rule (N.rule rl) | rl <- cc;
                                                   reduces_st (N.rule rl)] in
    Hashtbl.add reducible j b;
    b
  )
;;

let is_reducible ctx cc = St.take_time St.t_tmp2 (is_reducible ctx cc)

let rlred ctx cc (s,t) =
  let ccs = L.fold_left (fun ccs n -> N.flip n :: ccs) cc cc in
  let j = idx (s,t) in
  let redcbl rl =
    let i = idx rl in (
    let red = Rewriting.reducible_with [rl] in
    let is_rule (l,r) = Rule.is_rule (l,r) && (not (Term.is_subterm l r)) in
    let b = is_rule rl && (red t || red s) in
    Hashtbl.add redc (j, i) b; b)
  in big_or ctx [ C.find_rule rl | rl <- ccs; redcbl (N.rule rl) ]
;;

let c_red ctx cc =
  L.iter (fun rl -> require (rlred ctx cc (N.rule rl))) cc
;;

let c_red ctx = St.take_time St.t_cred (c_red ctx)

let c_cpred ctx cc =
  Hashtbl.clear reducible;
  let ccsymm = L.fold_left (fun ccs n -> N.flip n :: ccs) cc cc in
  let rs = [ N.rule n | n <- ccsymm; Rule.is_rule (N.rule n) ] in
  let rule, red = C.find_rule, is_reducible ctx ccsymm in
  let c2 = [ rule rl <&> (rule rl') <=>> (red st) | rl <- rs; rl' <- rs;
                                             st <- O.nontrivial_cps rl rl' ] in
  L.iter (fun c -> ignore (assert_weighted c 2)) c2;
;;

let c_cpred ctx = St.take_time St.t_ccpred (c_cpred ctx)

let c_max_red ctx cc =
  L.iter (fun rl -> assert_weighted (rlred ctx cc (N.rule rl)) 1) cc
;;


let c_max_goal_red ctx cc gs =
  NS.iter (fun g -> assert_weighted (rlred ctx cc (N.rule g)) 1) gs
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
 L.iter considered [ n | n <- ns; not (N.is_trivial n)];
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

(* block list of previously obtained TRSs *)
let rec block_trss ctx rrs cc = 
  let not_r rr = !! (big_and ctx [ C.find_rule r | r <- rr ]) in
  big_and ctx [ not_r rr | rr,_ <- rrs; rr <> [] ]
;;

(* find k maximal TRSs *)
let max_k ctx cc gs =
  let k = !(settings.k) !(St.iterations) in
  let cc_symm = NS.to_list (NS.symmetric cc) in 
  if !(settings.d) then F.printf "K = %i\n%!" k;
  let rec max_k acc ctx cc n =
    if n = 0 then List.rev acc (* return TRSs in sequence of generation *)
    else (
      require (block_trss ctx acc cc);
      let sat_call = if use_maxsat () then max_sat else check in
      if St.take_time St.t_sat sat_call ctx then (
        let m = get_model ctx in
        let c = if use_maxsat () then get_cost m else 0 in
        let is_rl n = 
          let rl = N.rule n in eval m (C.find_rule rl) && (not (Rule.is_dp rl))
        in
        let rr = [ n | n <- cc_symm; is_rl n ] in
        max_k ((rr, c) :: acc) ctx cc (n-1))
     else (
       if !(settings.d) then F.printf "no further TRS found\n%!"; 
       if (n = k && L.length !(settings.strategy) > 1) then
         raise (Restart (select_for_restart cc));
       acc))
   in
   C.store_rule_vars ctx cc_symm;
   if has_comp () then NS.iter (ignore <.> (C.store_eq_var ctx)) cc;
   let s = termination_strategy () in
   (* FIXME: restrict to actual rules?! *)
   St.take_time St.t_orient_constr (S.assert_constraints s 0 ctx) cc_symm;
   push ctx; (* backtrack point for Yices *)
   require (S.bootstrap_constraints 0 ctx cc_symm);
   search_constraints ctx cc gs;
   let trss = max_k [] ctx cc k in
   pop ctx; (* backtrack: get rid of all assertions added since push *)
   trss
;;

let max_k ctx = St.take_time St.t_maxk (max_k ctx)

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
let stuck_state es gs =
 (* no progress measure *)
 let h = Hashtbl.hash (NS.size es, es, gs) in
 let rep = List.for_all ((=) h) !hash_iteration in
 hash_iteration := h :: !hash_iteration;
 if List.length (!hash_iteration) > 20 then
   hash_iteration := Listx.take 20 !hash_iteration;
 if rep && !(settings.d) then F.printf "Restart: repeated iteration state\n%!";
 (* smallest equation produced in last 6 iteration was always > 17 *)
 (*let last6 = Listx.take (min 6 (L.length !sizes)) !sizes in
 let deg = L.length !sizes > 10 && L.for_all (fun x -> x > 17) last6 in
 if deg && !(settings.d) then F.printf "Restart: degenerated\n%!";
 *)
 (* iteration/size bound*)
 let max = !(St.iterations) > max_iterations () in
 if max && !(settings.d) then F.printf "Restart: maximum iterations reached\n";
 rep || (*deg || *)max
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
  let s = S.to_string !(settings.strategy) in
  if !(settings.d) then (
   F.printf "Start iteration %i with %i equations:\n %a\n%!"
     !St.iterations (NS.size aa) NS.print aa;
   if !St.goals > 0 then
   F.printf "\nand %i goals:\n%a%!\n"
     !St.goals NS.print gs;
   F.printf "%s\n%!" (Yojson.Basic.pretty_to_string 
    (Statistics.json s (!(settings.k) i) (select_count i))))
;;

let store_trs ctx j rr c =
  let rr_index = C.store_trs rr in
  (* for rewriting actually reduced TRS is used; have to store *)
  let rr_reduced = Variant.reduce rr in
  C.store_redtrs rr_reduced rr_index;
  C.store_rule_vars ctx rr_reduced; (* otherwise problems in norm *)
  if has_comp () then C.store_eq_vars ctx rr_reduced;
  if !(settings.d) then log_max_trs j rr rr_reduced c;
  rr_index
;;

let non_gjoinable ctx ns rr =
  let ac_syms = !(settings.ac_syms) in
  let keep n =
    (* to-subterm rules can always be oriented, no need for complicated join *)
    let is_to_sub (l,r) = Term.is_subterm r l in 
    let sys = rr,[],ac_syms in
    let s = termination_strategy () in
    let d = !(settings.d) in
    is_to_sub n || is_to_sub (Rule.flip n) || Ground.non_joinable ctx s sys n d
  in
  let ns' = NS.filter keep ns in
(*  NS.subsumption_free ns' *) (* expensive *)
  ns'
;;

let non_gjoinable ctx ns = St.take_time St.t_gjoin_check (non_gjoinable ctx ns)

let rec phi ctx aa gs =
  if stuck_state aa gs then
    raise (Restart (select_for_restart aa));
  set_iteration_stats aa gs;
  let process (j, acc, gs) (rr,c) =
    let trs_n = store_trs ctx j rr c in
    let rewriter = new Rewriter.rewriter (C.redtrs_of_index trs_n) in
    let irred, red = rewrite rewriter aa in (* rewrite eqs wrt new TRS *)
    let s = Unix.gettimeofday () in
    let irred = NS.filter N.not_increasing (NS.symmetric irred) in
    St.t_tmp2 := !(St.t_tmp2) +. (Unix.gettimeofday () -. s);
    let cps = reduced rewriter (overlaps rr irred) in (* rewrite CPs *)
    let nn = NS.diff (NS.add_all cps red) aa in (* only new ones *)
    let sel, rest = select nn 200 in
    (* FIXME where to move this variable registration stuff? *)
    if has_comp () then NS.iter (ignore <.> (C.store_eq_var ctx)) rest;
    let rr,ee = rr, NS.to_list irred in
    let gcps = reduced rewriter (overlaps_on rr irred gs) in (* rewrite goal CPs *)
    let gg = fst (select ~k:2 gcps 30) in
    match succeeds ctx (rr, ee) (NS.add_list !(settings.es) cps) gs with
       Some r -> raise (Success r)
     | None -> j+1, NS.add_list sel acc, NS.add_list gg gs
  in
  try
    let rrs = max_k ctx aa gs in
    let _, aa', gs' = L.fold_left process (0, NS.empty (), gs) rrs in
    let aa' = NS.add_all aa' aa in
    phi ctx aa' gs'
  with Success r -> r
;;

let init_settings fs es =
 settings.ac_syms := Ground.ac_symbols es;
 settings.d := !(fs.d);
 St.iterations := 0;
 settings.n := !(fs.n);
 settings.strategy := !(fs.strategy);
 settings.tmp := !(fs.tmp);
 settings.es := es;
 last_time := Unix.gettimeofday ();
 last_mem := St.memory ()
;;

let remember_state es gs =
 let h = Hashtbl.hash (termination_strategy (), es,gs) in
 if h = !hash_initial then raise Fail;
 hash_initial := h
;;

let termination_output = function
  GroundCompletion (trs,_) -> (
    let s = termination_strategy () in
    try
      F.printf "TERMINATION PROOF:\n";
      assert (Termination.check s trs !(settings.json)) 
    with _ -> F.printf "(sorry, no proof output for termination strategy)\n%!")
  | _ -> () 
;;


(* main ckb function *)
let rec ckb fs es gs =
 (* store initial state to capture*)
 remember_state es gs;
 (* init state *)
 let ctx = mk_context () in
 let es0 = L.map N.normalize es in
 try
  init_settings fs es0;
  let ctx = mk_context () in
  let ns0 = NS.of_list es0 in
  L.iter (fun s -> Strategy.init s 0 ctx es0) (Listx.unique (t_strategies ()));
  let res = phi ctx ns0 (NS.of_list gs) in
  if !(fs.output_tproof) then termination_output res;
  del_context ctx;
  res
 with Restart es_new -> (
  if !(settings.d) then Format.printf "restart\n%!";
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
  ckb fs (es_new @ es0) gs)
