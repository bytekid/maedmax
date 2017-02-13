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
  | (s,_, _) :: _ -> s
;;

let constraints _ = 
 match !(settings.strategy) with 
  | [] -> failwith "no constraints found"
  | (_,cs,_) :: _ -> cs
;;

let max_constraints _ =
 match !(settings.strategy) with
  | [] -> failwith "no max constraints found"
  | (_,_,ms) :: _ -> ms
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

let t_strategies _ = L.map (fun (ts,_,_) -> ts) !(settings.strategy)

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
  if gs <> [] then (
    if List.exists joinable gs then (
      if !(settings.d) then Format.printf "joined goal\n";
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
  F.printf "SELECT: given %i %a %i\n%a\n%!" (NS.size cc) NS.print cc
    (List.length ss) Rules.print ss 

let select_count i = !(settings.n)

(* selection of small new nodes *)
let select k cc thresh = 
 let aa = NS.sort_smaller_than thresh cc in
 let aa,aa' = Listx.split_at_most k aa in 
 let pp = NS.diff_list cc aa in 
 if !(settings.d) then log_select cc aa;
 (* remember smallest terms for divergence estimate *)
 let m = L.fold_left (fun m n -> min m (R.size (N.rule n))) 20 aa in
 sizes := m :: !sizes;
 (aa,pp)
;;

let select_for_restart cc = fst (select 5 (NS.diff_list cc !(settings.es)) 30)

let select cc =
  St.take_time St.t_select (select (select_count !(St.iterations)) cc)

(* * CRITICAL PAIRS  * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let eqs_for_overlaps ee =
  let use_for_overlaps n = let s,t = N.rule n in not (Term.is_subterm s t) in
  let ee' = NS.filter use_for_overlaps (NS.symmetric ee) in
  NS.variant_free ee'
;;

let cp_cache : (Rule.t * Rule.t, Rules.t) Hashtbl.t = Hashtbl.create 256

(* get overlaps for rules rr and active nodes cc *)
let overlaps rr aa =
 let aa_for_ols = NS.to_list (eqs_for_overlaps aa) in
 let ns = if !(settings.unfailing) then rr @ aa_for_ols else rr in
 let cps n1 n2 =
   try Hashtbl.find cp_cache (n1,n2)
   with Not_found -> (
     let cps = List.map N.normalize (N.cps n1 n2) in
     Hashtbl.add cp_cache (n1,n2) cps;
     cps)
 in
 NS.of_list [ n | n1 <- ns; n2 <- ns; n <- cps n1 n2 ]
;;

 (* FIXME: no caching yet *)
let overlaps rr = St.take_time St.t_overlap (overlaps rr)

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
let search_constraints ctx cc =
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
let max_k ctx cc =
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
   search_constraints ctx cc;
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
 F.printf "TRS %i - %i: cost %i\n %a\n\n reduced: %a\n@." !St.iterations j c 
   Rules.print (Variant.rename_rules rr)
   Rules.print (Variant.rename_rules rr')
;;


(* heuristic predicate checking degeneration of run, used to trigger restart *)
let degenerated cc =
 (L.length !sizes > 10) &&
 (L.for_all (fun x -> x > 16) (Listx.take 6 !sizes))
;;

(* towards main control loop *)
let repeated_iteration_state es gs =
 let h = Hashtbl.hash (NS.size es, es, gs) in
 let r = List.for_all ((=) h) !hash_iteration in
 hash_iteration := h :: !hash_iteration;
 if List.length (!hash_iteration) > 20 then
   hash_iteration := Listx.take 20 !hash_iteration;
 if r && !(settings.d) then F.printf "repeated iteration state";
 r
;;

let set_iteration_stats aa =
  let i = !St.iterations in
  St.iterations := i + 1;
  let s = S.to_string !(settings.strategy) in
  if !(settings.d) then (
   F.printf "Start iteration %i with %a equations\n%!"
     !St.iterations NS.print aa;
   F.printf "%s\n%!" (Yojson.Basic.pretty_to_string 
    (Statistics.json s (!(settings.k) i) (select_count i))));
  St.ces := NS.size aa
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
  if repeated_iteration_state aa gs || !(St.iterations) > 30 then
    raise (Restart (select_for_restart aa));
  set_iteration_stats aa;
  let process (j,acc) (rr,c) =
    let trs_n = store_trs ctx j rr c in
    let rewriter = new Rewriter.rewriter (C.redtrs_of_index trs_n) in
    let irred, red = rewrite rewriter aa in (* rewrite eqs wrt new TRS *)
    let cps = reduced rewriter (overlaps rr irred) in (* rewrite CPs *)
    let nn = NS.diff (NS.add_all cps red) aa in (* only new ones *)
    let nn = if !(settings.unfailing) then non_gjoinable ctx nn rr else nn in
    let sel, rest = select nn 200 in
    (* FIXME where to move this variable registration stuff? *)
    if has_comp () then NS.iter (ignore <.> (C.store_eq_var ctx)) rest;
    let rr,ee = rr, NS.to_list irred in
    match succeeds ctx (rr, ee) (NS.add_list !(settings.es) cps) gs with
       Some r -> raise (Success r)
     | None -> j+1, NS.add_list sel acc
  in
  try
    let rrs = max_k ctx aa in
    let s = Unix.gettimeofday () in
    let _, acc = L.fold_left process (0,NS.empty ()) rrs in
    St.t_tmp1 := !St.t_tmp1 +. (Unix.gettimeofday () -. s);
    let aa' = NS.add_all acc aa in
    if degenerated aa' then
      raise (Restart (select_for_restart aa'));
    phi ctx aa' gs
  with Success r -> r
;;

let set_settings fs es =
 settings.ac_syms := Ground.ac_symbols es;
 settings.d := !(fs.d);
 St.iterations := 0;
 settings.n := !(fs.n);
 settings.strategy := !(fs.strategy);
 settings.tmp := !(fs.tmp);
 settings.es := es
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
  set_settings fs es0;
  let ctx = mk_context () in
  let ns0 = NS.of_list es0 in
  L.iter (fun s -> Strategy.init s 0 ctx es0) (Listx.unique (t_strategies ()));
  let res = phi ctx ns0 gs in
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
  ckb fs (L.map N.normalize (es_new @ es0)) gs)
