(*** MODULES *****************************************************************)
module F = Format
module L = List
module A = Analytics
module S = Settings
module Lit = Literal
module NS = Nodes
module Ac = Theory.Ac
module T = Term
module FI = FingerprintIndex

(*** OPENS *******************************************************************)
open Prelude
open Settings
open SelectionTrace

(*** GLOBALS *****************************************************************)
let settings = ref Settings.default
let heuristic = ref Settings.default_heuristic

(* maintain list of created nodes to speed up selection by age *)
let all_nodes = ref []
let all_nodes_set = NS.empty ()
let all_goals = ref []


(*** FUNCTIONS ***************************************************************)
let ac_eqs () = [ Variant.normalize_rule e | e <- Ac.eqs !settings.ac_syms ]

let debug d = !settings.debug >= d

let log_select cc ss =
  let pnode f n =
    F.fprintf f "%a  (%i) (%i)" Lit.print n (Nodes.age n) (Lit.size n)
  in
  let plist = Formatx.print_list pnode "\n " in
  F.printf "select %i from %i:\n%a\n%!" (L.length ss) (L.length cc) plist ss;
  if debug 1 then
    F.printf "all:\n%a\n%!" plist cc
;;

let shape_changed es =
  let es = NS.to_list es in
  let shape = A.problem_shape (L.map Lit.terms es) in
  !settings.auto && shape <> !(A.shape) && shape <> NoShape
;;

let get_oldest_max_from nodelist onodeset max maxmax (aa,rew) =
  let rec get_oldest acc max k =
    if k > 5000 then (
      nodelist := List.rev acc @ !nodelist;
      if max + 2 <= maxmax then get_oldest [] (max + 2) 0 else None
    ) else
      match !nodelist with
      | [] -> None
      | ((n, size_n) as na) :: ns -> (
        nodelist := ns;
        (match onodeset with Some nss -> ignore (NS.remove n nss) | None -> ());
        let s,t = Lit.terms n in
        let nfs =
          try Some (rew#nf s, rew#nf t)
          with Rewriter.Max_term_size_exceeded -> None
        in
        match nfs with
        | None -> get_oldest acc max (k+1)
        | Some ((s',rss),(t',rst)) ->
          (* check for subsumption by other literals seems not beneficial *)
          if s' = t' || NS.mem aa n then get_oldest acc max (k+1)
          else if size_n > max then get_oldest (na :: acc) max (k+1)
          else (nodelist := List.rev acc @ !nodelist; Some n)
        )
  in
  get_oldest [] max 0
;;

let select_count i = !heuristic.n

let keep acs n =
  let fs = Rule.functions (Lit.terms n) in
  L.length fs > 1 || not (Listset.subset fs acs) ||
  L.mem (Lit.terms n) (ac_eqs ()) || not (Lit.is_ac_equivalent n acs)
;;

let select_goal_similar ns =
  let ns' = [n, A.goal_similarity !settings n | n <- ns] in
  let cmp m k = if m -. k < 0. then 1 else if m -. k > 0. then -1 else 0 in
  let ns' = L.sort (fun (_, m) (_, k) -> cmp m k) ns' in
  let n, d = L.hd ns' in
  if debug 1 then
    F.printf "selected for goal similarity: %a  (%i) %.3f\n%!"
      Lit.print n (Nodes.age n) d;
  n
;;

let get_old_nodes_from nodeset onodeset maxsize aarew n =
  let maxmaxsize = maxsize + 6 in
  let rec get_old_nodes n =
    if n = 0 then []
    else match get_oldest_max_from nodeset onodeset maxsize maxmaxsize aarew with
    | Some b ->
      if debug 1 then (
        F.printf "extra age selected: %a  (%i) (%i)\n%!"
          Lit.print b (Nodes.age b) (Lit.size b)
      );
      b :: (get_old_nodes (n - 1))
    | None -> []
  in get_old_nodes n
;;

let get_old_nodes = get_old_nodes_from all_nodes (Some all_nodes_set)

let get_old_goals : int -> (NS.t * Rewriter.rewriter) -> int -> Literal.t list = (get_old_nodes_from all_goals None)

let selections = ref 0

(* ns is assumed to be size sorted *)
let select_size_age aarew ns_sorted all n =
  (*let acs, cs = !settings.ac_syms, !settings.only_c_syms in
  let little_progress = A.little_progress 3 in
  let similar n n' =
    (Lit.are_ac_equivalent acs n n') || (Lit.are_c_equivalent cs n n')
  in*)
  let rec smallest acc = function
    [] -> acc, []
  | n :: ns ->
    (*if little_progress && List.exists (similar n) acc then smallest acc ns
    else*) n :: acc, ns
  in
  let rec select ns acc n =
    (* if ns is empty then there is also no interesting old node*)
    if n <= 0 || ns = [] then L.rev acc
    else (
      selections := !selections + 1;
      if !selections mod 20 < (!heuristic.size_age_ratio / 5) then
        let acc',ns' = smallest acc ns in
        select ns' acc' (n - 1)
      else if !selections mod 26 = 0 && all <> [] then
        let b = select_goal_similar all in
        select ns (b::acc) (n - 1)
      else (
        let max =
          if !A.equalities > 100 then
            try Lit.size (List.hd ns) + 10 with _ -> 20
          else 200
        in
        match get_old_nodes max aarew 1  with
        | b :: _ ->
          if debug 1 then
            F.printf "age selected: %a  (%i) (%i)\n%!"
              Lit.print b (Nodes.age b) (Lit.size b);
          select ns (b :: acc) (n - 1)
        | _ -> select (L.tl ns) (L.hd ns :: acc) (n - 1)))
   in
   select ns_sorted [] n
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
let select' ?(only_size = true) is_restart aarew k cc thresh =
  let k = if k = 0 then select_count !(A.iterations) else k in
  let acs = !settings.ac_syms in
  let small = NS.smaller_than thresh cc in
  if not is_restart then (
    if List.length small > 1500 then
      heuristic := {!heuristic with
        soft_bound_equations = thresh - 1;
        hard_bound_equations = !heuristic.hard_bound_equations - (if thresh > 20 then 1 else 0)}
    else if List.length small < 20 then 
      heuristic := {!heuristic with soft_bound_equations = thresh + 1;
      hard_bound_equations = !heuristic.hard_bound_equations + 1};
    if debug 1 then
      Format.printf "smaller than thresh: %d, reset to %d\n%!"
        (List.length small) !heuristic.soft_bound_equations
  );
  let small',_ = L.partition (keep acs) small in
  let size_sorted = NS.sort_size_age small' in
  let aa = 
    if only_size || !heuristic.size_age_ratio = 100 then
      fst (Listx.split_at_most k size_sorted)
    else
      let size_sorted' = split k size_sorted in
      Random.self_init();
      select_size_age aarew size_sorted' (NS.smaller_than 16 cc) k
  in
  let max = try Lit.size (List.hd aa) + 4 with _ -> 20 in
  let aa =
    let kk = if !(A.shape) = Boro || !(A.shape) = NoShape then 3 else 2 in
    if A.little_progress 2 then (get_old_nodes max aarew kk) @ aa else aa
  in
  let add_goal_sim = A.little_progress 10 && size_sorted <> [] in
  let aa = if add_goal_sim then select_goal_similar size_sorted :: aa else aa in
  let pp = NS.diff_list cc aa in
  if debug 1 then log_select size_sorted aa;
  if !(S.do_proof) = Some SelectionTrace then
    SelectionTrace.log aa (NS.to_list cc);
  (aa,pp)
;;

let select_for_restart cc =
  let k = !A.restarts * !heuristic.restart_carry in
  let rew = new Rewriter.rewriter !heuristic [] [] Order.default in
  let axs = !settings.axioms in
  let ths = Listset.diff (A.theory_equations (NS.to_list cc)) axs in
  let ths' = if shape_changed cc then ths else [] in
fst (select' true (NS.empty (),rew) k (NS.diff_list cc (axs @ ths)) 30) @ ths'
;;

let select_goals' grew aa k gg thresh =
 let acs = !settings.ac_syms in
 let small,_ = L.partition (keep acs) (NS.smaller_than thresh gg) in
 let sorted = NS.sort_size_unif small in
 let gg_a = fst (Listx.split_at_most k sorted) in
 let gg_p = NS.diff_list gg gg_a in 
 if debug 1 then log_select (NS.to_list gg) gg_a;
 if !(S.do_proof) = Some SelectionTrace then
   SelectionTrace.log gg_a (NS.to_list aa);
 (gg_a, gg_p)
;;


(* * NAIVE BAYES PROBABILITY ESTIMATION  * * * * * ** * * * * * * * * * * * * *)
let count_subterms_where pred cc n =
  let tt = Unix.gettimeofday () in
  let s, t = Literal.terms n in
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_embedded l r) in
  let matched_by (s',t') =
    let matching u =
      (is_rule (s,t) && pred u s) || (is_rule (t,s) && pred u t)
    in
    List.exists matching (T.subterms s' @ (T.subterms t'))
  in
  let r = List.length (List.filter matched_by cc) in
  A.t_tmp1 := !A.t_tmp1 +. (Unix.gettimeofday () -. tt);
  r
;;

let matchings = count_subterms_where Subst.is_instance_of

let unifiables = count_subterms_where Subst.unifiable

let count_instances_in cc =
  let cc = [Lit.terms n | n <- cc] in
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_embedded l r) in
  let subts r = [ u, (u, r) | u <- T.subterms (fst r); not (T.is_variable u)] in
  let ts = List.concat [subts (l,r) @ subts (r,l) | l,r <- cc] in
  let idx = FingerprintIndex.create ts in
  let insts u = [ v,rl | v,rl <- FI.get_instances u idx; Subst.is_instance_of v u] in
  let inst_count n =
    let s,t = Literal.terms n in
    let insts (l, r) = if is_rule (l,r) then L.length (insts l) else 0 in 
    insts (s,t) + insts (t,s)
  in
  let norm i = (float_of_int i) /. (float_of_int (List.length cc + 1)) in 
  (fun n -> norm (inst_count n))
;;

let node_features n cc inst_count =
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_subterm l r) in
  let s, t = Literal.terms n in
  let a  = Nodes.age n in
  let max_age = float_of_int (Nodes.max_age ()) in
  let age = (max_age -. float_of_int a) /. max_age in 
  {
    is_goal = Literal.is_goal n;
    size = Rule.size (s, t);
    size_diff = abs (Term.size s - Term.size t);
    linear = Rule.linear (s, t);
    age = age;
    orientable = (is_rule (s, t), is_rule (t, s));
    duplicating = (Rule.is_duplicating (s, t), Rule.is_duplicating (t, s));
    matchings = inst_count n;
    cps = 0. (*norm (unifiables cc n)*)
  }
;;

let node_features n cc inst_count =
  let fs = node_features n cc inst_count in
  let fb b = if b then 1. else 0. in
  let f = float_of_int in
  let fs = [fb fs.is_goal; f fs.size; f fs.size_diff; fb fs.linear; fs.age;
   fb (fst fs.orientable); fb (snd fs.orientable);
   fb (fst fs.duplicating); fb (snd fs.duplicating); fs.matchings(*;fs.cps*)] in
   (*List.iter (fun f -> Format.printf "%.2f " f) fs; Format.printf "-\n%!";*)
  fs
;;



let svc_predict fs =
  (*let cs = [
    -1.03892064; -1.25077127e-02; 1.14185105e-02; -3.24667191e-01;
    -2.44949523e-01; -5.93731421e-01;  -5.46609473e-01;  -4.10947563e-01;
    -4.81426762e-01; 1.30578948; 7.92451989e-03;  -1.09787315e-02;
    1.52099283e-04; 6.85348305e-02
  ]
  in
  let intercept = 2.12155573 in*)
  let cs =[ -1.06793059; -1.01833444e-02; 9.15323182e-03; -2.76104995e-01;
  -2.00477817e-01; -6.25611314e-01; -4.54663792e-01; -4.23847899e-01;
  -3.98430179e-01; 1.39753975; -1.13906581e-02;   1.17095294e-04;
   7.69841867e-02]
   in
  let intercept = 1.98866295 in
  let v = List.fold_left2 (fun s c f -> s +. c *. f) intercept cs fs in
  v > 0.0
;;

let ptable : (Settings.literal, bool) Hashtbl.t = Hashtbl.create 256

let predict n fs =
  try Hashtbl.find ptable n with 
  Not_found -> (
    (*Format.printf "%.8f \n%!" (classify fs);*)
    let v = svc_predict fs in
    Hashtbl.add ptable n v;
    v)
;;

let predict_select aa ns =
  let fs = SelectionTrace.state_features () in
  let sfs = L.map float_of_int [fs.equations; fs.goals; fs.iterations] in
  let aa = NS.to_list aa in
  let inst_count = count_instances_in aa in
  let featured = [ n, node_features n aa inst_count @ sfs | n <- ns ] in
  [ n, predict n fs | n, fs <- featured ]
;;

let select_classified aa k cc thresh =
  (*Format.printf "start select\n%!";*)
  let k = if k = 0 then select_count !(A.iterations) else k in
  let small = NS.smaller_than thresh cc in
  let small', _ = L.partition (keep !settings.ac_syms) small in
  let size_sorted = NS.sort_size_age small' in
  let size_sorted_pred = predict_select aa size_sorted in
  let aa = Listx.take_at_most k [ e | e, p <- size_sorted_pred; p] in
  (*log_select size_sorted aa;*)
  aa, NS.diff_list cc aa
;;

let select_random k cc thresh =
  Random.self_init ();
  let rec remove_nth i = function
    | [] -> failwith "Select.select_random: empty list"
    | x :: xs ->
      if i = 0 then x, xs
      else
        let y, ys = remove_nth (i - 1) xs in
        y, x :: ys
  in
  let rec take m xs =
    if m = 0 || xs = [] then []
    else
    let y, ys = remove_nth (Random.int (List.length xs)) xs in
    y :: (take (m - 1) ys)
  in
  let k = if k = 0 then select_count !(A.iterations) else k in
  let small = NS.smaller_than thresh cc in
  let small', _ = L.partition (keep !settings.ac_syms) small in
  let aa = take k small' in
  (*log_select size_sorted aa;*)
  aa, NS.diff_list cc aa
;;


let select rew cc =
  let thresh = !heuristic.soft_bound_equations in
  A.take_time A.t_select (select' ~only_size:false false rew 0 cc) thresh
;;

let select_goals gr aa k cc =
  A.take_time A.t_select (select_goals' gr aa k cc) !heuristic.soft_bound_goals
;;

(* selection by size + classification*)
let select rew cc =
  let select = match !settings.selection with
    | S.SizeAgeSelect -> select' ~only_size:false false rew 0 cc
    | S.ClassifiedSelect -> select_classified (fst rew) 0 cc
    | S.RandomSelect -> select_random 0 cc
  in
  A.take_time A.t_select select !heuristic.soft_bound_equations
;;

let select_goals gr aa k cc =
  let select = match !settings.selection with
    | S.SizeAgeSelect -> select_goals' gr aa k cc
    | S.ClassifiedSelect -> select_classified aa k cc
    | S.RandomSelect -> select_random k cc
  in
  A.take_time A.t_select select !heuristic.soft_bound_goals
;;


