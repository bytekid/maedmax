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

let log_select cc ss thresh =
  let sorted = NS.sort_size_age (NS.smaller_than thresh cc) in
  let pnode f n =
    F.fprintf f "%a  (%i) (%i)" Lit.print n (Nodes.age n) (Lit.size n)
  in
  let pl = Formatx.print_list pnode "\n " in
  F.printf "select %i from %i:\n%a\n%!" (L.length ss) (L.length sorted) pl ss;
  if debug 1 then
    F.printf "all:\n%a\n%!" pl sorted
;;

let init es0 gs0 =
  all_nodes := [ e, Lit.size e | e <- es0 ];
  Hashtbl.clear all_nodes_set;
  ignore (NS.add_list es0 all_nodes_set);
  (* pseudo-selected, but still valuable *)
  if !(S.do_proof) = Some SelectionTrace then
    SelectionTrace.log (es0 @ gs0) es0
;;

let shape_changed es =
  let es = NS.to_list es in
  let shape = A.problem_shape (L.map Lit.terms es) in
  !settings.auto && shape <> !(A.shape) && shape <> NoShape
;;

let yes _ = true

let get_oldest_max_from accept nodelist onodeset max maxmax (aa,rew) =
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
          if s' = t' || NS.mem aa n then
            get_oldest acc max (k+1)
          else if size_n > max || not (accept n) then
            get_oldest (na :: acc) max (k+1)
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

let get_old_nodes_from accept nodeset onodeset maxsize aarew n =
  let maxmaxsize = maxsize + 6 in
  let rec get_old_nodes n =
    if n = 0 then []
    else match get_oldest_max_from accept nodeset onodeset maxsize maxmaxsize aarew with
    | Some b ->
      if debug 1 then (
        F.printf "extra age selected: %a  (%i) (%i)\n%!"
          Lit.print b (Nodes.age b) (Lit.size b)
      );
      b :: (get_old_nodes (n - 1))
    | None -> []
  in get_old_nodes n
;;

let get_old_nodes ?(accept = yes) =
  get_old_nodes_from accept all_nodes (Some all_nodes_set)
;;

let get_old_goals ?(accept = yes) = (get_old_nodes_from accept all_goals None)

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

let adjust_bounds thresh small_count =
  if small_count > 1500 then
    let delta = if thresh > 20 then 1 else 0 in
    heuristic := {!heuristic with
      soft_bound_equations = thresh - 1;
      hard_bound_equations = !heuristic.hard_bound_equations - delta}
  else if small_count < 20 then 
    heuristic := {!heuristic with soft_bound_equations = thresh + 1;
    hard_bound_equations = !heuristic.hard_bound_equations + 1};
  if debug 1 then
    Format.printf "smaller than thresh: %d, reset to %d\n%!"
      small_count !heuristic.soft_bound_equations
;;


(* selection of small new nodes *)
let select' ?(only_size = true) is_restart aarew k cc thresh =
  let k = if k = 0 then select_count !(A.iterations) else k in
  let acs = !settings.ac_syms in
  let small = NS.smaller_than thresh cc in
  if not is_restart then
    adjust_bounds thresh (List.length small);
  let small', _ = L.partition (keep acs) small in
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

let select_goals' (aa, _) k gg thresh =
 let acs = !settings.ac_syms in
 let small,_ = L.partition (keep acs) (NS.smaller_than thresh gg) in
 let sorted = NS.sort_size_unif small in
 let gg_a = fst (Listx.split_at_most k sorted) in
 let gg_p = NS.diff_list gg gg_a in
 (gg_a, gg_p)
;;


(* * SELECTION BY CLASSIFICATION * * * * * * * * * ** * * * * * * * * * * * * *)
(*let count_subterms_where pred cc n =
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

let matches = count_subterms_where Subst.is_instance_of

let unifiables = count_subterms_where Subst.unifiable*)

let count_term_cond retrieve check cc =
  let cc = [Lit.terms n | n <- cc] in
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_embedded l r) in
  let subts r = [ u, (u, r) | u <- T.subterms (fst r); not (T.is_variable u)] in
  let ts = List.concat [subts (l,r) @ subts (r,l) | l,r <- cc] in
  let idx = FingerprintIndex.create ts in
  let insts u = [ v,rl | v,rl <- retrieve u idx; check v u] in
  let inst_count n =
    let s,t = Literal.terms n in
    let insts (l, r) = if is_rule (l,r) then L.length (insts l) else 0 in 
    insts (s,t) + insts (t,s)
  in
  let norm i = (float_of_int i) /. (float_of_int (List.length cc + 1)) in 
  (fun n -> norm (inst_count n))
;;

let count_instances = count_term_cond FI.get_instances Subst.is_instance_of

let count_unifiables = count_term_cond FI.get_unifiables Subst.unifiable 

let node_features n inst_count unif_count =
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_subterm l r) in
  let s, t = Literal.terms n in
  let a  = Nodes.age n in
  let max_age = float_of_int (Nodes.max_age ()) in
  let age = (max_age -. float_of_int a) /. max_age in 
  {
    is_goal_selection = Literal.is_goal n;
    size = Rule.size (s, t);
    size_diff = abs (Term.size s - Term.size t);
    linear = Rule.linear (s, t);
    age = age;
    orientable = (is_rule (s, t), is_rule (t, s));
    duplicating = (Rule.is_duplicating (s, t), Rule.is_duplicating (t, s));
    matches = inst_count n;
    cps = unif_count n
  }
;;
(*
let node_features n inst_count unif_count =
  let fs = node_features' n inst_count unif_count in
  let fb b = if b then 1. else 0. in
  let f = float_of_int in
  [fb fs.is_goal_selection; f fs.size; f fs.size_diff; fb fs.linear;
   fs.age; fb (fst fs.orientable); fb (snd fs.orientable);
   fb (fst fs.duplicating); fb (snd fs.duplicating); fs.matches; fs.cps]
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
  let featured = [ n, node_features n inst_count @ sfs | n <- ns ] in
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
*)
let classify_random_tree n s =
  if n.age <= 0. then
    if n.size_diff <= 3 then
      false (*[[ 78.   0.]]*)
    else (* if n.size_diff > 3 *)
      if s.equations <= 223 then
        if n.matches <= 0. then
          if s.goals <= 8 then
            false (*[[ 3.  1.]]*)
          else (* if s.goals > 8 *)
            false (*[[ 11.   0.]]*)
        else (* if n.matchings > 0 *)
          true (*[[ 0.  4.]]*)
      else (* if s.equations > 223 *)
        if n.cps <= 0. then
          false (*[[ 1.  0.]]*)
        else (* if n.cps > 0 *)
          true (*[[  0.  12.]]*)
  else (* if n.age > 0 *)
    if s.equations <= 166 then
      if s.equations <= 141 then
        if n.size <= 7 then
          if n.age <= 0. then
            false (*[[ 2.  0.]]*)
          else (* if n.age > 0 *)
            true (*[[ 12.  24.]]*)
        else (* if n.size > 7 *)
          if not n.linear then
            false (*[[ 18.   1.]]*)
          else (* if n.linear > 0 *)
            false (*[[ 12.   6.]]*)
      else (* if s.equations > 141 *)
        if n.matches <= 0. then
          if n.age <= 0. then
            true (*[[  67.  160.]]*)
          else (* if n.age > 0 *)
            false (*[[ 15.   9.]]*)
        else (* if n.matchings > 0 *)
          if s.equations <= 163 then
            true (*[[  3.  54.]]*)
          else (* if s.equations > 163 *)
            false (*[[ 1.  1.]]*)
    else (* if s.equations > 166 *)
      if s.iterations <= 11 then
        if n.matches <= 0. then
          if n.size <= 8 then
            false (*[[ 37.  16.]]*)
          else (* if n.size > 8 *)
            false (*[[ 53.   4.]]*)
        else (* if n.matchings > 0 *)
          if not (fst n.duplicating) then
            true (*[[ 2.  9.]]*)
          else (* if fst n.duplicating > 0 *)
            false (*[[ 2.  0.]]*)
      else (* if s.iterations > 11 *)
        if n.age <= 0. then
          if s.goals <= 79 then
            true (*[[  7.  16.]]*)
          else (* if s.goals > 79 *)
            false (*[[ 9.  3.]]*)
        else (* if n.age > 0 *)
          true (*[[  0.  12.]]*)
;;

let classify aa =
  match !settings.select_classify with
  | None -> fun _ -> true
  | Some classify ->
    let inst_count = count_instances (NS.to_list aa) in
    let unif_count = count_unifiables (NS.to_list aa) in
    (fun n ->
      let s = SelectionTrace.state_features () in
      let n = node_features n inst_count unif_count in
      classify n s
    )
;;

let select_random aa k cc thresh =
  let classify = classify aa in
  let rec remove_nth i = function
    | [] -> failwith "Select.select_random: empty list"
    | x :: xs ->
      if i = 0 then x, xs
      else
        let y, ys = remove_nth (i - 1) xs in
        y, x :: ys
  in
  let rec take m attempts xs =
    if m = 0 || xs = [] then []
    else
      let i = Random.int (List.length xs) in
      let y = List.nth xs i in
      if classify y || attempts > List.length xs then 
        let y, ys = remove_nth i xs in
        y :: (take (m - 1) 0 ys)
      else take m (attempts + 1) xs
  in
  let _ = Random.self_init () in
  let k = if k = 0 then select_count !(A.iterations) else k in
  let small = NS.smaller_than thresh cc in
  let small', _ = L.partition (keep !settings.ac_syms) small in
  let ss = take k 0 small' in
  ss, NS.diff_list cc ss
;;

let select_by_age select_goals aarew k cc thresh =
  let k = if k = 0 then select_count !(A.iterations) else k in
  let small = NS.smaller_than thresh cc in
  adjust_bounds thresh (List.length small);
  let size_sorted = split k (NS.sort_size_age small) in
  Random.self_init();
  let min = try Lit.size (List.hd size_sorted) + 10 with _ -> 20 in
  let max = if !A.equalities > 100 then min else 200 in
  let classify = classify (fst aarew) in
  let get = if select_goals then get_old_goals else get_old_nodes in
  let aa = get ~accept:classify max aarew k in
  aa, NS.diff_list cc aa
;;

let select_by_size aarew k cc thresh =
  let k = if k = 0 then select_count !(A.iterations) else k in
  let small = NS.smaller_than thresh cc in
  adjust_bounds thresh (List.length small);
  let size_sorted = NS.sort_size_age small in
  let classify = classify (fst aarew) in
  let rec take m xs =
    if m = 0 then []
    else
      match xs with
      | [] -> []
      | y :: ys -> if classify y then y :: (take (m - 1) ys) else take m ys
  in
  (*let aa = split k size_sorted in*)
  let aa = take k size_sorted in
  let aa' = split (k - (List.length aa)) size_sorted in
  let aa_all = aa @ aa' in (* avoid that nothing is selected *)
  aa_all, NS.diff_list cc aa_all
;;

(* selection by size/age/classification*)
let select aarew cc =
  let select = match !settings.selection with
    | S.MixedSelect -> select' ~only_size:false false aarew 0 cc
    | S.RandomSelect -> select_random (fst aarew) 0 cc
    | S.AgeSelect -> select_by_age false aarew 0 cc
    | S.SizeSelect -> select_by_size aarew 0 cc
  in
  let aa, cc' = A.take_time A.t_select select !heuristic.soft_bound_equations in
  if debug 1 then
    log_select cc aa !heuristic.soft_bound_equations;
  if !(S.do_proof) = Some SelectionTrace then
    SelectionTrace.log aa (NS.to_list (fst aarew));
  aa, cc'
;;

let select_goals aarew k gg =
  let select = match !settings.selection with
    | S.MixedSelect -> select_goals' aarew k gg
    | S.RandomSelect -> select_random (fst aarew) k gg
    | S.AgeSelect -> select_by_age true aarew k gg
    | S.SizeSelect -> select_by_size aarew 0 gg
  in
  let aa, gg' = A.take_time A.t_select select !heuristic.soft_bound_goals in
  if debug 1 then
    log_select gg aa !heuristic.soft_bound_goals;
  if !(S.do_proof) = Some SelectionTrace then
    SelectionTrace.log aa (NS.to_list (fst aarew));
  aa, gg'
;;

let read_file filename =
  let chan = open_in filename in
  let rec add_lines lines =
    try add_lines (input_line chan :: lines)
    with End_of_file -> close_in chan; lines
  in
  List.fold_left (^) "" (List.rev (add_lines []))
;;

let get_classification json_file =
  let t = Unix.gettimeofday () in
  let thresh = function
  | `Int i -> float_of_int i
  | `Float f -> f
  | _ -> failwith "Select.get_classification: unexpected threshhold"
  in
  let attr att n s =
    match att with
    | `String a ->
      let f = float_of_int in
      let b2f b = if b then 1.0 else 0.0 in
      if a = "is_goal" then b2f n.is_goal_selection
      else if a = "node_size" then f n.size
      else if a = "node_size_diff" then f n.size_diff
      else if a = "is_linear" then b2f n.linear
      else if a = "age" then n.age
      else if a = "orientable_lr" then b2f (fst n.orientable)
      else if a = "orientable_rl" then b2f (snd n.orientable)
      else if a = "duplicating_lr" then b2f (fst n.duplicating)
      else if a = "duplicating_rl" then b2f (snd n.duplicating)
      else if a = "matches" then n.matches
      else if a = "cps" then n.cps
      else if a = "state_equations" then f s.equations
      else if a = "state_goals" then f s.goals
      else if a = "state_iterations" then f s.iterations
      else failwith ("Select.get_classification: unexpected attribute " ^ a)
    | _ -> failwith "Select.get_classification: unexpected attribute type"
  in
  let assoc l =
    let assoc s = List.assoc s l in
    try (attr (assoc "attr"), thresh (assoc "thresh"), assoc "leq", assoc "gt")
    with Not_found -> failwith "Select.get_classification: unexpected json"
  in
  let rec decision_tree (json : Yojson.Basic.json) n s = match json with
  | `Int c -> c
  | `Assoc l ->
    let attr_of, th, leq, gt = assoc l in
    if attr_of n s <= th then decision_tree leq n s else decision_tree gt n s
  | _ -> failwith "Select.get_classification: unexpected tree structure"
  in
  (*let rec tree_string ind (json : Yojson.Basic.json) = match json with
  | `Int c -> ind ^ (string_of_int c) ^ "\n"
  | `Assoc l ->
    let attr_of, th, leq, gt = assoc l in
    let ind = " " ^ ind in
    (*Format.printf "%s if %s <= %.2f then \n%!" ind (match List.assoc "attr" l with `String a -> a | _ -> "?") th; *)
    let leq = tree_string ind leq in
    let gt = tree_string ind gt in
    ind ^ "if " ^ (match List.assoc "attr" l with `String a -> a | _ -> "?") ^
    " <= " ^ (string_of_float th) ^ " then\n" ^ leq ^ ind ^ "else\n" ^ gt
  | _ -> failwith "Select.get_classification: unexpected tree structure"
  in*)
  let majority_vote fs n s =
    let sum = List.fold_left (+) 0 [f n s | f <- fs] in
    sum >= List.length fs / 2 (* >=: accept on draw since false neg are worse *)
  in
  let json = Yojson.Basic.from_string (read_file json_file) in
  let c = 
  match json with
  | `List tjsons -> majority_vote [decision_tree j | j <- tjsons]
  | _ -> failwith "Select.get_classification: unexpected tree representation"
  in
  A.t_tmp1 := !A.t_tmp1 +. (Unix.gettimeofday () -. t);
  c
;;
