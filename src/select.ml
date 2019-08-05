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

module SizeOrderedNode = struct
  type t = Lit.t
  let le l l' = Lit.size l <= Lit.size l'
end

module SizeQueue = UniqueHeap.Make(SizeOrderedNode)

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
(* min size of all_nodes, max_int if unknown *)
let min_all_nodes = ref max_int

let all_goals = ref []
let min_all_goals = ref max_int


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

let add_to_all_nodes (ns, ns_sized) =
  all_nodes := L.rev_append (L.rev !all_nodes) ns_sized;
  ignore (NS.add_list ns all_nodes_set);
  if !min_all_nodes < max_int then (
    let m = List.fold_left (fun m (_, s) -> min m s) !min_all_nodes ns_sized in
    (*Format.printf "update min size to %d\n%!" m;*)
    min_all_nodes := m)
;; 

let add_to_all_goals gs_sized =
  all_goals := L.rev_append (L.rev !all_goals) gs_sized;
  if !min_all_goals < max_int then (
    let m = List.fold_left (fun m (_, s) -> min m s) !min_all_goals gs_sized in
    (*Format.printf "update min goal size to %d\n%!" m;*)
    min_all_goals := m)
;; 


let init es0 gs0 =
  all_nodes := [ e, Lit.size e | e <- es0 ];
  NS.H.clear all_nodes_set;
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

let old_select = ref 0

let consolidate_all_nodes _ =
  if !settings.ac_syms <> [] then (
  Format.printf "consolidate\n%!";
  let t = Unix.gettimeofday () in
  let ac_equiv (n, _) (n', _) = Lit.are_ac_equivalent !settings.ac_syms n n' in
  let rec drop_AC_eq acc = function
   | [] -> List.rev acc
   | n :: ns -> drop_AC_eq (n :: acc) [n' | n' <- ns; not (ac_equiv n n')]
  in
  all_nodes := drop_AC_eq [] !all_nodes;
  A.t_tmp2 := !A.t_tmp2 +. (Unix.gettimeofday () -. t)
  )
;;

let max_list_scan = ref 5000

let get_oldest_max_from accept nodelist onodeset max maxmax (aa,rew) =
  (*Format.printf "get oldest %d\n%!" max;*)
  old_select := !old_select + 1;
  let many_cps = !A.cp_counts <> [] && List.hd !A.cp_counts > 1000 in
  let rec get_oldest acc max min_size k =
    if k > !max_list_scan then (
      nodelist := List.rev acc @ !nodelist;
      if max + 2 <= maxmax then get_oldest [] (max + 2) max_int 0 else None, max_int
    ) else
      match !nodelist with
      | [] -> None, min_size
      | ((n, size_n) as na) :: ns -> (
        nodelist := ns;
        (match onodeset with Some nss -> ignore (NS.remove n nss) | None -> ());
        let s,t = Lit.terms n in
        let no_select_nf = !heuristic.no_select_nf in
        let nfs =
          if no_select_nf > 0 && !A.selections mod no_select_nf = 0 then
            Some ((s, []),(t, []))
          else
            try Some (rew#nf s, rew#nf t)
            with Rewriter.Max_term_size_exceeded -> None
        in
        match nfs with
        | None -> get_oldest acc max min_size (k+1)
        | Some ((s',rss),(t',rst)) ->
          (* check for subsumption by other literals seems not beneficial *)
          if s' = t' || NS.mem aa n then
            get_oldest acc max (min min_size size_n) (k+1)
          else (
          let ac_equiv n =
            let t = Unix.gettimeofday () in
            let ac_equiv = Lit.are_ac_equivalent !settings.ac_syms in
            let res = NS.exists (fun n' -> ac_equiv n n') aa in
            A.t_tmp3 := !A.t_tmp3 +. (Unix.gettimeofday () -. t);
            res
          in
          if false && many_cps && ac_equiv n then (
            if debug 3 then Format.printf "throw out %a \n%!" Lit.print n;
            get_oldest acc max (min min_size size_n) (k+1))
          else if size_n > max || not (accept n) then
            get_oldest (na :: acc) max (min min_size size_n) (k+1)
          else (
            nodelist := List.rev acc @ !nodelist;
            (*Format.printf "pick size %d, is %dth\n%!" size_n k;*)
            Some n, min_size)
        ))
  in
  get_oldest [] max max_int 0
;;

let select_count i = !heuristic.n i

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

let get_old_nodes_from accept (nodeset, min) onodeset maxsize aarew n =
  if !min < max_int && maxsize < !min && List.length !nodeset < !max_list_scan then
    ((*F.printf "prune: no node with maxsize %d exists, min %d (%B)\n" maxsize !min (!nodeset = []);*) [])
  else (
  let maxmaxsize = maxsize + 6 in
  let rec get_old_nodes n =
    if n = 0 then []
    else match get_oldest_max_from accept nodeset onodeset maxsize maxmaxsize aarew with
    | Some b, _ ->
      if debug 1 then (
        F.printf "extra age selected: %a  (%i) (%i) for maxsize %d/%d\n%!"
          Lit.print b (Nodes.age b) (Lit.size b) maxsize maxmaxsize
      );
      b :: (get_old_nodes (n - 1))
    | None, minsize -> (
      (*F.printf "no node with maxsize %d found, min size is %d (%B)\n%!" maxsize minsize (!nodeset = []);*)
      min := minsize;
      [])
  in get_old_nodes n)
;;

let get_old_nodes ?(accept = yes) =
  get_old_nodes_from accept (all_nodes, min_all_nodes) (Some all_nodes_set)
;;

let get_old_goals ?(accept = yes) =
  get_old_nodes_from accept (all_goals, min_all_goals) None
;;

(* ns is assumed to be size sorted *)
let select_size_age aarew ns_sorted all n =
  let acs, cs = !settings.ac_syms, !settings.only_c_syms in
  let similar n n' =
    (Lit.are_ac_equivalent acs n n') || (Lit.are_c_equivalent cs n n')
  in
  let rec smallest acc = function
    [] -> acc, []
  | n :: ns ->
    if (*little_progress &&*) List.exists (similar n) acc then smallest acc ns
    else n :: acc, ns
  in
  let rec select ns acc n =
    (* if ns is empty then there is also no interesting old node*)
    if n <= 0 || ns = [] then L.rev acc
    else (
      A.selections := !A.selections + 1;
      if !A.selections mod 20 < (!heuristic.size_age_ratio / 5) then
        let acc',ns' = smallest acc ns in
        select ns' acc' (n - 1)
      else if !A.selections mod 26 = 0 && all <> [] then
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
  if small_count > (if !A.shape = Idrogeno then 300 else 1500) then
    let delta = if thresh > 20 then 1 else 0 in
    heuristic := {!heuristic with
      soft_bound_equations = thresh - 1 (*2*);
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
  if !A.shape = Idrogeno then max_list_scan := 1000;
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
      let res = select_size_age aarew size_sorted' (NS.smaller_than 16 cc) k in
      res
  in
  let max = try (Lit.size (List.hd aa)) + 4 with _ -> 20 in
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
  let c, d = !heuristic.restart_carry in
  let k = !A.restarts * c + d in
  if debug 1 then
    Format.printf "select %d for restart (%d restarts)\n%!" k !A.restarts;
  let rew = new Rewriter.rewriter !heuristic [] [] Order.default in
  let axs = !settings.axioms in
  let ths = Listset.diff (A.theory_equations (NS.to_list cc)) axs in
  let ths' = if shape_changed cc then ths else [] in
  let cc' = NS.diff_list cc (axs @ ths) in
  fst (select' true (NS.empty (),rew) k cc' 30) @ ths'
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
let count_term_cond retrieve check cc =
  let cc = [Lit.terms n | n <- cc] in
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_embedded l r) in
  let subts r = [ u, u | u <- T.subterms (fst r); not (T.is_variable u)] in
  let ts = List.concat [subts (l,r) @ subts (r,l) | l,r <- cc] in
  let ps = [[]; [0]; [1]; [0;0]; [0;1]; [1;0]; [1;1]] in
  let idx = FingerprintIndex.create ~poss:ps ts in
  let check v u =
    let c = check v u in
    c
  in
  let insts u = [ v | v <- retrieve u idx; check v u] in
  let count_node n =
    let s, t = Literal.terms n in
    let insts (l, r) = if is_rule (l,r) then L.length (insts l) else 0 in 
    insts (s,t) + insts (t,s)
  in
  let len = float_of_int (List.length cc + 1) in
  let norm i = (float_of_int i) /. len in
  (fun n -> norm (count_node n))
;;

let count_instances = count_term_cond FI.get_instances Subst.is_instance_of

let count_unifiables = count_term_cond FI.get_unifiables Subst.unifiable

let count_instances = SelectionTrace.count_instances

let count_unifiables = SelectionTrace.count_unifiables


let node_features n inst_count unif_count =
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_subterm l r) in
  let s, t = Literal.terms n in
  let a  = Nodes.age n in
  let max_age = float_of_int (Nodes.max_age ()) in
  let age = (max_age -. float_of_int a) /. max_age in 
  let m, c = inst_count n, unif_count n in
  {
    is_goal_selection = Literal.is_inequality n;
    size = Rule.size (s, t);
    size_diff = abs (Term.size s - Term.size t);
    linear = Rule.linear (s, t);
    age = age;
    orientable = (is_rule (s, t), is_rule (t, s));
    duplicating = (Rule.is_duplicating (s, t), Rule.is_duplicating (t, s));
    matches = m;
    cps = c
  }
;;

let classification_table : (Literal.t, bool) Hashtbl.t = Hashtbl.create 256

let pqgram_table : (Term.t, float array) Hashtbl.t = Hashtbl.create 256

let pq_vec_size = 2182

let pq_grams (s, t) =
  let pqs t = 
  try Hashtbl.find pqgram_table t
  with Not_found -> (
    let v = SelectionTrace.count_named_vector t in
    let a = Array.make pq_vec_size 0.0 in
    List.iter (fun (i, c) -> a.(i) <- float_of_int c) (Listx.index v);
    Hashtbl.add pqgram_table t a;
    a)
  in (pqs s, pqs t)
;;

let classify aa =
  match !settings.select_classify with
  | None -> fun _ -> true
  | Some classify ->
    let inst_count = count_instances (NS.to_list aa) in
    let unif_count = count_unifiables (NS.to_list aa) in
    let s = SelectionTrace.state_features () in
    (fun node ->
      try Hashtbl.find classification_table node with
      Not_found ->
        let n = node_features node inst_count unif_count in
        let pqs = pq_grams (Lit.terms node) in
        let bnd =
          if !Settings.tmp > 0.01 then !Settings.tmp 
          else (*if !A.shape = Carbonio || !A.shape = Ossigeno || !A.shape = Silicio then 0.15 else*) 0.2
        in
        let c = classify ~bound:bnd n s pqs in
        Hashtbl.add classification_table node c;
        c
    )
;;

let classify aa = A.take_time A.t_tmp3 (classify aa)

let reset _ = Hashtbl.reset classification_table

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

let rec select_classified_mixed d aarew k cc thresh =
  let k = if k = 0 then select_count !(A.iterations) else k in
  let acs = !settings.ac_syms in
  let classify = classify (fst aarew) in
  let small = NS.smaller_than thresh cc in
  adjust_bounds thresh (List.length small);
  let small', _ = L.partition (keep acs) small in
  let size_sorted = NS.sort_size_age small' in
  let aa = 
    if !heuristic.size_age_ratio = 100 then
      fst (Listx.split_at_most k size_sorted)
    else
      let size_sorted' = split k size_sorted in
      Random.self_init();
      select_size_age aarew size_sorted' (NS.smaller_than 16 cc) k
  in
  let aa = List.filter classify aa in
  let max = try Lit.size (List.hd aa) + 4 with _ -> 20 in
  let aa =
    let kk = if !(A.shape) = Boro || !(A.shape) = NoShape || !(A.shape) = Xeno then 3 else 2 in
    if A.little_progress 2 then (get_old_nodes max aarew kk) @ aa else aa
  in
  let add_goal_sim = A.little_progress 10 && size_sorted <> [] in
  let aa = if add_goal_sim then select_goal_similar size_sorted :: aa else aa in
  let pp = NS.diff_list cc aa in
  (aa,pp)
;;

(* selection by size/age/classification*)
let select aarew cc =
  let select = match !settings.selection with
    | S.MixedSelect -> select' ~only_size:false false aarew 0 cc
    | S.RandomSelect -> select_random (fst aarew) 0 cc
    | S.AgeSelect -> select_by_age false aarew 0 cc
    | S.SizeSelect -> select_by_size aarew 0 cc
    | S.ClassifiedMixed -> select_classified_mixed 1 aarew 0 cc
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
    | S.ClassifiedMixed -> select_goals' aarew k gg
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
  let thresh = function
  | `Int i -> float_of_int i
  | `Float f -> f
  | _ -> failwith "Select.get_classification: unexpected threshhold"
  in
  let attr att n s (pq1, pq2) =
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
      else (
        let sz = pq_vec_size in
        try let i = int_of_string a in if i < sz then pq1.(i) else pq2.(i - sz)
        with _ -> failwith ("Select.get_classification: no attribute " ^ a))
    | _ -> failwith "Select.get_classification: unexpected attribute type"
  in
  let assoc l =
    let assoc s = List.assoc s l in
    try (attr (assoc "attr"), thresh (assoc "thresh"), assoc "leq", assoc "gt")
    with Not_found -> failwith "Select.get_classification: unexpected json"
  in
  let rec decision_tree (json : Yojson.Basic.json) = match json with
  | `Float c -> (fun _ _ _ -> c)
  | `Assoc l ->
    let attr_of, th, leq, gt = assoc l in
    let left = decision_tree leq in
    let right = decision_tree gt in
    (fun n s pq -> if attr_of n s pq <= th then left n s pq else right n s pq)
  | `Int c -> (fun _ _ _ -> float_of_int c)
  | _ -> failwith "Select.get_classification: unexpected tree structure"
  in
  (*let majority_vote fs n s =
    let sum = List.fold_left (+) 0 [f n s | f <- fs] in
    sum >= List.length fs / 2 (* >=: accept on draw since false neg are worse *)
  in*)
  let average fs len ?(bound=0.3) n s pq =
    let sum = List.fold_left (+.) 0. [f n s pq | f <- fs] in
    sum /. len >= bound
  in
  let json = Yojson.Basic.from_string (read_file json_file) in
  match json with
  | `List tjsons ->
    let len = float_of_int (List.length tjsons) in
    average [decision_tree j | j <- tjsons] len
  | _ -> failwith "Select.get_classification: unexpected tree representation"
;;
