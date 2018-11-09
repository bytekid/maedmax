(*** OPENS *******************************************************************)
open Format
open Yojson.Basic
open Settings

(*** MODULES *****************************************************************)
module L = List

(*** TYPES *******************************************************************)
type state_features = {
  equations: int;
  goals: int;
  iterations: int;
}

type equation_features = {
  is_goal: bool;
  size: int;
  size_diff: int;
  linear: bool;
  age: float; (* (max age - node age) / max age *)
  orientable: bool * bool;
  duplicating: bool * bool;
  matchings: float; (* normalized by number of nodes *)
  cps: float (* normalized by number of nodes *)
}

type selection = Literal.t * equation_features * state_features

(*** GLOBALS ********************* *******************************************)
let selections : selection list ref = ref []

(*** FUNCTIONS ***************************************************************)
let state_features _ =
  let ee = !Analytics.equalities in
  let gg = !Analytics.goals in
  let i = !Analytics.iterations in
  { equations = ee; goals = gg; iterations = i}
;;

let state_feature_string fs =
  Printf.sprintf "%d %d %d" fs.equations fs.goals fs.iterations
;;

let count_subterms_where pred cc n =
  let s, t = Literal.terms n in
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_embedded l r) in
  let matched_by n' =
    let s',t' = Literal.terms n' in
    let matching u =
      (is_rule (s,t) && pred u s) || (is_rule (t,s) && pred u t)
    in
    List.exists matching (Term.subterms s' @ (Term.subterms t'))
  in
  List.length (List.filter matched_by cc) 
;;

let matchings = count_subterms_where Subst.is_instance_of

let unifiables = count_subterms_where Subst.unifiable

let node_features n cc =
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_subterm l r) in
  let s, t = Literal.terms n in
  let a  = Nodes.age n in
  let max_age = float_of_int (Nodes.max_age ()) in
  let age = (max_age -. float_of_int a) /. max_age in
  let norm i = (float_of_int i) /. (float_of_int (List.length cc + 1)) in 
  {
    is_goal = Literal.is_goal n;
    size = Rule.size (s, t);
    size_diff = abs (Term.size s - Term.size t);
    linear = Rule.linear (s, t);
    age = age;
    orientable = (is_rule (s, t), is_rule (t, s));
    duplicating = (Rule.is_duplicating (s, t), Rule.is_duplicating (t, s));
    matchings = norm (matchings cc n);
    cps = norm (unifiables cc n)
  }
;;

let node_feature_string fs =
  let i b = if b then 1 else 0 in
  let s b = if b then "1" else "0" in
  let s2 (b1,b2) = s b1 ^ " " ^ (s b2) in 
  Printf.sprintf "%d %d %d %d %.2f %s %s %.3f %.3f"
    (i fs.is_goal) fs.size fs.size_diff (i fs.linear) fs.age (s2 fs.orientable)
    (s2 fs.duplicating) fs.matchings fs.cps
;;

let log selected all =
  let state_data = state_features () in
  let add e =
    (* exclude trivial literals that may appear just before success *)
    if fst (Literal.terms e) <> snd (Literal.terms e) then
      let e_data = node_features e all in
      selections := (e, e_data, state_data) :: !selections
  in
  List.iter add selected
;;

let report ancs =
  let used rl = List.mem rl ancs in
  let show (n, n_fs, st_fs) =
    let rl = Literal.terms n in
    let sn_fs = node_feature_string n_fs in
    let sst_fs = state_feature_string st_fs in
    let u = if used rl then 1 else 0 in
    Format.printf "-- %a\n%s %s %d\n" Rule.print rl sn_fs sst_fs u; 
  in
  List.iter show !selections
;;

let for_goal_disproof (rr, ee) (rs, rt) =
  let tfst = (fun (rl,_,_) -> rl) in
  let rrs,rrt = List.map tfst rs, List.map tfst rt in
  let ancs = Trace.ancestors (ee @ rr @ rrs @ rrt) in
  report (List.map fst ancs)
;;

let for_goal_proof es0 g_orig ((s, t), (rs, rt), sigma) =
  let g = Variant.normalize_rule g_orig in
  let ancs = Trace.goal_proof g (s, t) (rs, rt) sigma in
  report (List.map fst ancs)
;;

let for_ground_completion ee0 (rr, ee) =
  let ancs = Trace.ancestors (ee @ rr) in
  report (List.map fst ancs)
;;
