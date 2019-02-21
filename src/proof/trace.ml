(*** MODULES *****************************************************************)
module F = Format
module H = Hashtbl
module T = Term
module R = Rule
module O = Overlap
module S = Settings
module Sub = Subst

(*** TYPES *******************************************************************)
type pos = int list

type step = R.t * pos * Subst.t

type origin =
  | Initial
  | Rewrite of R.t * (step list * step list)
  | CP of R.t * int list * Subst.t * R.t

type result =
  | Reduced of R.t * (step list * step list)
  | Deleted

type direction =
  | LeftRight | RightLeft

type cpf_step = pos * R.t * direction * Subst.t * T.t

type cpf_conv = T.t * (cpf_step list)

type rule = R.t * direction

type inference =
  | Deduce of T.t * T.t * T.t
  | Delete of T.t
  | SimplifyL of R.t * T.t
  | SimplifyR of R.t * T.t
  | OrientL of R.t
  | OrientR of R.t
  | Compose of R.t * T.t
  | Collapse of R.t * T.t

(*** GLOBALS *****************************************************************)
let trace_table : (R.t, origin * int) H.t = H.create 128
let children_table : (R.t, result) H.t = H.create 128
let goal_trace_table : (R.t, origin * int) H.t = H.create 128
let deleted : R.t list ref = ref []

let count = ref 0

(*** FUNCTIONS ***************************************************************)
let root = []

let rl_sub (rl, _, s) = (rl,s)

let parents = function
  | Initial -> []
  | Rewrite (p, (lstps, rstps)) -> (p, []) :: (List.map rl_sub (lstps @ rstps))
  | CP (rl1, _, mu, rl2) -> [rl1, mu; rl2, mu]
;;

let origin_string = function
| Initial -> "Initial"
| Rewrite (p, _) -> "Rewrite(" ^ (Rule.to_string p) ^ ")"
| CP (rl1, _, _, rl2) -> "CP(" ^ (Rule.to_string rl1) ^ ","^ (Rule.to_string rl2) ^")"
;;

let children = function
  | Deleted -> []
  | Reduced (c, (lsteps, rsteps)) -> [c]
;;

let dir b = if b then LeftRight else RightLeft

let pstr = List.fold_left (fun s i -> s ^ (string_of_int i)) ""

let print (s, ss) = 
  F.printf "%a\n%!" T.print s;
  let rec print = function
    | [] -> ()
    | (p, rl, d, _, t) :: steps -> (
      let ds = if d = LeftRight then "->" else "<-" in
      F.printf " %s %a (%a at %s)\n%!" ds T.print t R.print rl (pstr p);
      print steps)
  in print ss
;;

let print_all c = List.iter print c

let rec print_steps = function
  | [] -> ()
  | (rl, p) :: ss ->
   F.printf " -> using %a at %s\n" R.print rl (pstr p);
   print_steps ss
;;

(* keep first origin for equation to avoid cycles *)
let add eq o = if not (H.mem trace_table eq) then
  let c = !count in
  count := c + 1;
  if S.do_proof_debug () then
    F.printf "ADDING %i:%a %s\n" c R.print eq (origin_string o);
  H.add trace_table eq (o, c)
;;

let gadd g o =
  if not (H.mem goal_trace_table g) then (
    let c = !count in
    count := c + 1;
    (*if S.do_proof_debug () then
      F.printf "ADDING GOAL %i:%a %s\n" c R.print g (origin_string o);*)
    H.add goal_trace_table g (o, c))
;;

let clear _ =
  H.clear trace_table;
  H.clear goal_trace_table;
  H.clear children_table;
  count := 0;
  deleted := []
;;

let add_initials eqs = List.iter (fun e -> add e Initial) eqs

let add_overlap eq (rl1, p, rl2, mu) = add eq (CP (rl1, p, mu, rl2))

let add_rewrite eq eq0 steps =
  add eq (Rewrite (eq0, steps));
  H.add children_table eq0 (Reduced (eq, steps))
;;

let add_delete eq =
  if not (H.mem children_table eq) then
    H.add children_table eq Deleted
;;

let add_initial_goal eqs = List.iter (fun e -> gadd e Initial) eqs

let add_overlap_goal eq (rl1, p, rl2, mu) = gadd eq (CP (rl1, p, mu, rl2))

let add_rewrite_goal eq eq0 steps = gadd eq (Rewrite (eq0,steps))

let trace_goal g =
  try H.find goal_trace_table g
  with Not_found ->
    Format.printf "trace goal %a\n%!" Rule.print g;
    failwith "Trace.trace_goal: not found"
;;

let trace_eq e =
  try H.find trace_table e
  with Not_found -> failwith "Trace: equation not found"
;;

let ancestors eqs = 
  let rec ancestors acc = function
    | [] -> acc
    | eq :: eqs ->
      try
        let eq = Variant.normalize_rule eq in
        if List.mem eq (List.map fst acc) then
          ancestors acc eqs
        else
          let o = fst (trace_eq eq) in
          let ps = List.map fst (parents o) in
          let acc' = ancestors acc (Listset.diff ps [eq | eq, _ <- acc]) in
          let xs = List.map fst acc' in
          assert (List.length xs = List.length (Listx.unique xs));
          let acc'' = acc' @ [eq, o] in
          ancestors acc'' (Listset.diff eqs (List.map fst acc''))
      with Not_found -> (
        F.printf "no origin found for %a\n%!" R.print eq;
        failwith "Trace.of_equation: equation unknown")
  in
  ancestors [] eqs
;;

(* Get renaming that renames first to second rule *)
let rename_to (l1, r1) (l2, r2) =
  let t1, t2 = T.F(0, [l1; r1]), T.F(0, [l2; r2]) in
  try Sub.pattern_match t1 t2, true
  with Sub.Not_matched ->
    try Sub.pattern_match (T.F(0, [r1; l1])) t2, false
    with Sub.Not_matched -> (
      F.printf "%a to %a\n%!" R.print (l1, r1) R.print (l2, r2);
      failwith "Trace.rename_to: not a variant"
    )
;;

let rec last (t, steps) =
  match steps with
  | [] -> t
  | (_, _, _, _, u) :: steps' -> last (u, steps')
;;

let equation_of (t, conv) = (t, last (t, conv))

let flip = function LeftRight -> RightLeft | _ -> LeftRight

(* Revert a cpf conversion *)
let rev (t, steps) =
  let rec rev (t, steps) =
    match steps with
    | [] -> t,[]
    | (p, rl, d, sub, u) :: ss ->
      let v, ss' = rev (u,ss) in
      v, ss' @ [p, rl, flip d, sub, t]
  in
  let u, steps_rev = rev (t,steps) in
  assert (last (t, steps) = u);
  u, steps_rev
;;

let rev_unless conv b = if b then conv else rev conv

let subst_conversion sub (t,steps) =
  let subst_step (p, rl, d, tau, u) =
    (p, rl, d, Subst.compose tau sub, T.substitute sub u)
  in
  T.substitute sub t, List.map subst_step steps
;;

let subst_print =
  let vname = Signature.get_var_name in
  let print_binding (x, t) = F.printf "  %s -> %a\n" (vname x) T.print t in
  List.iter print_binding
;;

(* Given a conversion for s = t where u = v or v = u occurs produce a conversion
   for u = v using s = t or t = s. *)
let solve (s, steps) (u, v) goals =
  if S.do_proof_debug () then
    (F.printf "LOOK FOR %a IN: \n" R.print (u, v); print (s, steps));
  let t = last (s, steps) in
  let rec solve steps_bef s' = function
    | [] -> failwith "Trace.solve: equation not found"
    | (p, rl, d, sub, t') :: steps_aft ->
      if rl <> (u, v) && rl <> (v, u) then
        solve ((p, rl, flip d, sub, s') :: steps_bef) t' steps_aft
      else (
        let is_instance g = R.is_instance g (s,t) in
        if S.do_proof_debug () && not (List.exists is_instance goals) then
          F.printf "no instance: %a\n %!" R.print (s,t);
        let oriented_rl = if d = LeftRight then rl else R.flip rl in
        let res step = s', steps_bef @ [step] @ (snd (rev (t', steps_aft))) in
        if (s', t') = oriented_rl then
          let st_step = root, (s, t), LeftRight, Sub.empty, t in
          rev_unless (res st_step) ((s', t') = (u, v)), Sub.empty
        else (
          if S.do_proof_debug () then
            F.printf "INSTANTIATE  %a TO %a\n%!" R.print oriented_rl
              R.print (s', t');
          let tau = R.instantiate_to oriented_rl (s', t') in
          assert ((R.substitute tau oriented_rl) = (s', t'));
          let st_step = root, (s, t), LeftRight, tau, t in
          assert (equation_of (res st_step) = (s', t'));
          let uv_tau = R.substitute tau (u, v) in
          let conv = rev_unless (res st_step) (uv_tau = (s', t')) in
          if S.do_proof_debug () then (
            F.printf "SUBSTITUTE TO %a\n%!" R.print (equation_of conv);
            subst_print tau;
          );
          conv, tau
        )
      )
 in
 solve [] s steps
;;

let flip_unless keep_dir d = if keep_dir then d else flip d

let normalize rl d =
  let rl', kept = Variant.normalize_rule_dir rl in
  rl', if kept then d else flip d 
;;

let rewrite_conv t steps =
  let step_conv (t, acc) (rl, p, sub) =
    try
      let u, _ = Rewriting.step_at_with t p rl in
      let rl', d' = normalize rl LeftRight in
      u, (p, rl', d', sub, u) :: acc
    with _ -> failwith "Trace.rewrite_conv: no match"
  in
  List.rev (snd (List.fold_left step_conv (t, []) steps))
;;

let rewrite_conv' t steps =
  let step_conv (t, acc) (rl, p, sub, u) =
  try
    let rl', d' = normalize rl LeftRight in
    u, (p, rl', d', sub, u) :: acc
  with _ -> failwith "Trace.rewrite_conv: no match"
  in
  List.rev (snd (List.fold_left step_conv (t, []) steps))
;;

let the_overlap r1 r2 p =
  match O.overlap_between_at r1 r2 p with
    | Some o -> o 
    | _ -> failwith "Trace.the_overlap: no overlap"
;; 

(* Produce conversion for single equation given its origin *)
let conversion_for (s, t) o =
  if S.do_proof_debug () then
    F.printf "\n CONVERSION FOR %a\n%!" R.print (s, t);
  match o with
  | Initial -> s, []
  | CP (r1, p, mgu, r2) -> (* r1 is inside, r2 outside *)
    let s', t' = O.cp_of_overlap (r1, p, r2, mgu) in
    let ren, keep_dir = rename_to (s',t') (s,t) in
    let u = T.substitute ren (T.substitute mgu (fst r2)) in
    let r1, d1 = normalize r1 RightLeft in
    let r2, d2 = normalize r2 LeftRight in
    let s', t' = R.substitute ren (s', t') in
    (* FIXME: extend mgu for variables on other side? *)
    let conv = s', [(p, r1, d1, mgu, u); (root, r2, d2, mgu, t')] in
    let v, conv = rev_unless conv keep_dir in
    if S.do_proof_debug () then (
      F.printf "\ndeduce conversion for %a %s:\n%!"
        R.print (s', t') (if keep_dir then "" else "(flipped)");
     print (v, conv)
    );
    v, conv
  | Rewrite ((s0, t0), (ss, ts)) ->
    (*assert (snd (Variant.normalize_rule_dir (s,t))); not necessarily *)
    let sconv = rewrite_conv s0 ss in
    let tconv = rewrite_conv t0 ts in
    let ren, keep_dir = rename_to (last (s0, sconv), last (t0, tconv)) (s, t) in
    let s0f, t0f = R.substitute ren (s0, t0) in
    let _, sconv = subst_conversion ren (s0, sconv) in
    let _, tconv = subst_conversion ren (t0, tconv) in
    let st_step = (root, (s0, t0), LeftRight, ren, t0f) in
    let u = last (s0f, sconv) in
    assert ((keep_dir && u = s) || (not keep_dir && u = t));
    let _, rsconv = rev (s0f, sconv) in
    let conv = rsconv @ st_step :: tconv in
    let v, conv = if keep_dir then (s, conv) else rev (t, conv) in
    assert (last (v, conv) = t);
    if S.do_proof_debug () then (
      F.printf "\nrewrite conversion for %a (%i):\n%!"
        R.print (s,t) (if keep_dir then 1 else 0);
      print (v, conv)
    );
    v, conv
;;

(* Produce trace for equation *)
let trace_for eqs =
  if S.do_proof_debug () then (
    F.printf "\n2. TRACE FOR EQUATION\n we consider the ancestors:\n";
      List.iter (fun (a, _) -> F.printf " %a\n" R.print a) (ancestors eqs));
  [a, conversion_for a o | a, o <- ancestors eqs; o <> Initial]
;;

(* given a proven goal g with origin o, trace it back to an initial goal;
   the encountered non-initial goals are collected in goals_acc while the used
   rules are collectd in rule_acc*)
let goal_ancestors g =
  let rec goal_ancestors rule_acc goals_acc g =
    let o, i = trace_goal g in
    assert (snd (Variant.normalize_rule_dir g));
    if S.do_proof_debug () then
      F.printf "NEXT TACKLE GOAL %a:\n%!" R.print g;
    let goals_acc = (g, o) :: goals_acc in
    match o with
    (* need to reverse list of subsequent goals encountered *)
    | Initial -> Listx.unique rule_acc, goals_acc
    (* g was obtained from rewriting goal (s,t) using rule (rs,rt) *)
    | Rewrite ((s, t), (rs, rt)) ->
      assert (snd (Variant.normalize_rule_dir (s, t)));
      let rls = Listx.unique (List.map (fun (rl, _, _) -> rl) (rs @ rt)) in
      goal_ancestors (rls @ rule_acc) goals_acc (s, t)
    (* g was obtained from deduce with goal g0 using rule rl *)
    | CP (rl, _, _, g0) ->
      let g0 = Variant.normalize_rule g0 in
      let rl', _ = normalize rl LeftRight in
      goal_ancestors (rl' :: rule_acc) goals_acc g0
  in
  let g = Variant.normalize_rule g in
  goal_ancestors [] [] g
;;

(* Create conversions for a list of goals with associated origins. The goal list
  (2nd parameter) is assumed to be non-empty and already normalized *)
let rec goal_conversions gconv_acc = function
  | [] -> failwith "Trace.goal_conversions: empty list not expected"
  | ((v, w), o) :: goals -> (
    assert (snd (Variant.normalize_rule_dir (v, w)));
    let inst = R.instantiate_to (v, w) in
    let rho = match gconv_acc with [] -> Sub.empty | (vw, _) :: _ -> inst vw in
    match o with
    | Initial -> List.rev gconv_acc
    (* (v,w) was obtained from rewriting goal (s,t) using rule (rs,rt) *)
    | Rewrite ((s, t), (rs, rt)) ->
      let conv = subst_conversion rho (conversion_for (v, w) o) in
      let conv', tau = solve conv (s, t) (List.map fst gconv_acc) in
      let gconv = R.substitute tau (s, t), conv' in
      if S.do_proof_debug () then (
        F.printf "RESULTING CONVERSION for %a:\n%!" R.print (fst gconv);
        print (snd gconv)
      );
      goal_conversions (gconv :: gconv_acc) goals
    (* (v,w) was obtained from deduce with goal g0 using rule rl *)
    | CP (rl, _, _, g0) ->
      let g0 = Variant.normalize_rule g0 in
      if S.do_proof_debug () then
        F.printf "DERIVED BY DEDUCE FROM %a:\n%!" R.print g0;
      let conv = subst_conversion rho (conversion_for (v, w) o) in
      let conv', tau = solve conv g0 (List.map fst gconv_acc) in
      let gconv = R.substitute tau g0, conv' in
      if S.do_proof_debug () then (
        assert (snd (Variant.normalize_rule_dir g0));
        F.printf "RESULTING CONVERISON for %a:\n%!" R.print (fst gconv);
        print (snd gconv)
      );
      goal_conversions (gconv :: gconv_acc) goals
  )
;;

(* Given a goal g with origin o and a conversion gc for it, find all its
   ancestors and build conversions for them. *)
let all_goal_conversions gc g =
  let rls, goals = goal_ancestors g in
  rls, goal_conversions [gc] (List.rev goals)
;;

let subst_append (s, sconv) (t, tconv) =
  if S.do_proof_debug () then
    assert (Sub.unifiable (last (s, sconv)) t);
  let sigma = Sub.mgu (last (s, sconv)) t in
  subst_conversion sigma  (s, sconv @ tconv)
;;

let goal_conv (s, t) (rs, rt) =
  let t', rtconv = rev (t, rewrite_conv' t rt) in
  let pg_conv = subst_append (s, rewrite_conv' s rs) (t', rtconv) in
  equation_of pg_conv, pg_conv
;;

(* (s,t) is the goal that was proven, (rs,rt) the rules used to rewrite it to
   the common normal form, g_orig is the normalized original goal *)
let goal_proof g_orig (s, t) (rs, rt) sigma =
  if S.do_proof_debug () then (
    F.printf "\n0. ORIGINAL GOAL %a\n%!" R.print g_orig;
    F.printf "\n1. PROVEN GOAL %a\n%!" R.print (s, t);
    if sigma <> Sub.empty then F.printf "(substituted)\n%!");
  let goal_conv = goal_conv (s, t) (rs, rt) in
  if S.do_proof_debug () then
    (F.printf "2. THE GOAL CONVERSION:\n%!"; print (snd goal_conv));
  (* in case (s,t) is not the original goal we need to trace it back.
     Add original goal in case it is not yet there, replace in table to avoid
     cyclic dependencies: original goal (s,t) initially not in table produces
     (s',t') might produce (s,t), now added into table, ...*)
  let grls, gconvs =
    if (s, t) <> g_orig then all_goal_conversions goal_conv (s, t)
    else [], []
  in
  let rls = Listx.unique ([ r | r, _, _, _ <- rs @ rt] @ grls) in
  let t = trace_for rls @ [goal_conv] @ gconvs in
  if S.do_proof_debug () then (
    F.printf "\nFINAL CONVERSIONS: \n%!";
    let pconv (i, (rl, c)) = F.printf "%i. %a:\n%!" i R.print rl; print c in
    List.iter pconv (Listx.index t));
  t
;;

(* * * RUN CONSTRUCTION * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Construct a classical oKB run from a successful maedmax execution.
   TODO That may fail for the following reasons (not experienced so far):
   - an equation may have been constructed from a simplification using an
     intermediate rule which may have been oriented using a different reduction
     order.
     May be remedied by doing Deduce instead of simplify in the creation phase.
   - also the last entry in the children table may use a different TRS with a
     different reduction order.
*)

(* Given equation l = r, compute SimplifyL inferences that correspond to the
   rewrite sequence rs. The applied rules need not be oriented before, we can
   also do ordered rewriting with equations. *)
let to_rewrite_left ((l, r) as lr) rs keep_origin =
  let steps = rewrite_conv l rs in
  let rec collect acc u = function
      [] -> acc (* reversal happens in to_origins *)
    | (p, _, _, _, v) :: ss -> collect (SimplifyL ((u, r), v) :: acc) v ss
  in
  (* first step needs to be deduce if keep_origin is true *)
  match steps with
  | [] -> l, []
  | (_, _, _, _, l') :: steps' ->
    let first = if keep_origin then Deduce (l, l', r) else SimplifyL (lr, l') in
    last (l, steps), collect [first] l' steps'
;;

(* As above for SimplifyR. *)
let rec to_rewrite_right ((l, r) as lr) rs keep_origin =
  let steps = rewrite_conv r rs in
  let rec collect acc u = function
      [] -> acc (* reversal happens in to_origins *)
    | (p, _, _, _, v) :: ss -> collect (SimplifyR ((l, u), v) :: acc) v ss
  in 
  (* first step needs to be deduce if keep_origin is true *)
  match steps with
  | [] -> r, []
  | (_, _, _, _, r') :: steps' ->
    let first = if keep_origin then Deduce (r, l, r') else SimplifyR (lr, r') in
    last (r, steps), collect [first] r' steps'
;;

let later_use_exists st =
  let origin_used st = function
    | CP (r1, _, _, r2) -> r1 = st || r2 = st
    | Initial -> false
    | Rewrite (eq', _) -> st = eq'
  in  
  let rec check = function
  | [] -> false
  | (eq, o) :: es ->
    if origin_used st o then true
    else if st = eq then false (* produced again! stop*)
    else check es
  in check
;;

(* Compute Deduce and Simplify steps that gave rise to the given equations. *)
let creation_steps eqs =
  let rec steps acc = function
    | [] -> List.rev acc
    | ((s, t), o) :: es -> (
      match o with
      | Initial -> steps acc es
      | CP (r1, p, _, r2) ->
        (* rename *both* (rules not obeying variable condition make problems) *)
        let r1, r2 = R.rename r1, R.rename r2 in
        let (r1, p, r2, mgu) as o = the_overlap r1 r2 p in
        let s', t' = O.cp_of_overlap o in
        let ren, keep_dir = rename_to (s', t') (s, t) in
        let u = T.substitute ren (T.substitute mgu (fst r2)) in
        let s', t' = R.substitute ren (s, t) in
        steps (Deduce (u, s', t') :: acc) es
      | Rewrite ((s0, t0), (ss, ts)) ->
        let later_used = later_use_exists (s0,t0) es in
        let s, os = to_rewrite_left (s0, t0) ss later_used in
        let _, os' = to_rewrite_right (s, t0) ts (ss = [] && later_used) in
        steps (os' @ os @ acc) es
    )
  in
  (* do deduce before rewrite to avoid simplifying away needed equations *)
  let ds, rs = List.partition (function _, CP _ -> true | _ -> false) eqs in
  steps [] (ds @ rs)
;;

(* Compute Simplify and Delete steps that simplify away the given equations. *)
let simplify_away_steps rew ee eqs =
  let rewrite (s, t) =
    let s', rs = rew#nf s in
    let t', rt = rew#nf t in
    let rest = if s' = t' then [(s',t'), Deleted] else [] in
    ((s,t), Reduced((s', t'), (rs, rt))) :: rest
  in
  let rec simplify_steps acc = function
    | [] -> List.rev acc
    | ((s0, t0), r) :: es -> (
      match r with
      | Deleted -> simplify_steps (Delete s0 :: acc) es
      | Reduced ((s, t), (ss, ts)) ->
        (* these equations are not needed later on *)
        let keep_origin = false in
        let s, os = to_rewrite_left (s0, t0) ss keep_origin in
        let _, os' = to_rewrite_right (s, t0) ts keep_origin in
        simplify_steps (os' @ os @ acc) es
    )
  in
  simplify_steps [] (List.concat (List.map rewrite eqs))
;;

(* Orient steps for rules rr out of equation set ee *)
let orient_steps ee rr =
  let orient acc rl =
    if List.mem rl ee then OrientL rl :: acc else
    if List.mem (R.flip rl) ee then OrientR (R.flip rl) :: acc else acc
  in
  List.fold_left orient [] rr
;;

(* Collapse/SimplifyL steps for l -> r where the rewrite steps rs apply to l *)
let rec to_collapse (l, r) rs =
  let steps = rewrite_conv l rs in
  let rec collect acc u = function
    | [] -> acc (* reversal happens in caller *)
    | (p, _, _, _, v) :: ss ->
      let s = if acc=[] then Collapse ((u, r), v) else SimplifyL ((u, r), v) in
      collect (s :: acc) v ss
  in
  last (l, steps), collect [] l steps
;;

(* Compose steps for l -> r where the rewrite steps rs apply to r. *)
let rec to_compose (l, r) rs =
  let steps = rewrite_conv r rs in
  let rec collect acc u = function
      [] -> acc (* reversal happens in caller *)
    | (p, _, _, _, v) :: ss -> collect ((Compose ((l, u), v)) :: acc) v ss
  in
  last (r, steps), collect [] r steps
;;

(* Compose and collapse steps to interreduce the TRS rr. *)
let interreduce rew rls =
  let rec reduce os_acc rr ee = function
    | [] -> (List.rev os_acc, rr, ee)
    | (l, r) :: rls ->
      let r', rrs = rew#nf r in
      let l', lrs = rew#nf l in
      let _, os = to_compose (l, r) rrs in
      let _, os' = to_collapse (l, r') lrs in
      if l = l' then reduce (os' @ os @ os_acc) ee (Listset.add (l, r') rr) rls
      else reduce (os' @ os @ os_acc) ((l', r') :: ee) rr rls
  in
  reduce [] [] [] rls
;;

(* Show inference steps of a run. *)
let show_run r =
  let tp = T.print in
  let rec show = function
    | [] -> ()
    | OrientL e :: steps ->
      F.printf " orientl %a = %a\n%!" tp (fst e) tp (snd e);
      show steps
    | OrientR e :: steps ->
      F.printf " orientr %a = %a\n%!" tp (fst e) tp (snd e);
      show steps
    | Delete t :: steps ->
      F.printf " delete %a = %a\n%!" tp t tp t;
      show steps
    | Deduce (u, s, t) :: steps ->
      F.printf " deduce %a <- %a -> %a\n" tp s tp u tp t;
      show steps
    | SimplifyL ((s, t), u) :: steps ->
      F.printf " simplifyl %a = %a to %a = %a\n%!" tp s tp t tp u tp t;
      show steps
    | SimplifyR ((s, t), u) :: steps ->
      F.printf " simplifyr %a = %a to %a = %a\n%!" tp s tp t tp s tp u;
      show steps
    | Compose ((s, t), u) :: steps ->
      F.printf " compose %a -> %a to %a -> %a\n%!" tp s tp t tp s tp u;
      show steps
    | Collapse ((s, t), u) :: steps ->
      F.printf " collapse %a -> %a to %a = %a\n%!" tp s tp t tp u tp t;
      show steps
  in
  if S.do_proof_debug () then show r
;;

let print_system ee rr =
  Format.printf "EE:\n%a\nRR:\n%a\n" (Rules.print_with "=") ee Rules.print rr
;;

(* Simulate the inference steps starting from the initial equations ee0.
   Outcommented lines could serve as fault tolerance. *)
let simulate ee0 steps =
  let (<:>) = Listset.add in
  let drop, mem, tp, d = Listx.remove, List.mem, T.print, S.do_proof_debug () in
  let rec sim acc (ee_i, rr_i) steps =
    if d then
      print_system ee_i rr_i;
    match steps with
    | [] -> List.rev acc,(ee_i, rr_i)
    | z :: steps ->
      match z with
      | OrientL e ->
        if d then F.printf " orientl %a = %a\n%!" tp (fst e) tp (snd e);
        assert(mem e ee_i);
        sim (z :: acc) (drop e ee_i, e <:> rr_i) steps
      | OrientR e ->
        let rr_i' = R.flip e <:> rr_i in
        if d then F.printf " orientr %a = %a\n%!" tp (fst e) tp (snd e);
        assert (mem e ee_i);
        sim (z :: acc) (drop e ee_i, rr_i') steps
      | Delete t ->
        if d then F.printf " delete %a = %a\n%!" tp t tp t;
        sim (z :: acc) (drop (t, t) ee_i, rr_i) steps
      | Deduce (u, s, t) ->
        if d then F.printf " deduce %a <- %a -> %a\n%!" tp s tp u tp t;
        sim (z :: acc) ((s, t) <:> ee_i, rr_i) steps
      | SimplifyL ((s,t) as st, u) ->
        if d then F.printf " simplifyl %a = %a to %a = %a\n%!" tp s tp t tp u tp t;
        assert (mem st ee_i);
        sim (z :: acc) ((u, t) <:> (drop st ee_i), rr_i) steps
      | SimplifyR ((s, t) as st, u) ->
        if d then F.printf " simplifyr %a = %a to %a = %a\n%!" tp s tp t tp s tp u;
        assert (mem st ee_i);
        sim (z :: acc) ((s, u) <:> (drop st ee_i), rr_i) steps
      | Collapse ((s,t) as st,u) ->
        if d then F.printf " collapse %a -> %a to %a = %a\n%!" tp s tp t tp u tp t;
        assert (mem st rr_i);
        sim (z :: acc) ((u, t) <:> ee_i, drop st rr_i) steps
      | Compose ((s, t) as st, u) ->
        if d then F.printf " compose %a -> %a to %a -> %a\n%!" tp s tp t tp s tp u;
        assert (mem st rr_i);
        sim (z :: acc) (ee_i, (s, u) <:> (drop st rr_i)) steps
  in
  sim [] (ee0, []) steps
;;

(* Check whether equations/rules required for inferences are present.
   TODO: also check rewrite steps *)
let check ee0 steps (ee, rr) =
  let drop, mem, tp, d = Listx.remove, List.mem, T.print, S.do_proof_debug () in
  let (<:>) = Listset.add in
  let rec sim acc (ee_i, rr_i) = function
      [] -> true
    | z :: steps -> match z with
    | OrientL e ->
      if d then F.printf " orientl %a = %a\n%!" tp (fst e) tp (snd e);
      (mem e ee_i) && sim (z :: acc) (drop e ee_i, e <:> rr_i) steps
    | OrientR e ->
      if d then F.printf " orientr %a = %a\n%!" tp (fst e) tp (snd e);
      let rr_i' = R.flip e <:> rr_i in
      mem e ee_i && sim (z :: acc) (drop e ee_i, rr_i') steps
    | Delete t ->
      if d then F.printf " delete %a = %a\n%!" tp t tp t;
      mem (t, t) ee_i && sim (z :: acc) (drop (t, t) ee_i, rr_i) steps
    | Deduce (u, s, t) ->
      if d then F.printf " deduce %a <- %a -> %a\n" tp s tp u tp t;
      sim (z :: acc) ((s,t) <:> ee_i, rr_i) steps
    | SimplifyL ((s, t), u) ->
      if d then F.printf " simplifyl %a = %a to %a = %a\n" tp s tp t tp u tp t;
      let in_e = mem (s, t) ee_i in
      in_e && sim (z :: acc) ((u,t) <:> (drop (s, t) ee_i), rr_i) steps
    | SimplifyR ((s, t), u) ->
      if d then F.printf " simplifyr %a = %a to %a = %a\n" tp s tp t tp s tp u;
      let in_e = mem (s, t) ee_i in
      in_e && sim (z :: acc) ((s, u) <:> (drop (s, t) ee_i), rr_i) steps
    | Collapse ((s, t), u) ->
      if d then F.printf " collapse %a -> %a to %a = %a\n" tp s tp t tp u tp t;
      let in_r = mem (s, t) rr_i in
      in_r && sim (z :: acc) ((u, t) <:> ee_i, drop (s, t) rr_i) steps
    | Compose ((s,t),u) ->
      if d then F.printf " compose %a -> %a to %a -> %a\n" tp s tp t tp s tp u;
      let in_r = mem (s, t) rr_i in
      in_r && sim (z :: acc) (ee_i, (s, u) <:> (drop (s, t) rr_i)) steps
  in
  let _, (ee', rr') = simulate ee0 steps in
  sim [] (ee0, []) steps && Listset.equal ee ee' && Listset.equal rr rr'
;;

(* Construct a run from ee0, to obtain (an interreduced version of) (ee,rr). *)
let reconstruct_run ee0 (ee, rr, ord) =
  let rew = new Rewriter.rewriter Settings.default_heuristic rr [] ord in
  rew#add ee;
  (* 0. collect derivations for computed (ee,rr) *)
  let ee0 = [ Variant.normalize_rule e | e <- ee0 ] in
  let ancs = ancestors (ee @ rr) in
  assert ([a | a ,_ <- ancs] = Listx.unique [a | a ,_ <- ancs]);
  (* 0. create all equations needed by means of deduce and simplify  *)
  let steps0 = creation_steps ancs in
  (* 1. simulate the run so far, this results in equations ee' and rr' *)
  let steps1, (ee', rr') = simulate ee0 steps0 in
  if S.do_proof_debug () then (
    Format.printf "after creation:\n";
    print_system ee' rr');
  (* 2. by ground completeness, additional equations are subsumed/joinable;
        so compute these derivations, results in Delete or already present
        equations *)
  let ee'' = Listset.diff ee' (Rules.flip (ee @ rr) @ ee @ rr) in
  if S.do_proof_debug () then
    Format.printf "%d superfluous: %a\n" (List.length ee'') (Rules.print_with "=") ee'';
  let steps_ee = simplify_away_steps rew ee ee'' in
  (* 3. rules in rr need to be oriented  *)
  let orient_steps = orient_steps ee' (Listset.diff rr rr') in
  (* 4. interreduce the set of all rules, computing collapse/compose steps *)
  if S.do_proof_debug () then 
    Format.printf "before interreduce: \nexpected:%a\nadditional:%a\n%!"
      Rules.print rr Rules.print rr';
  let interred_steps, ee_add, rr_reduced = interreduce rew (Listset.diff rr' rr) in
  assert (Listset.subset rr_reduced rr);
  (* 5.interreduction can produce equations that should be subsumed/joinable *)
  let ss_ee' = simplify_away_steps rew ee (Listx.unique ee_add) in
  (* combine all inference steps *)
  let steps = steps1 @ orient_steps @ steps_ee @ interred_steps @ ss_ee' in
  let run, res = simulate ee0 steps in
  assert (check ee0 run res);
  if S.do_proof_debug () then (
    F.printf "initial equations: \n%a\n%!" Rules.print ee0;
    F.printf "FINAL RUN:\n%!";
    show_run run;
    F.printf "final equations: \n%a\n%!" Rules.print (fst res);
    F.printf "final rules: \n%a\n%!" Rules.print (snd res));
  run, res
;;


let ancestors_with_subst eqs = 
  let mk eq = { S.terms = eq; S.is_equality = true } in
  let rec ancestors (eq, sigma) =
    let eq = Variant.normalize_rule eq in
    let o = fst (trace_eq eq) in
    if o = Initial then [mk eq, sigma]
    else
      let ps = [p, Subst.compose tau sigma | p, tau <- parents o] in
      List.concat (List.map ancestors ps)
  in
  List.concat (List.map ancestors eqs)
;;

let goal_ancestors_with_subst (g, sigma) =
  let mk eq = { S.terms = eq; S.is_equality = false } in
  let restr subst rl = [x,t | x,t <- subst; List.mem x (Rule.variables rl)] in
  let rec goal_ancestors (g', sigma) =
    (*Format.printf "looking for ancestors of %a (substituted: %a)\n%!"
      Rule.print g' Rule.print (Rule.substitute sigma g');*)
    let g = Variant.normalize_rule g' in
    let sigma = Subst.compose (fst (rename_to g g')) sigma in
    match fst (trace_goal g) with
    | Initial -> [mk g, sigma]
    | Rewrite ((s, t), (rs, rt)) ->
      (*Format.printf " rewritew %a\n%!" Rule.print (s,t);*)
      assert (snd (Variant.normalize_rule_dir (s, t)));
      let rls = [ rl, restr (Subst.compose s sigma) rl | rl, _, s <- rs @ rt] in
      goal_ancestors ((s, t), restr sigma (s, t)) @ (ancestors_with_subst rls)
    | CP (rl, p, mu, g0) ->
      let s, t = O.cp_of_overlap (rl, p, g0, mu) in
      let ren, keep_dir = rename_to (s,t) g in
      let subst st = restr (Subst.compose mu (Subst.compose ren sigma)) st in
      (*Format.printf " CP %a %a\n%!" Rule.print g0
      Rule.print rl;
      Format.printf " CP %a %a\n%!" Rule.print (Rule.substitute mu g0)
      Rule.print (Rule.substitute mu rl);
      Format.printf " CP %a %a\n%!" Rule.print (Rule.substitute (subst g0) g0)
      Rule.print (Rule.substitute (subst rl) rl);*)
      goal_ancestors (g0, subst g0) @ (ancestors_with_subst [rl, subst rl])
  in
  Listx.unique (goal_ancestors (g, sigma))
;;

let proof_literal_instances (es, gs) = function
  | Settings.Proof ((s,t),(rs, rt), sigma) ->
    (*Format.printf "proved goal %a\n" Rule.print (s,t);*)
    let s' = last (s, rewrite_conv' s rs) in
    let t' = last (t, rewrite_conv' t rt) in
    assert (Subst.unifiable s' t');
    assert (Term.substitute sigma s' = Term.substitute sigma t');
    let rl_pos_sub = List.map (fun (rl, p, r, _) -> (rl, p, r)) in
    if (s',t') <> (s,t) then
      add_rewrite_goal (s', t') (s, t) (rl_pos_sub rs, rl_pos_sub rt);
    goal_ancestors_with_subst ((s', t'), sigma);
  | _ -> []
;;
