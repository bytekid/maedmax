(*** MODULES *****************************************************************)
module F = Format
module H = Hashtbl
module T = Term
module R = Rule
module O = Overlap
module S = Settings
module X = Xml

(*** TYPES *******************************************************************)
type pos = int list

type step = R.t * pos

type origin = Initial 
  | Rewrite of R.t * (step list * step list)
  | CP of R.t * int list * R.t

type result =
  | Reduced of R.t * (step list * step list)
  | Deleted

type direction = LeftRight | RightLeft

type cpf_step = pos * R.t * direction * T.t

type cpf_conv = T.t * (cpf_step list)

type rule = R.t * direction

type inference = Deduce of T.t * T.t * T.t
  | Delete of T.t
  | SimplifyL of R.t * T.t
  | SimplifyR of R.t * T.t
  | OrientL of R.t
  | OrientR of R.t
  | Compose of R.t * T.t
  | Collapse of R.t * T.t

(*** GLOBALS *****************************************************************)
let parents_table : (R.t, origin * int) H.t = H.create 128
let children_table : (R.t, result) H.t = H.create 128
let goal_trace_table : (R.t, origin * int) H.t = H.create 128
let deleted : R.t list ref = ref []
let count = ref 0

(*** FUNCTIONS ***************************************************************)
let root = []

let parents = function
   Initial -> []
 | Rewrite (p, (lsteps, rsteps)) -> p :: (List.map fst (lsteps @ rsteps))
 | CP (rl1, _, rl2) -> [rl1; rl2]
;;

let children = function
   Deleted -> []
 | Reduced (c, (lsteps, rsteps)) -> [c]
;;

let dir = function false -> RightLeft | _ -> LeftRight

let pstr = List.fold_left (fun s i -> s ^ (string_of_int i)) ""

let print (s, ss) = 
  F.printf "%a\n%!" T.print s;
  let rec print = function
    | [] -> ()
    | (p,rl,d,t) :: steps -> (
      let ds = if d = LeftRight then "->" else "<-" in
      F.printf " %s %a (%a at %s)\n%!" ds T.print t R.print rl (pstr p);
      print steps)
  in print ss
;;

let print_all = List.iter print

let rec print_steps = function
   [] -> ()
 | (rl,p) :: ss ->
   F.printf " -> using %a at %s\n" Rule.print rl (pstr p); print_steps ss 
;;

(* keep first origin for equation to avoid cycles *)
let add eq o = if not (H.mem parents_table eq) then
  let c = !count in
  count := c + 1;
  H.add parents_table eq (o,c)
;;

let gadd g o =
  if not (H.mem goal_trace_table g) then (
  let c = !count in
  count := c + 1;
  if !(S.do_proof_debug) then
    F.printf "ADDING GOAL %i:%a\n" c Rule.print g;
  H.add goal_trace_table g (o,c))
;;

let add_initials eqs = List.iter (fun e -> add e Initial) eqs

let add_overlap eq (rl1,p,rl2,_) = add eq (CP (rl1,p,rl2))

let add_rewrite eq eq0 steps =
  add eq (Rewrite (eq0,steps));
  H.add children_table eq0 (Reduced (eq,steps))
;;

let add_delete eq =
  if not (H.mem children_table eq) then
    H.add children_table eq Deleted

let add_initial_goal eqs = List.iter (fun e -> gadd e Initial) eqs

let add_overlap_goal eq (rl1,p,rl2,_) = gadd eq (CP (rl1,p,rl2))

let add_rewrite_goal eq eq0 steps = gadd eq (Rewrite (eq0,steps))

let max_eq_size = ref 0;;
let max_goal_size = ref 0;;

let variant_free ee = 
  List.fold_right (fun e ee -> if not (List.exists (Rule.variant e) ee) then e :: ee else ee) ee []
;; 

let ancestors eqs = 
  let rec ancestors acc = function
    | [] -> acc
    | eq :: eqs ->
      try
        let eq = Variant.normalize_rule eq in
        max_eq_size := max !max_eq_size (Rule.size eq);
        if List.mem eq (List.map fst acc) then
          ancestors acc eqs
        else
          let o,_ = H.find parents_table eq in
          let ps = parents o in
          let acc' = ancestors acc (Listset.diff ps [eq | eq,_ <- acc]) in
          let xs = List.map fst acc' in
          assert (List.length xs = List.length (Listx.unique xs));
          let acc'' = acc' @ [eq,o] in
          ancestors acc'' (Listset.diff eqs (List.map fst acc''))
      with Not_found -> (
        F.printf "no origin found for %a\n%!" R.print eq;
        failwith "Trace.of_equation: equation unknown")
  in ancestors [] eqs
;;

(* Return descendants in simplification. Since the equations can emerge as
   intermediate results, they need not be normalized. *)
let descendants eqs =
  let rec desc acc = function
    | [] -> acc
    | eq :: eqs ->
      (* already present and final equations can be ignored *)
      if List.mem eq (List.map fst acc) || not (H.mem children_table eq) then
        desc acc eqs
      else
        let r = H.find children_table eq in
        let acc' = desc acc (Listset.diff (children r) [eq | eq,_ <- acc]) in
        let acc'' = (eq,r) :: acc' in
        desc acc'' eqs
  in desc [] eqs
;;

(* Get renaming that renames first to second rule *)
let rename_to (l1,r1) (l2,r2) =
  let t1, t2 = T.F(0,[l1;r1]), T.F(0,[l2;r2]) in
  try Subst.pattern_match t1 t2, true
  with _ ->
    try Subst.pattern_match (T.F(0,[r1;l1])) t2, false
    with _ -> failwith "Trace.rename_to: not a variant"
;;

let rec last (t, steps) =
 match steps with
   | [] -> t
   | (_,_,_,u) :: steps' -> last (u,steps')
;;

let equation_of (t, conv) = (t, last (t,conv))

let flip = function LeftRight -> RightLeft | _ -> LeftRight

(* Revert a cpf conversion *)
let rev (t,steps) = 
 let rec rev (t, steps) =
  match steps with
    | [] -> t,[]
    | (p,rl,d,u) :: ss -> let v,ss' = rev (u,ss) in v, ss' @ [p,rl,flip d,t]
  in
  let u, spets = rev (t,steps) in
  assert (last (t,steps) = u);
  u, spets
;;

let rev_unless conv b = if b then conv else rev conv

let subst sub (t,steps) =
  let ssteps = List.map (fun (p,rl,d,u) -> (p,rl,d,T.substitute sub u)) steps in
  T.substitute sub t, ssteps
;;

let subst_print = 
  List.iter
    (fun (x,t) -> F.printf "  %s -> %a\n" (Signature.get_var_name x) T.print t)

(* Given a conversion for s = t where u = v or v = u occurs produce a conversion
   for u = v using s = t or t = s. *)
let solve (s,steps) (u,v) goals =
 if !(S.do_proof_debug) then
  (F.printf "LOOK FOR %a IN: \n" Rule.print (u,v); print (s,steps));
 let t = last (s,steps) in
 let rec solve steps_bef s' = function 
     [] -> failwith "Trace.solve: equation not found"
   | (p,rl,d,t') :: steps_aft ->
     if rl <> (u,v) && rl <> (v,u) then
       solve ((p,rl,flip d,s') :: steps_bef) t' steps_aft
     else (
       if (!(S.do_proof_debug) &&
          not (List.exists (fun g -> Rule.is_instance g (s,t)) goals)) then
         F.printf "no instance: %a\n %!" Rule.print (s,t);
       let st_step = root, (s,t), LeftRight, t in
       let res = s', steps_bef @ [st_step] @ (snd (rev (t',steps_aft))) in
       let oriented_rl = if d = LeftRight then rl else Rule.flip rl in
       if (s',t') = oriented_rl then
         rev_unless res ((s',t') = (u,v)), Subst.empty
       else (
         if !(S.do_proof_debug) then
           F.printf "INSTANTIATE  %a TO %a\n%!" Rule.print oriented_rl
             Rule.print (s',t');
         let tau = Rule.instantiate_to oriented_rl (s',t') in
         assert ((Rule.substitute tau oriented_rl) = (s',t'));
         assert (equation_of res = (s',t'));
         let conv = rev_unless res (Rule.substitute tau (u,v) = (s',t')) in
         if !(S.do_proof_debug) then (
           F.printf "SUBSTITUTE TO %a\n%!" Rule.print (equation_of conv);
           subst_print tau;
         );
     conv, tau))
 in
 let conv, tau = solve [] s steps in
 if !(S.do_proof_debug) then (
   let uv' = Rule.substitute tau (u,v) in
   assert (equation_of conv = uv');
   (F.printf "RESULT: \n"; print conv));
 conv, tau
;;

let flip_unless keep_dir d = if keep_dir then d else flip d

let normalize rl d =
  let rl', kept = Variant.normalize_rule_dir rl in
  rl', if kept then d else flip d 
;;

let rewrite_conv t steps =
  let step_conv (t,acc) (rl,p) =
  try
    let u = Rewriting.step_at_with t p rl in
    let rl', d' = normalize rl LeftRight in
    u, (p,rl',d',u) :: acc
  with _ -> failwith "Trace.rewrite_conv: no match"
  in List.rev (snd (List.fold_left step_conv (t,[]) steps))
;;

let rewrite_conv' t steps =
  let step_conv (t,acc) (rl,p,u) =
  try
    let rl', d' = normalize rl LeftRight in
    u, (p,rl',d',u) :: acc
  with _ -> failwith "Trace.rewrite_conv: no match"
  in List.rev (snd (List.fold_left step_conv (t,[]) steps))
;;

let rec last (s, ss) = match ss with
 | [] -> s 
 | [_,_,_,t] -> t 
 | (_,_,_,t) :: steps -> last (t, steps)
;;

let the_overlap r1 r2 p =
  match O.overlap_between_at r1 r2 p with
    | Some o -> o 
    | _ -> failwith "Trace.the_overlap: no overlap"
;; 

(* Produce conversion for single equation given its origin *)
let conversion_for (s,t) o = 
  if !(S.do_proof_debug) then
    F.printf "\n CONVERSION FOR %a\n%!" R.print (s,t);
  match o with
 | Initial -> s,[]
 | CP (r1, p, r2) -> (* r1 is inside, r2 outside *)
   let ((r1,p,r2,mgu) as o) = the_overlap r1 r2 p in
   let s',t' = O.cp_of_overlap o in
   let ren, keep_dir = rename_to (s',t') (s,t) in
   let u = T.substitute ren (T.substitute mgu (fst r2)) in
   let r1,d1 = normalize r1 RightLeft in
   let r2,d2 = normalize r2 LeftRight in
   let s',t' = Rule.substitute ren (s',t') in
   let conv = s', [(p, r1, d1, u); (root, r2, d2, t')] in
   let v, conv = rev_unless conv keep_dir in
   if !(S.do_proof_debug) then (
     F.printf "\ndeduce conversion for %a %s:\n%!"
       R.print (s',t') (if keep_dir then "" else "(flipped)");
     print (v,conv));
   v,conv
 | Rewrite ((s0,t0), (ss, ts)) ->
   (*assert (snd (Variant.normalize_rule_dir (s,t))); not necessarily *)
   let sconv = rewrite_conv s0 ss in
   let tconv = rewrite_conv t0 ts in
   let ren, keep_dir = rename_to (last (s0,sconv), last (t0,tconv)) (s,t) in
   let (s0f,t0f) = Rule.substitute ren (s0, t0) in
   let _,sconv = subst ren (s0,sconv) in
   let _,tconv = subst ren (t0,tconv) in
   let st_step = (root,(s0,t0),LeftRight,t0f) in
   assert ((keep_dir && last (s0f, sconv) = s) ||
           (not keep_dir && last (s0f, sconv) = t));
   let _,rsconv = rev (s0f, sconv) in
   let conv = rsconv @ st_step :: tconv in
   let v,conv = if keep_dir then (s,conv) else rev (t,conv) in
   assert (last (v,conv) = t);
   if !(S.do_proof_debug) then (
     F.printf "\nrewrite conversion for %a (%i):\n%!" R.print (s,t) (if keep_dir then 1 else 0);
     print (v,conv));
   v,conv
;;

(* Produce trace for equation *)
let trace_for eqs =
  if !(S.do_proof_debug) then (
    F.printf "\n2. TRACE FOR EQUATION\n we consider the ancestors:\n";
      List.iter (fun (a,_) -> F.printf " %a\n" R.print a) (ancestors eqs));
  [ a, conversion_for a o | a, o <- ancestors eqs; o <> Initial ]
;;

(* given a proven goal g with origin o, trace it back to an initial goal;
   conversions for the encountered non-initial goals are collected in goal_conv
   while the used rules in rule_acc (for those ancestors have to be collected
   separately). *)
let rec goal_ancestors rule_acc gconv_acc g o =
  try
    max_goal_size := max !max_goal_size (Rule.size g);
    let (v,w), keep_gdir = Variant.normalize_rule_dir g in
    let delta =
      match gconv_acc with
          [] -> Subst.empty
        | ((v',w'),_) :: _ -> Rule.instantiate_to (v,w) (v',w')
    in
    if !(S.do_proof_debug) then
      F.printf "NEXT ATTACK THE GOAL %a:\n%!" R.print (v,w);
    match o with
     (* recursion stops if we reach an initial goal; need to reverse the list
        of subsequent goals encountered *)
     | Initial ->
       Listx.unique rule_acc, List.rev gconv_acc
     (* (v,w) was obtained from rewriting goal (s,t) using rule (rs,rt) *)
     | Rewrite ((s,t), (rs,rt)) ->
       assert (snd (Variant.normalize_rule_dir (s,t)));
       if !(S.do_proof_debug) then
         F.printf "DERIVED BY REWRITE FROM %a:\n%!" R.print (s,t);
       let conv = subst delta (conversion_for (v,w) o) in
       let conv', tau = solve conv (s,t) (List.map fst gconv_acc) in
       let gconv = Rule.substitute tau (s,t), conv' in
       if !(S.do_proof_debug) then (
         F.printf "RESULTING CONVERISON for %a:\n%!" R.print (fst gconv);
           print (snd gconv));
       let rls = Listx.unique (List.map fst (rs @ rt)) in
       let o,i = H.find goal_trace_table (s,t) in
       if !(S.do_proof_debug) then
           F.printf "R-ADD GOAL %i:%a \n\n%!" i Rule.print (fst gconv);
       goal_ancestors (rls @ rule_acc) (gconv :: gconv_acc) (s,t) o
     (* (v,w) was obtained from deduce with goal g0 using rule rl *)
     | CP (rl, p, g0) ->
       let g0 = Variant.normalize_rule g0 in
       if !(S.do_proof_debug) then
         F.printf "DERIVED BY DEDUCE FROM %a:\n%!" R.print g0;
       let conv = subst delta (conversion_for (v,w) o) in
       let conv', tau = solve conv g0 (List.map fst gconv_acc) in
       let gconv = Rule.substitute tau g0, conv' in
       if !(S.do_proof_debug) then (
         F.printf "RESULTING CONVERISON for %a:\n%!" R.print (fst gconv);
         print (snd gconv));
       let rl',d_rl = normalize rl LeftRight in
       let o,i = H.find goal_trace_table g0 in
       if !(S.do_proof_debug) then
           F.printf "D-ADD GOAL %i:%a \n\n%!" i Rule.print (fst gconv);
       goal_ancestors (rl' :: rule_acc) (gconv :: gconv_acc) g0 o
  with Not_found -> (
    F.printf "no origin found for goal %a\n%!" R.print g;
    failwith "Trace.goal_ancestors: equation unknown")
;;

let append (s,sconv) (t,tconv) =
  if !(S.do_proof_debug) then
    assert (Subst.unifiable (last (s,sconv)) t);
  let sigma = Subst.mgu (last (s,sconv)) t in
  subst sigma  (s,sconv @ tconv)
;;

(* (s,t) is the goal that was proven, (rs,rt) the rules used to rewrite it to
   the common normal form, g_orig is the normalized original goal *)
let goal_proof g_orig (s,t) (rs,rt) sigma =
  if !(S.do_proof_debug) then (
    F.printf "\n0. ORIGINAL GOAL %a\n%!" R.print g_orig;
    F.printf "\n1. PROVEN GOAL %a\n%!" R.print (s,t);
    if sigma <> [] then F.printf "(substituted)\n%!");
  let goal_conv =
    let t', rtconv = rev (t,rewrite_conv' t rt) in
    let pg_conv =  append (s,rewrite_conv' s rs) (t', rtconv) in
    equation_of pg_conv, pg_conv
  in
  if !(S.do_proof_debug) then
    (F.printf "2. THE GOAL CONVERSION:\n%!"; print (snd goal_conv));
  (* in case (s,t) is not the original goal we need to trace it back.
     Add original goal in case it is not yet there, replace in table to avoid
     cyclic dependencies: original goal (s,t) initially not in table produces
     (s',t') might produce (s,t), now added into table, ...*)
  let grls, gconvs =
    if ((s,t) <> g_orig) then (
      let o = try fst (H.find goal_trace_table (s,t)) with _ -> Initial in
      H.add goal_trace_table g_orig (Initial, -1);
      goal_ancestors [] [goal_conv] (s,t) o)
    else
      [],[]
  in
  let rls = Listx.unique ([ r | r,_,_ <- rs @ rt] @ grls) in
  let t = trace_for rls @ [goal_conv] @ gconvs in
  if !(S.do_proof_debug) then (
    F.printf "\nFINAL CONVERSIONS: \n%!";
    let pconv (i,(rl,c)) =
      F.printf "%i. %a:\n%!" i Rule.print rl; print c
    in
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
let rec to_simplifyl (l,r) rs =
  let steps = rewrite_conv l rs in
  let rec collect acc u = function
      [] -> acc (* reversal happens in to_origins *)
    | (p,rl,d,v) :: ss ->
      let s = SimplifyL ((u,r), v) in
      collect (s :: acc) v ss
  in 
  last (l,steps), collect [] l steps
;;

(* As above for SimplifyR. *)
let rec to_simplifyr (l,r) rs =
  let steps = rewrite_conv r rs in
  let rec collect acc u = function
      [] -> acc (* reversal happens in to_origins *)
    | (p,rl,d,v) :: ss ->
      let s = SimplifyR ((l,u), v) in
      collect ((*if (l,u) = rl then acc else*) s :: acc) v ss
  in 
  last (r,steps), collect [] r steps
;;

(* Compute Deduce and Simplify steps that gave rise to the given equations. *)
let rec creation_steps acc = function
    [] -> List.rev acc
  | ((s,t),o) :: es -> (match o with
    | Initial -> creation_steps acc es
    | CP (r1, p, r2) ->
      (* rename *both* (rules not obeying variable condition make problems) *)
      let r1,r2 = Rule.rename r1, Rule.rename r2 in
      let (r1,p,r2,mgu) as o = the_overlap r1 r2 p in
      let s',t' = O.cp_of_overlap o in
      let ren, keep_dir = rename_to (s',t') (s,t) in
      let u = T.substitute ren (T.substitute mgu (fst r2)) in
      let s',t' = Rule.substitute ren (s,t) in
      creation_steps (Deduce (u, s', t') :: acc) es
    | Rewrite ((s0,t0), (ss, ts)) ->
      let s,os = to_simplifyl (s0,t0) ss in
      let _,os' = to_simplifyr (s,t0) ts in
      creation_steps (os' @ os @ acc) es
    )
;;

(* Compute Simplify and Delete steps that simplify away the given equations. *)
let rec simplify_steps acc = function
    [] -> List.rev acc
  | ((s0,t0),r) :: es -> (match r with
    | Deleted -> simplify_steps (Delete s0 :: acc) es
    | Reduced ((s,t), (ss, ts)) ->
      let s,os = to_simplifyl (s0,t0) ss in
      let _,os' = to_simplifyr (s,t0) ts in
      simplify_steps (os' @ os @ acc) es
    )
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
let rec to_collapse (l,r) rs =
  let steps = rewrite_conv l rs in
  let rec collect acc u = function
      [] -> acc (* reversal happens in caller *)
    | (p,rl,d,v) :: ss ->
      let s = if acc = [] then Collapse ((u,r), v) else SimplifyL ((u,r), v) in
      (*F.printf "collapse %a to %a\n%!" Rule.print (u,r) Rule.print (v,r);*)
      collect (s :: acc) v ss
  in last (l,steps), collect [] l steps
;;

(* Compose steps for l -> r where the rewrite steps rs apply to r. *)
let rec to_compose (l,r) rs =
  let steps = rewrite_conv r rs in
  let rec collect acc u = function
      [] -> acc (* reversal happens in caller *)
    | (p,rl,d,v) :: ss -> collect ((Compose ((l,u), v)) :: acc) v ss
  in last (r,steps), collect [] r steps
;;

(* Compose and collapse steps to interreduce the TRS rr. *)
let interreduce rr =
  let rec reduce acc ee rr_u rr_p =
    match rr_u with
      [] -> (List.rev acc, ee, rr_p)
    | (l,r) :: rr_u' ->
      let rr = rr_p @ rr_u' in
      let rrs,r' = Rewriting.nf_with_at rr r in
      let lrs,l' = Rewriting.nf_with_at rr l in
      let _,os = to_compose (l,r) rrs in
      let _,os' = to_collapse (l,r') lrs in
      if l=l' then reduce (os' @ os @ acc) ee rr_u' (Listset.add (l,r') rr_p)
      else reduce (os' @ os @ acc) ((l',r') :: ee) rr_u' rr_p
  in reduce [] [] rr []
;;

(* Show inference steps of a run. *)
let show_run r =
  let tp = T.print in
  let rec show = function
    [] -> ()
  | OrientL e :: steps ->
    F.printf " orientl %a = %a\n%!" tp (fst e) tp (snd e); show steps
  | OrientR e :: steps ->
    F.printf " orientr %a = %a\n%!" tp (fst e) tp (snd e); show steps
  | Delete t :: steps ->
    F.printf " delete %a = %a\n%!" tp t tp t; show steps
  | Deduce (u,s,t) :: steps ->
    F.printf " deduce %a <- %a -> %a\n" tp s tp u tp t; show steps
  | SimplifyL ((s,t),u) :: steps ->
    F.printf " simplifyl %a = %a to %a = %a\n%!" tp s tp t tp u tp t; show steps
  | SimplifyR ((s,t),u) :: steps ->
    F.printf " simplifyr %a = %a to %a = %a\n%!" tp s tp t tp s tp u; show steps
  | Compose ((s,t),u) :: steps ->
    F.printf " compose %a -> %a to %a -> %a\n%!" tp s tp t tp s tp u; show steps
  | Collapse ((s,t),u) :: steps ->
    F.printf " collapse %a -> %a to %a = %a\n%!" tp s tp t tp u tp t; show steps
  in if !(S.do_proof_debug) then show r
;;

(* Simulate the inference steps starting from the initial equations ee0.
   Outcommented lines could serve as fault tolerance. *)
let simulate ee0 steps =
  let drop, mem = Listx.remove, List.mem in
  let (<:>) = Listset.add in
  let rec sim acc (ee_i,rr_i) = function
      [] -> List.rev acc,(ee_i,rr_i)
    | z :: steps -> match z with
    | OrientL e ->
      if (mem e ee_i) then sim (z :: acc) (drop e ee_i, e <:> rr_i) steps
      (*else if mem e rr_i then sim acc (ee_i, rr_i) steps*)
      else failwith "orientl inference impossible"
    | OrientR e ->
      let rr_i' = Rule.flip e <:> rr_i in
      if mem e ee_i then sim (z :: acc) (drop e ee_i, rr_i') steps
      (*else if (mem (Rule.flip e) rr_i) then sim acc (ee_i, rr_i) steps*)
      else failwith "orientr inference impossible"
    | Delete t ->
      sim (z :: acc) (drop (t,t) ee_i, rr_i) steps
    | Deduce (u,s,t) ->
      sim (z :: acc) ((s,t) <:> ee_i, rr_i) steps
    | SimplifyL ((s,t) as st,u) ->
      if mem st ee_i then sim (z :: acc) ((u,t) <:> (drop st ee_i), rr_i) steps
      (*else if (mem (u,t) ee_i) then sim acc (ee_i, rr_i) steps*)
      else failwith "SimplifyL inference impossible"
    | SimplifyR ((s,t) as st,u) ->
      if mem st ee_i then sim (z :: acc) ((s,u) <:> (drop st ee_i), rr_i) steps
      (*else if (mem (s,u) ee_i) then sim acc (ee_i, rr_i) steps*)
      else failwith "SimplifyR inference impossible"
    | Collapse ((s,t) as st,u) ->
      if mem st rr_i then sim (z :: acc) ((u,t) <:> ee_i, drop st rr_i) steps
      (*else if (mem (u,t) ee_i) then sim acc (ee_i, rr_i) steps*)
      else failwith "Collapse inference impossible"
    | Compose ((s,t) as st,u) ->
      if mem st rr_i then sim (z :: acc) (ee_i, (s,u) <:> (drop st rr_i)) steps
      (*else if mem (s,u) rr_i then sim acc (ee_i, rr_i) steps*)
      else failwith "Compose inference impossible"
  in sim [] (ee0,[]) steps
;;

(* Check whether equations/rules required for inferences are present.
   TODO: also check rewrite steps *)
let check ee0 steps (ee,rr) =
  let drop, mem, tp, d = Listx.remove, List.mem, T.print, !(S.do_proof_debug) in
  let (<:>) = Listset.add in
  let rec sim acc (ee_i,rr_i) = function
      [] -> true
    | z :: steps -> match z with
    | OrientL e ->
      if d then F.printf " orientl %a = %a\n%!" tp (fst e) tp (snd e);
      (mem e ee_i) && sim (z :: acc) (drop e ee_i, e <:> rr_i) steps
    | OrientR e ->
      if d then F.printf " orientr %a = %a\n%!" tp (fst e) tp (snd e);
      let rr_i' = Rule.flip e <:> rr_i in
      mem e ee_i && sim (z :: acc) (drop e ee_i, rr_i') steps
    | Delete t ->
      if d then F.printf " delete %a = %a\n%!" tp t tp t;
      mem (t,t) ee_i && sim (z :: acc) (drop (t,t) ee_i, rr_i) steps
    | Deduce (u,s,t) ->
      if d then F.printf " deduce %a <- %a -> %a\n" tp s tp u tp t;
      sim (z :: acc) ((s,t) <:> ee_i, rr_i) steps
    | SimplifyL ((s,t),u) ->
      if d then F.printf " simplifyl %a = %a to %a = %a\n" tp s tp t tp u tp t;
      mem (s,t) ee_i && sim (z :: acc) ((u,t) <:> (drop (s,t) ee_i), rr_i) steps
    | SimplifyR ((s,t),u) ->
      if d then F.printf " simplifyr %a = %a to %a = %a\n" tp s tp t tp s tp u;
      mem (s,t) ee_i && sim (z :: acc) ((s,u) <:> (drop (s,t) ee_i), rr_i) steps
    | Collapse ((s,t),u) ->
      if d then F.printf " collapse %a -> %a to %a = %a\n" tp s tp t tp u tp t;
      mem (s,t) rr_i && sim (z :: acc) ((u,t) <:> ee_i, drop (s,t) rr_i) steps
    | Compose ((s,t),u) ->
      if d then F.printf " compose %a -> %a to %a -> %a\n" tp s tp t tp s tp u;
      mem (s,t) rr_i && sim (z :: acc) (ee_i, (s,u) <:> (drop (s,t) rr_i)) steps
  in
  let _, (ee',rr') = simulate ee0 steps in
  sim [] (ee0,[]) steps && Listset.equal ee ee' && Listset.equal rr rr'
;;

(* Construct a run from ee0, to obtain (an interreduced version of) (ee,rr). *)
let reconstruct_run ee0 ee rr =
  (* collect derivations for computed (ee,rr) *)
  let ee0 = [ Variant.normalize_rule e | e <- ee0 ] in
  let steps0 = creation_steps [] (ancestors (ee @ rr)) in

  (* simulate the run so far, this results in equations ee' and rr' *)
  let steps1,(ee',rr') = simulate ee0 steps0 in

  (* by ground completeness, additional equations must be subsumed/joinable *)
  let ee'' = Listset.diff ee' (Rules.flip (ee @ rr) @ ee @ rr) in
  (* compute these derivations that result in Delete or present equations *)
  let steps_ee = simplify_steps [] (descendants ee'') in

  (* rules in rr need to be oriented  *)
  let orient_steps = orient_steps ee' (Listset.diff rr rr') in

  (* interreduce the set of all rules, computing collapse/compose steps *)
  let rr'' = Listset.union rr rr' in
  let interred_steps, ee_add, rr_reduced = interreduce rr'' in

  (* interreduction might produce equations that should be subsumed/joinable *)
  let ss_ee' = simplify_steps [] (descendants (Listx.unique ee_add)) in

  (* combine all inference steps *)
  let steps = steps1 @ orient_steps @ steps_ee @ interred_steps @ ss_ee' in
  let run, res = simulate ee0 steps in
  assert (check ee0 run res);
  if !(S.do_proof_debug) then (
    F.printf "FINAL RUN:\n%!";
    show_run run;
    F.printf "final equations: \n%a\n%!" (Rules.print) (fst res);
    F.printf "final rules: \n%a\n%!" (Rules.print) (snd res));
  run, res
;;

(*** XML REPRESENTATION  *****************************************************)
let xml_str s = Xml.PCData s

let pos_to_xml p =
  (* CeTA positions start at 1 *)
  let px i = X.Element("position", [], [ xml_str (string_of_int (i + 1)) ]) in
  X.Element("positionInTerm", [], List.map px p)
;;

let equation_to_xml (l,r) = X.Element("inequality",[],[T.to_xml l;T.to_xml r])

let input_to_xml es g_opt =
  let es0 = [ Variant.normalize_rule e | e <- es ] in
  let xes = X.Element("equations",[], [ Rules.to_xml es0 ] ) in
  let xgs = match g_opt with None -> [] | Some g -> [ equation_to_xml g ] in
  let input = X.Element("equationalReasoningInput",[],xes :: xgs) in
  X.Element("input",[],[input])
;;

let step_to_xml (p,rl,dir,t) =
  let dirstr = function LeftRight -> "leftRight" | _ -> "rightLeft" in
  let dirxml = X.Element(dirstr dir, [], []) in
  let components = [pos_to_xml p; R.to_xml rl; dirxml; T.to_xml t] in
  X.Element("equationStep", [], components)
;;

let conversion_to_xml (t, steps) =
  let start = X.Element("startTerm", [], [T.to_xml t]) in
  X.Element("conversion", [], start :: (List.map step_to_xml steps))
;;

let rule_sub_to_xml ((s,t), (s',steps)) =
  let xconv = conversion_to_xml (s',steps) in
  X.Element("ruleSubsumptionProof", [], [ R.to_xml (s,t); xconv ])
;;

let eqproof_to_xml cs =
  let xsub = X.Element("subsumptionProof", [], List.map rule_sub_to_xml cs) in
  let xconv = X.Element("convertibleInstance", [], [ xsub ]) in
  X.Element("equationalDisproof", [], [ xconv ])
;;

let inference_to_xml step =
  let t3_to_xml ((s,t),u) = [ T.to_xml v | v <- [s;t;u] ] in
  let to_xml = function
      Deduce (s,t,u) -> X.Element("deduce", [], [ T.to_xml v | v <- [s;t;u] ])
    | Delete s -> X.Element("delete", [], [T.to_xml s])
    | SimplifyL (st,u) -> X.Element("simplifyl", [], t3_to_xml (st,u))
    | SimplifyR (st,u) -> X.Element("simplifyr", [], t3_to_xml (st,u))
    | OrientL (s,t) -> X.Element("orientl", [], [T.to_xml s; T.to_xml t])
    | OrientR (s,t) -> X.Element("orientr", [], [T.to_xml s; T.to_xml t])
    | Compose (st,u) -> X.Element("compose", [], t3_to_xml (st,u))
    | Collapse (st,u) -> X.Element("collapse", [], t3_to_xml (Rule.flip st,u))
  in X.Element("orderedCompletionStep", [], [ to_xml step ])
;;

let run_to_xml steps = X.Element("run", [], [ inference_to_xml s | s <- steps ])

let ordered_completion_input_to_xml ee0 (rr,ee,ord) =
  let ee0 = [ Variant.normalize_rule e | e <- ee0 ] in
  let xes0 = X.Element("equations", [], [ Rules.to_xml ee0 ] ) in
  let xrs = X.Element("trs", [], [ Rules.to_xml rr] ) in
  let xes = X.Element("equations", [], [ Rules.to_xml ee ] ) in
  let xord = X.Element("reductionOrder", [], [ ord#to_xml ] ) in
  let oxi = X.Element("orderedCompletionInput", [], [ xes0; xrs; xes; xord ]) in
  X.Element("input",[],[oxi])
;;

let eqdisproof_to_xml ee0 (rr,ee,ord) ((s,t), (rs,rt)) =
  let xconv_s = conversion_to_xml (s, rewrite_conv' s rs) in
  let xconv_t = conversion_to_xml (t, rewrite_conv' t rt) in
  let xnorm = X.Element("normalization", [], [xconv_s; xconv_t]) in
  let steps, _ = reconstruct_run ee0 ee rr in
  let comps = (run_to_xml steps) :: [xnorm ] in
  let xconv = X.Element("groundCompletionAndNormalization", [], comps) in
  X.Element("equationalDisproof", [], [ xconv ])
;;

let xml_proof_wrapper xinput xproof =
  let xversion = X.Element("cpfVersion", [], [ xml_str "2.1" ]) in
  let xt = X.Element("tool", [], [
    X.Element("name", [], [ xml_str "maedmax" ]);
    X.Element("version", [], [ xml_str "0.9" ]) ])
  in
  let xo = X.Element("origin", [], [ X.Element("proofOrigin", [], [ xt ]) ]) in
  let attrs = [ "xmlns:xsi","http://www.w3.org/2001/XMLSchema-instance";
                "xsi:noNamespaceSchemaLocation","../xml/cpf.xsd"] in
  X.Element("certificationProblem", attrs, [xinput; xversion; xproof; xo])
;;

let xml_goal_proof es0 g_orig ((s,t), (rs,rt), sigma) =
  let g = Variant.normalize_rule g_orig in
  let rulesubs = goal_proof g (s,t) (rs,rt) sigma in
  let xproof = X.Element("proof", [], [ eqproof_to_xml rulesubs ]) in
  xml_proof_wrapper (input_to_xml es0 (Some g)) xproof
;;

let xml_goal_disproof es0 g_orig ((rr,ee,ord) as res) rst =
  let g = Variant.normalize_rule g_orig in
  let xproof = X.Element("proof", [], [ eqdisproof_to_xml es0 res (g,rst) ]) in
  xml_proof_wrapper (input_to_xml es0 (Some g)) xproof
;;

let xml_ground_completion ee0 (rr,ee,ord) =
  let steps, (ee',rr') = reconstruct_run ee0 ee rr in
  let ee' = variant_free ee' in
  let xcproof = X.Element("orderedCompletionProof", [], [ run_to_xml steps ]) in
  let xproof = X.Element("proof", [], [ xcproof ]) in
  let xinput = ordered_completion_input_to_xml ee0 (rr',ee',ord) in
  xml_proof_wrapper xinput xproof
;;
