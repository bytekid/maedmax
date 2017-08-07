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
  | Deduce of R.t * int list * R.t

type direction = LeftRight | RightLeft

type cpf_step = pos * R.t * direction * Term.t

type cpf_conv = Term.t * (cpf_step list)

(*** GLOBALS *****************************************************************)
let trace_table : (R.t, origin) H.t = H.create 128
let goal_trace_table : (R.t, origin * int) H.t = H.create 128
let gcount = ref 0
(*** FUNCTIONS ***************************************************************)
let root = []

let parents = function
   Initial-> []
 | Rewrite (p, (lsteps, rsteps)) -> p :: (List.map fst (lsteps @ rsteps))
 | Deduce (rl1, _, rl2) -> [rl1; rl2]
;;

let dir = function false -> RightLeft | _ -> LeftRight

let pstr = List.fold_left (fun s i -> s ^ (string_of_int i)) ""

let print (s, ss) = 
  F.printf "%a\n%!" Term.print s;
  let rec print = function
    | [] -> ()
    | (p,rl,d,t) :: steps -> (
      let ds = if d = LeftRight then "->" else "<-" in
      F.printf " %s %a (%a at %s)\n%!" ds Term.print t R.print rl (pstr p);
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
let add eq o = if not (H.mem trace_table eq) then H.add trace_table eq o

let gadd g o =
  if not (H.mem goal_trace_table g) then (
  let c = !gcount in
  gcount := c + 1;
       if !(S.do_proof_debug) then
  F.printf "ADDING GOAL %i:%a\n" c Rule.print g;
  let t = goal_trace_table in H.add t g (o,c))

let add_initials eqs =
  (*if !(S.do_proof_debug) then
    List.iter (fun eq -> F.printf "initial: %a\n" R.print eq) eqs;*)
  List.iter (fun e -> add e Initial) eqs

let add_overlap eq (rl1,p,rl2,_) =
  (*if !(S.do_proof_debug) then
    F.printf "overlap: %a\n" R.print eq;*)
  add eq (Deduce (rl1,p,rl2))

let add_rewrite eq eq0 steps =
  (*if !(S.do_proof_debug) then
    F.printf "rewrite: %a\n" R.print eq;*)
  add eq (Rewrite (eq0,steps))

let add_initial_goal eqs =
  (*if !(S.do_proof_debug) then
    List.iter (fun eq -> F.printf "initial: %a\n" R.print eq) eqs;*)
  List.iter (fun e -> gadd e Initial) eqs

let add_overlap_goal eq (rl1,p,rl2,_) =
  (*if !(S.do_proof_debug) then
    F.printf "overlap: %a\n" R.print eq;*)
  gadd eq (Deduce (rl1,p,rl2))

let add_rewrite_goal eq eq0 steps =
  (*if !(S.do_proof_debug) then
    F.printf "rewrite: %a\n" R.print eq;*)
  gadd eq (Rewrite (eq0,steps))

let ancestors eqs = 
  let rec ancestors acc = function
    | [] -> acc
    | eq :: eqs ->
      try
        let eq = Variant.normalize_rule eq in
        if List.mem eq (List.map fst acc) then
          ancestors acc eqs
        else
          let o = H.find trace_table eq in
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

(* Get renaming that renames first to second rule *)
let rename_to (l1,r1) (l2,r2) =
  let t1, t2 = Term.F(0,[l1;r1]), Term.F(0,[l2;r2]) in
  try Subst.pattern_match t1 t2, true
  with _ ->
    try Subst.pattern_match (Term.F(0,[r1;l1])) t2, false
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
  List.iter (fun (x,t) -> Format.printf "  %s -> %a\n" (Signature.get_var_name x) Term.print t)

(* Given a conversion for s = t where u = v or v = u occurs produce a conversion
   for u = v using s = t or t = s. *)
let solve (s,steps) (u,v) goals =
 if !(S.do_proof_debug) then
  (Format.printf "LOOK FOR %a IN: \n" Rule.print (u,v); print (s,steps));
 let t = last (s,steps) in
 let rec solve steps_bef s' = function 
     [] -> failwith "Trace.solve: equation not found"
   | (p,rl,d,t') :: steps_aft ->
     if rl <> (u,v) && rl <> (v,u) then
       solve ((p,rl,flip d,s') :: steps_bef) t' steps_aft
     else (
       if (!(S.do_proof_debug) && not (List.exists (fun g -> Rule.is_instance g (s,t)) goals)) then
         Format.printf "no instance: %a\n %!" Rule.print (s,t);
       let st_step = root, (s,t), LeftRight, t in
       let res = s', steps_bef @ [st_step] @ (snd (rev (t',steps_aft))) in
       let oriented_rl = if d = LeftRight then rl else Rule.flip rl in
       if (s',t') = oriented_rl then
         rev_unless res ((s',t') = (u,v)), Subst.empty
       else (
         if !(S.do_proof_debug) then
           Format.printf "INSTANTIATE  %a TO %a\n%!" Rule.print oriented_rl Rule.print (s',t');
         let tau = Rule.instantiate_to oriented_rl (s',t') in
         assert ((Rule.substitute tau oriented_rl) = (s',t'));
         assert (equation_of res = (s',t'));
         if (!(S.do_proof_debug) && Rule.substitute tau (u,v) <> (s',t')) then (
           Format.printf "SUBSTITUTED IS  %a\n%!" Rule.print (Rule.substitute tau (u,v));
           assert (Rule.substitute tau (v,u) = (s',t')));
         let conv = rev_unless res (Rule.substitute tau (u,v) = (s',t')) in
         if !(S.do_proof_debug) then (
           Format.printf "SUBSTITUTE TO %a\n%!" Rule.print (equation_of conv);
           subst_print tau;
         );
     conv, tau))
 in
 let conv, tau = solve [] s steps in
 if !(S.do_proof_debug) then (
   let uv' = Rule.substitute tau (u,v) in
   assert (equation_of conv = uv');
   (Format.printf "RESULT: \n"; print conv));
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
 | Deduce (r1, p, r2) -> (* r1 is inside, r2 outside *)
   let ((r1,p,r2,mgu) as o) = the_overlap r1 r2 p in
   let s',t' = O.cp_of_overlap o in
   let ren, keep_dir = rename_to (s',t') (s,t) in
   let u = Term.substitute ren (Term.substitute mgu (fst r2)) in
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
       (* no substitution added by solve *)
       let conv',_ = solve conv (s,t) (List.map fst gconv_acc) in
       let gconv = Rule.substitute delta (s,t), conv' in
       if !(S.do_proof_debug) then (
         F.printf "RESULTING CONVERISON for %a:\n%!" R.print (fst gconv); print (snd gconv));
       let rls = Listx.unique (List.map fst (rs @ rt)) in
       let o,i = H.find goal_trace_table (s,t) in
       if !(S.do_proof_debug) then
           Format.printf "R-ADD GOAL %i:%a \n\n%!" i Rule.print (fst gconv);
       goal_ancestors (rls @ rule_acc) (gconv :: gconv_acc) (s,t) o
     (* (v,w) was obtained from deduce with goal g0 using rule rl *)
     | Deduce (rl, p, g0) ->
       (*assert (snd (Variant.normalize_rule_dir g0));*)
       let g0 = Variant.normalize_rule g0 in
       if !(S.do_proof_debug) then
         F.printf "DERIVED BY DEDUCE FROM %a:\n%!" R.print g0;
       let conv = subst delta (conversion_for (v,w) o) in
       let conv', tau = solve conv g0 (List.map fst gconv_acc) in
       let gconv = Rule.substitute tau g0, conv' in
       if !(S.do_proof_debug) then (
         F.printf "RESULTING CONVERISON for %a:\n%!" R.print (fst gconv); print (snd gconv));
       let rl',d_rl = normalize rl LeftRight in
       let o,i = H.find goal_trace_table g0 in
       if !(S.do_proof_debug) then
           Format.printf "D-ADD GOAL %i:%a \n\n%!" i Rule.print (fst gconv);
       goal_ancestors (rl' :: rule_acc) (gconv :: gconv_acc) g0 o
  with Not_found -> (
    F.printf "no origin found for goal %a\n%!" R.print g;
    failwith "Trace.goal_ancestors: equation unknown")
;;

let append (s,sconv) (t,tconv) =
  let sigma = Subst.mgu (last (s,sconv)) t in
  subst sigma  (s,sconv @ tconv)
;;

(* (s,t) is the goal that was proven, (rs,rt) the rules used to rewrite it to
   the common normal form, g_orig is the normalized original goal *)
let goal_proof g_orig (s,t) (rs,rt) sigma =
  if !(S.do_proof_debug) then (
    F.printf "\n0. ORIGINAL GOAL %a\n%!" R.print g_orig;
    F.printf "\n1. PROVEN GOAL %a\n%!" R.print (s,t));
  let goal_conv =
    if sigma = [] then (
      (*Format.printf "t: rewrite conv from %a:" Term.print t; print (t,rewrite_conv t rt);
      Format.printf "s: rewrite conv from %a:" Term.print t; print (s,rewrite_conv s rs);*)
      let t', rtconv = rev (t,rewrite_conv t rt) in
      (* conversion for the proven goal using the rules *)
      let pg_conv =  append (s,rewrite_conv s rs) (t', rtconv) in
      equation_of pg_conv, pg_conv
      )
    else (
      failwith "substituted proof";
      (*let s',t' = Rule.substitute sigma (s,t) in
      (s',t'), (s',[])*))
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
  let rls = Listx.unique (List.map fst (rs @ rt) @ grls) in
  let t = trace_for rls @ [goal_conv] @ gconvs in
  if !(S.do_proof_debug) then (
    F.printf "\nFINAL CONVERSIONS: \n%!";
    let pconv (i,(rl,c)) =
      F.printf "%i. %a:\n%!" i Rule.print rl; print c
    in
    List.iter pconv (Listx.index t));
  t
;;

(*** XML REPRESENTATION  *****************************************************)
let xml_str s = Xml.PCData s

let pos_to_xml p =
  (* CeTA positions start at 1 *)
  let px i = X.Element("position", [], [ xml_str (string_of_int (i + 1)) ]) in
  X.Element("positionInTerm", [], List.map px p)
;;

let equation_to_xml (l,r) = X.Element("equation",[],[T.to_xml l;T.to_xml r])

let input_to_xml es g =
  let es0 = [ Variant.normalize_rule e | e <- es ] in
  let xes = X.Element("equations",[], [ Rules.to_xml es0 ] ) in
  let xgs = [ equation_to_xml g ] in
  let input = X.Element("equationalReasoningInput",[],xes :: xgs) in
  X.Element("input",[],[input])
;;

let step_to_xml (p,rl,dir,t) =
  let dirstr = function LeftRight -> "leftRight" | _ -> "rightLeft" in
  let dirxml = X.Element(dirstr dir, [], []) in
  let components = [pos_to_xml p; R.to_xml rl; dirxml; Term.to_xml t] in
  X.Element("equationStep", [], components)
;;

let conversion_to_xml (t, steps) =
  let start = X.Element("startTerm", [], [Term.to_xml t]) in
  X.Element("conversion", [], start :: (List.map step_to_xml steps))
;;

let rule_sub_to_xml ((s,t), (s',steps)) =
  let xconv = conversion_to_xml (s',steps) in
  X.Element("ruleSubsumptionProof", [], [ R.to_xml (s,t); xconv ])
;;

let eqproof_to_xml cs =
  let xsub = X.Element("subsumptionProof", [], List.map rule_sub_to_xml cs) in
  X.Element("equationalProof", [], [ xsub ])
;;

let xml_goal_proof es0 g_orig ((s,t), (rs,rt), sigma) =
  let g_orig = Variant.normalize_rule g_orig in
  let rulesubs = goal_proof g_orig (s,t) (rs,rt) sigma in
  let xinput = input_to_xml es0 g_orig in
  let xversion = X.Element("cpfVersion", [], [ xml_str "2.1" ]) in
  let xproof = X.Element("proof", [], [ eqproof_to_xml rulesubs ]) in
  let xt = X.Element("tool", [], [
    X.Element("name", [], [ xml_str "madmax" ]);
    X.Element("version", [], [ xml_str "0.9" ]) ])
  in
  let xo = X.Element("origin", [], [ X.Element("proofOrigin", [], [ xt ]) ]) in
  let attrs = [ "xmlns:xsi","http://www.w3.org/2001/XMLSchema-instance";
                "xsi:noNamespaceSchemaLocation","../xml/cpf.xsd"] in
  X.Element("certificationProblem", attrs, [xinput; xversion; xproof; xo])
;;
