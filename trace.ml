(*** MODULES *****************************************************************)
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
let trace_table : (R.t, origin) Hashtbl.t = Hashtbl.create 128

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
  Format.printf "%a\n%!" Term.print s;
  let rec print = function
    | [] -> ()
    | (p,rl,d,t) :: steps -> (
      let ds = if d = LeftRight then "->" else "<-" in
      Format.printf " %s %a (%a at %s)\n%!" ds Term.print t R.print rl (pstr p);
      print steps)
  in print ss
;;

let print_all = List.iter print

let rec print_steps = function
   [] -> ()
 | (rl,p) :: ss ->
   Format.printf " -> using %a at %s\n" Rule.print rl (pstr p); print_steps ss 
;;

(* keep first origin for equation to avoid cycles *)
let add eq o =
    if not (Hashtbl.mem trace_table eq) then Hashtbl.add trace_table eq o

let add_initials eqs =
  (*if !(S.do_proof_debug) then
    List.iter (fun eq -> Format.printf "initial: %a\n" R.print eq) eqs;*)
  List.iter (fun e -> add e Initial) eqs

let add_overlap eq (rl1,p,rl2,_) =
  (*if !(S.do_proof_debug) then
    Format.printf "overlap: %a\n" R.print eq;*)
  add eq (Deduce (rl1,p,rl2))

let add_rewrite eq eq0 steps =
  (*if !(S.do_proof_debug) then
    Format.printf "rewrite: %a\n" R.print eq;*)
  add eq (Rewrite (eq0,steps))

let ancestors eqs = 
  let rec ancestors acc = function
    | [] -> acc
    | eq :: eqs ->
      try
        let eq = Variant.normalize_rule eq in
        if List.mem eq (List.map fst acc) then
          ancestors acc eqs
        else
          let o  = Hashtbl.find trace_table eq in
          let ps = parents o in
          let acc' = ancestors acc (Listset.diff ps [eq | eq,_ <- acc]) in
          let xs = List.map fst acc' in
          assert (List.length xs = List.length (Listx.unique xs));
          let acc'' = acc' @ [eq,o] in
          ancestors acc'' (Listset.diff eqs (List.map fst acc''))
      with Not_found -> (
        Format.printf "no origin found for %a\n%!" R.print eq;
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

let flip = function LeftRight -> RightLeft | _ -> LeftRight

(* Revert a cpf conversion *)
let rec rev (t, steps) =
 match steps with
   | [] -> t,[]
   | (p,rl,d,u) :: ss -> let v,ss' = rev (u,ss) in v, ss' @ [p,rl,flip d,t]
;;

let rev (t,steps) = 
  let u, spets = rev (t,steps) in
  assert (last (t,steps) = u);
  u, spets
;;

let subst sub = List.map (fun (p,rl,d,u) -> (p,rl,d,T.substitute sub u)) 

let flip_unless keep_dir d = if keep_dir then d else flip d

let normalize rl d =
  let rl', kept = Variant.normalize_rule_dir rl in
  rl', if kept then d else flip d 
;;

let rewrite_conv t steps =
  let step_conv (t,acc) (rl,p) =
  try
    (*Format.printf "apply rule %a to %a\n%!" Rule.print rl Term.print t;*)
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
let conversion_for (s,t) = function
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
   let v, conv = if keep_dir then conv else rev conv in
   if !(S.do_proof_debug) then (
     Format.printf "\ndeduce conversion for %a %s:\n%!"
       R.print (s',t') (if keep_dir then "" else "(flipped)");
     print (v,conv));
   v,conv
 | Rewrite ((s0,t0), (ss, ts)) ->
   (*assert (snd (Variant.normalize_rule_dir (s,t))); not necessarily *)
   let sconv = rewrite_conv s0 ss in
   let tconv = rewrite_conv t0 ts in
   let ren, keep_dir = rename_to (last (s0,sconv), last (t0,tconv)) (s,t) in
   let (s0f,t0f) = Rule.substitute ren (s0, t0) in
   let sconv = subst ren sconv in
   let tconv = subst ren tconv in
   let st_step = (root,(s0,t0),LeftRight,t0f) in
   assert ((keep_dir && last (s0f, sconv) = s) ||
           (not keep_dir && last (s0f, sconv) = t));
   let _,rsconv = rev (s0f, sconv) in
   let conv = rsconv @ st_step :: tconv in
   let v,conv = if keep_dir then (s,conv) else rev (t,conv) in
   assert (last (v,conv) = t);
   if !(S.do_proof_debug) then (
     Format.printf "\nrewrite conversion for %a (%i):\n%!" R.print (s,t) (if keep_dir then 1 else 0);
     print (v,conv));
   v,conv
;;

(* Produce trace for equation *)
let trace_for eqs =
  (*Format.printf "ancestors:\n";
  List.iter (fun (a,_) -> Format.printf "  %a\n" R.print a) (ancestors eqs);*)
  [ a, conversion_for a o | a, o <- ancestors eqs; o <> Initial ]
;;

let rec goal_ancestors rule_acc gconv_acc sigma g o =
  try
    let ((v,w) as g1), keep_gdir = Variant.normalize_rule_dir g in
    if !(S.do_proof_debug) then
      Format.printf "\ngoal_ancestors for %a:\n%!" R.print (v,w);
    match o with
     (* recursion stops if we reach an initial goal; need to reverse the list
        of subsequent goals encountered *)
     | Initial -> Listx.unique rule_acc, List.rev gconv_acc
     | Rewrite ((s,t), (rs,rt)) ->
       (* reverse origin: want to obtain (s,t) from (v,w) *)
       assert (snd (Variant.normalize_rule_dir (s,t)));
       if !(S.do_proof_debug) then (
         Format.printf " rewrite back to %a:\n%!" R.print (s,t);
         Format.printf " steps from s:\n%!";
         print_steps rs;
         Format.printf " steps from t:\n%!";
         print_steps rt);
       let sconv = rewrite_conv s rs in (* from so to v or w *)
       let vw,rtconv = rev (t,rewrite_conv t rt) in (* from v or w to t *)
       let ren, not_flipped = rename_to (last (s,sconv), vw) (v,w) in
         (* not_flipped: s is connected to v, t to w *)
       assert ((T.substitute ren vw = w && not_flipped) || (T.substitute ren vw = v && (not not_flipped)));
       let vw_step =
         if not_flipped then (root,g1,LeftRight,w)
         else (root,g1,RightLeft,v) 
       in
       let conv = s, sconv @ (vw_step:: rtconv) in
       if !(S.do_proof_debug) then (
         Format.printf "final conv\n%!";
         print conv);
       assert (last conv = t);
       let gconv = (s,t), conv in
       let rls = Listx.unique (List.map fst (rs @ rt)) in
       assert (snd (Variant.normalize_rule_dir (s,t)));
       let o = Hashtbl.find trace_table (s,t) in
       goal_ancestors (rls @ rule_acc) (gconv :: gconv_acc) sigma (s,t) o
     | Deduce (rl, p, g0) ->
       let ((rl,p,g0,mgu) as o) = the_overlap rl g0 p in
       let v',w' = O.cp_of_overlap o in (* strange var names *)
       if !(S.do_proof_debug) then
         Format.printf " simulated CP: %a\n%!" R.print (v',w');
       let ren, keep_dir = rename_to (v',w') (v,w) in
       let rl',d_rl = normalize rl LeftRight in
       let (s0,t0),d_g = normalize (Rule.substitute mgu g0) LeftRight in
       if !(S.do_proof_debug) then
         Format.printf " deduce back to %a %i:\n%!" R.print (s0,t0) (if d_g = LeftRight then 1 else 0);
       let u,d = if keep_dir then v, LeftRight else w, RightLeft in
       let gconv =
         if d_g = LeftRight then (s0,[(p,rl',d_rl,u); (root,g1,d,t0)])
         else (s0,[(root,g1,flip d,u); (p,rl',flip d_rl,t0)])
       in 
       if !(S.do_proof_debug) then
         print gconv;
       let o = Hashtbl.find trace_table (Variant.normalize_rule g0) in
       goal_ancestors (rl' :: rule_acc) (((s0,t0),gconv) :: gconv_acc) sigma g0 o
  with Not_found -> (
    Format.printf "no origin found for goal %a\n%!" R.print g;
    failwith "Trace.goal_ancestors: equation unknown")
;;

(* (s,t) is the goal that was proven, (rs,rt) the rules used to rewrite it to
   the common normal form, g_orig is the normalized original goal *)
let goal_proof g_orig (s,t) (rs,rt) sigma =
  if !(S.do_proof_debug) then (
    Format.printf "\nProve original goal %a:\n%!" R.print g_orig;
    Format.printf "\nfind the goal conversion for %a:\n%!" R.print (s,t));
  let goal_conv =
    if sigma = [] then 
      let t', rtconv = rev (t,rewrite_conv t rt) in
      (s,t), (s,rewrite_conv s rs @ rtconv)
    else (
      failwith "substituted proof";
      let s',t' = Rule.substitute sigma (s,t) in
      (s',t'), (s',[]))
  in
  if !(S.do_proof_debug) then
    print (snd goal_conv);
  (* in case (s,t) is not the original goal we need to trace it back.
     Add original goal in case it is not yet there, replace in table to avoid
     cyclic dependencies: original goal (s,t) initially not in table produces
     (s',t') might produce (s,t), now added into table, ...*)
  let grls, gconvs =
    if ((s,t) <> g_orig) then (
      assert (snd (Variant.normalize_rule_dir (s,t)));
      let o = try Hashtbl.find trace_table (s,t) with _ -> Initial in
      Hashtbl.add trace_table g_orig Initial;
      goal_ancestors [] [] sigma (s,t) o)
    else
      [],[]
  in
  let rls = Listx.unique (List.map fst (rs @ rt) @ grls) in
  let t = trace_for rls @ (goal_conv :: gconvs) in
  if !(S.do_proof_debug) then (
    Format.printf "final conversions: \n%!";
    List.iter (fun (rl,c) -> Format.printf "%a:\n%!" Rule.print rl; print c) t);
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
  let es0 = List.map Variant.normalize_rule es in
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