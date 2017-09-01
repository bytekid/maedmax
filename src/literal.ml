module O = Overlap
module T = Trace

type t = { terms: Rule.t; is_goal: bool; is_equality: bool }

let make ts e g = {terms = ts; is_goal = g; is_equality = e }

let terms l = l.terms

let is_goal l = l.is_goal

let is_equality l = l.is_equality

let is_inequality l = not l.is_equality

let is_equal l l' = compare l l' = 0

let flip l = { l with terms = Rule.flip l.terms }

let is_subsumed l l' =
  Rule.is_instance l.terms l'.terms ||
  Rule.is_instance (Rule.flip l.terms) l'.terms
;;

let is_trivial l = fst l.terms = snd l.terms

let normalize l = { l with terms = Variant.normalize_rule l.terms }

let not_increasing l = not (Term.is_subterm (fst l.terms) (snd l.terms))

let cps l l' =
  assert (not (l.is_goal && l'.is_goal));
  if not l.is_equality && not l'.is_equality then []
  else
    let r1, r2 = l.terms, l'.terms in
    let os = [ O.cp_of_overlap o,o | o <- O.overlaps_between r1 r2 ] in
    let os = [ (s,t),o | (s,t),o <- os; s <> t ] in
    let is_eq = l.is_equality && l'.is_equality in
    let is_goal = l.is_goal || l'.is_goal in
    if !(Settings.do_proof) then (
      let trace = if is_goal then T.add_overlap_goal else T.add_overlap in
      let add ((s,t),o) =
        if s<>t then trace (Variant.normalize_rule (s,t)) o
      in List.iter add os);
    [ make (Variant.normalize_rule (fst o)) is_eq is_goal | o <- os ]
;;

let pcps rew l l' =
  let prime ((l,_),_,_,tau) = rew#is_nf_below_root (Term.substitute tau l) in
  assert (not (l.is_goal && l'.is_goal));
  if not l.is_equality && not l'.is_equality then []
  else
    let r1, r2 = l.terms, l'.terms in
    let os = [ O.cp_of_overlap o,o | o <- O.overlaps_between r1 r2; prime o ] in
    let is_eq = l.is_equality && l'.is_equality in
    let is_goal = l.is_goal || l'.is_goal in
    if !(Settings.do_proof) then (
      let trace = if is_goal then T.add_overlap_goal else T.add_overlap in
      let add ((s,t),o) =
        if s<>t then trace (Variant.normalize_rule (s,t)) o
      in List.iter add os);
    [ make (Variant.normalize_rule (fst o)) is_eq is_goal | o <- os ]
;;

let rewriter_nf_with l rewriter =
  let ts = l.terms in
  let s', rs = rewriter#nf (fst ts) in
  let t', rt = rewriter#nf (snd ts) in
  let rls = List.map fst (rs @ rt) in
  if s' = t' then Some([], rls)
  else if Rule.equal ts (s',t') then (
    if !(Settings.do_proof) then (
      let st' = Variant.normalize_rule (s',t') in
      T.add_rewrite st' ts (rs,rt);
      T.add_delete st');
    None)
  else (
    let st' = Variant.normalize_rule (s',t') in
    if !(Settings.do_proof) then
      (if l.is_goal then T.add_rewrite_goal else T.add_rewrite) st' ts (rs,rt);
    (* preserve goal/equality status *)
    Some ([ make st' l.is_equality l.is_goal ], rls))
;;
  
let to_nf l (rewriter : Rewriter.rewriter) =
  let s, _ = rewriter#nf (fst l.terms) in
  let t, _ = rewriter#nf (snd l.terms) in
  make (Variant.normalize_rule (s,t)) l.is_equality l.is_goal
;;
  
let joins l trs =
  let _, s' = Rewriting.nf_with trs (fst l.terms) in
  let _, t' = Rewriting.nf_with trs (snd l.terms) in
  s' = t'
;;

let print ppf l =
  let eq = if l.is_equality then "=" else "!=" in
  let eq = eq ^ (if l.is_goal then "G" else "") in
  Format.fprintf ppf "%a %s %a" Term.print (fst l.terms) eq Term.print (snd l.terms)
;;

let is_ac_equivalent l fs = Theory.Ac.equivalent fs l.terms

let is_ground l = Rule.is_ground l.terms

let make_axiom ts = make ts true false

let make_neg_axiom ts = make ts false false

let make_goal ts = make ts true true

let make_neg_goal ts = make ts false true
