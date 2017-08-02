module O = Overlap
module T = Trace

class literal (ts : Rule.t) (pos : bool) (goal : bool) = object (self)

  method terms = ts

  method is_goal = goal

  method is_equality = pos

  method is_inequality = not pos

  method compare (l : literal) =
    Pervasives.compare (ts, pos, goal) (l#terms, l#is_equality, l#is_goal)

  method equal l = (self#compare l) = 0

  method flip = new literal (Rule.flip ts) pos goal

  method is_subsumed (l : < terms : Rule.t >) =
    Rule.is_instance ts l#terms || Rule.is_instance (Rule.flip ts) l#terms

  method is_trivial = (fst ts = snd ts)

  method normalize = new literal (Variant.normalize_rule ts) pos goal

  method not_increasing = not (Term.is_subterm (fst ts) (snd ts))

  (* already normalized *)
  method cps (l : literal) =
    assert (not (goal && l#is_goal));
    if not pos && not l#is_equality then []
    else
      let r1, r2 = ts, l#terms in
      let os = [ O.cp_of_overlap o,o | o <- O.overlaps_between r1 r2 ] in
      let is_eq, is_goal = pos && l#is_equality, goal || l#is_goal in
      if !(Settings.do_proof) then (
        let trace = if is_goal then T.add_overlap_goal else T.add_overlap in
        let add ((s,t),o) =
          if s<>t then trace (Variant.normalize_rule (s,t)) o
        in List.iter add os);
      [ new literal (Variant.normalize_rule (fst o)) is_eq is_goal | o <- os ]
  
  method rewriter_nf_with (rewriter : Rewriter.rewriter) =
    let s', rs = rewriter#nf (fst ts) in
    let t', rt = rewriter#nf (snd ts) in
    let rls = List.map fst (rs @ rt) in
    if s' = t' then Some([], rls)
    else if Rule.equal ts (s',t') then None
    else (
      let st' = Variant.normalize_rule (s',t') in
      if !(Settings.do_proof) then
        (if goal then T.add_rewrite_goal else T.add_rewrite) st' ts (rs,rt);
      (* preserve goal/equality status *)
      Some ([ new literal st' pos goal ], rls))
  
  method to_nf (rewriter : Rewriter.rewriter) =
    let s, _ = rewriter#nf (fst ts) in
    let t, _ = rewriter#nf (snd ts) in
    new literal (Variant.normalize_rule (s,t)) pos goal
  
  method joins trs = 
    let _, s' = Rewriting.nf_with trs (fst ts) in
    let _, t' = Rewriting.nf_with trs (snd ts) in
    s' = t'

  method print ppf =
    Format.fprintf ppf "%a %s %a" Term.print (fst ts)
      ((if pos then "=" else "!=") ^ (if goal then "G" else ""))
      Term.print (snd ts)

  method is_ac_equivalent fs = Theory.Ac.equivalent fs ts

  method is_ground = Rule.is_ground ts
end

type t = literal

let make_axiom ts = new literal ts true false

let make_neg_axiom ts = new literal ts true false

let make_goal ts = new literal ts true true

let make_neg_goal ts = new literal ts false true

let is_equality l = l#is_equality