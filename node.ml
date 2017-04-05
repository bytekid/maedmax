module Logic = Yicesx
module O = Overlap
module T = Term
module R = Rule

open Prelude
open Yicesx

module type T = sig
  type t
  val terms : t -> R.t
  val rule : t -> R.t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val of_rule : Yices.context -> Rule.t -> t
  (* Whether node is superfluous *)
  val is_trivial : t -> bool
  (* Returns a combination of the two nodes if they are equivalent, and None
     otherwise. Check only equality, ie. assume normalization *)
  val combine : t -> t -> t option
  (* Returns a combination of the two nodes if one subsumes the other,
     and None otherwise (more expensive than plain combine) *)
  val combine_subsumed : t -> t -> t option
  (* Mirror its terms *)
  val not_increasing : t -> bool
  val flip : t -> t
  (* Apply rule function *)
  val rule_map : (R.t -> R.t) -> t -> t
  (* Rename variables in node in a uniform way *)
  val normalize : t -> t
  (* Compute critical pairs of rule n and rule n'. Result is not normalized *)
  val cps : t -> t -> t list
  (* Compute normal form of term with respect to rules, using rewriter object.
     Result is not normalized  *)
  val rewriter_nf_with : Rewriter.rewriter -> t ->
    (t list * t list * Rules.t) option
  (* whether the TRS joins the equation *)
  val joins : Rules.t -> t -> bool
  (* less-than-or-equal, to fit Ordered module type for heaps *)
  val le: t -> t -> bool
  (* AC equivalence check *)
  val is_ac_equivalent: Signature.sym list -> t -> bool
  val print : Format.formatter -> t -> unit
end


module Equation = struct
  type t = R.t

  let terms e = e

  let rule e = e

  let compare = R.compare

  let equal e e' = (compare e e') = 0

  let of_rule _ rl = rl

  let flip = R.flip

  let rule_map f e = f e

  let is_subsumed r r' = R.is_instance r r' || R.is_instance (flip r) r'

  let is_trivial (s,t) = (s = t)

  let normalize = Variant.normalize_rule

  let not_increasing (l,r) = not (Term.is_subterm l r)

  let cps r1 r2 =
    let os = [ O.cp_of_overlap o,o | o <- O.overlaps_between r1 r2 ] in
    if !(Settings.do_proof) then (
      let add ((s,t),o) = if s<>t then Trace.add_overlap (normalize (s,t)) o in
      List.iter add os);
    List.map fst os
  ;;

  let cps r1 = Statistics.take_time Statistics.t_tmp2 (cps r1)

  let combine_subsumed rl rl' =
    if is_subsumed rl rl' then Some rl'
    else if is_subsumed rl' rl then Some rl
    else None
  ;;

  let combine r1 r2 = if r1 = r2 then Some r1 else None
  
  let rewriter_nf_with rewriter ((s,t) as rl) =
    let s', rs = rewriter#nf s in
    let t', rt = rewriter#nf t in
    let rls = List.map fst (rs @ rt) in
    if s' = t' then Some([], [], rls)
    else if R.equal rl (s',t') then None
    else (
      if !(Settings.do_proof) then
        Trace.add_rewrite (normalize (s',t')) (s,t) (rs,rt);
      Some ([], [s', t'], rls))
  ;;
  
  let joins trs (s,t) = 
    let _, s' = Rewriting.nf_with trs s in
    let _, t' = Rewriting.nf_with trs t in
    s' = t'
  ;;

  let le rl rl' = R.size rl <= R.size rl'

  let print ppf (l, r) =
    let s = R.size (rule (l,r)) in
    Format.fprintf ppf "%a = %a (%i)" Term.print l Term.print r s

  let is_ac_equivalent acs (l,r) = Term.flatten acs l = Term.flatten acs r
end


module ConstraintEquality = struct
  type t = R.t * Logic.t

  let terms = fst

  let rule = fst

  let compare (e,c) (e',c') =
    let cmp = R.compare e e' in
    if cmp <> 0 then cmp else compare c c'
  ;;

  let equal ec ec' = (compare ec ec') = 0

  let of_rule ctx rl = (rl, Logic.mk_true ctx)

  let is_trivial ((s,t), c) = Term.compare s t = 0 || Logic.is_false c

  let normalize (st, c) = Variant.normalize_rule st, c

  let not_increasing ((l,r), _) = not (Term.is_subterm l r)

  let flip (rl, c) = R.flip rl, c

  let rule_map f (e, c) = (f e, c)

  let combine (r1,c1) (r2,c2) =
    if r1 = r2 then Some (r1, c1 <|> c2) else None
  ;;

  (* FIXME: overapproximation, actually constraint implication should be
           nf_with checked *)
  let combine_subsumed (rl, c) (rl',c') =
    match Equation.combine_subsumed rl rl' with
      | Some st -> Some (st, c <&> c')
      | None -> None
  ;;

  let cps (r1,c1) (r2,c2) =
    [ O.cp_of_overlap o, c1 <&> c2 | o <- O.overlaps_between r1 r2 ]

  (* FIXME: does not actually use rewriter *)
  let rewriter_nf_with _ _ = failwith "nf not implemented"

  let joins trs ((s,t), _) = 
    let _, s' = Rewriting.nf_with trs s in
    let _, t' = Rewriting.nf_with trs t in
    s' = t'
  ;;

  let le rl rl' = R.size (rule rl) <= R.size (rule rl')

  let is_ac_equivalent acs ((l,r),_) = Term.flatten acs l = Term.flatten acs r

  let print ppf ((l,r),_) = Format.fprintf ppf "%a = %a" T.print l T.print r
end