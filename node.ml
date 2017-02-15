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
  (* Compute normal form of term with respect to rules. Upon progress, return
    pair (old, ns) of (modified) old and new nodes. Result is not normalized  *)
  val nf_with : t list -> t -> (t list * t list * R.t list) option
  (* Compute normal form of term with respect to rules. Result is not
     normalized  *)
  val rewriter_nf_with : Rewriter.rewriter -> t ->
    (t list * t list * R.t list) option
  (* whether the TRS joins the equation *)
  val joins : Rules.t -> t -> bool
  (* less-than-or-equal, to fit Ordered module type for heaps *)
  val le: t -> t -> bool
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

  let normalize = Statistics.take_time Statistics.t_tmp2 normalize

  let not_increasing (l,r) = not (Term.is_subterm l r)

  let cps r1 r2 = [ O.cp_of_overlap o | o <- O.overlaps_between r1 r2 ]

  let combine_subsumed rl rl' =
    if is_subsumed rl rl' then Some rl'
    else if is_subsumed rl' rl then Some rl
    else None
  ;;

  let combine r1 r2 = if r1 = r2 then Some r1 else None

  let nf_with trs ((s,t) as rl) =
    let rs, s' = Rewriting.nf_with trs s in
    let rt, t' = Rewriting.nf_with trs t in
    if s' = t' then Some([], [], rs@rt)
    else if R.equal rl (s',t') then None
    else Some([], [s', t'], rs@rt)
  ;;  
  
  let rewriter_nf_with rewriter ((s,t) as rl) =
    let s', rs = rewriter#nf s in
    let t', rt = rewriter#nf t in
    if s' = t' then Some([], [], rs@rt)
    else if R.equal rl (s',t') then None
    else Some([], [s', t'], rs@rt)
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

  let nf_with ces ((s,t),c) =
    let trs = List.map fst ces in
    let rs_s, s' = Rewriting.nf_with trs s in
    let rs_t, t' = Rewriting.nf_with trs t in
    if (s,t) = (s', t') then None
    else
      let used (r,_) = List.exists ((=) r) (rs_s @ rs_t) in
      let sand b (_,c) = b <&> c in
      let c' = List.fold_left sand (mk_true (ctx c)) (List.filter used ces) in
      let rls' = if s' = t' then [] else [(s',t'), c <&> c'] in
      Some ([(s,t), c <&> (!! c')], rls', rs_s @ rs_t)
  ;;

  (* FIXME: does not actually use rewriter *)
  let rewriter_nf_with rewriter ((_,c) as n) =
    let ces = [ rl, mk_true (ctx c) | rl <- rewriter#trs ] in
    nf_with ces n
  ;;

  let joins trs ((s,t), _) = 
    let _, s' = Rewriting.nf_with trs s in
    let _, t' = Rewriting.nf_with trs t in
    s' = t'
  ;;

  let le rl rl' = R.size (rule rl) <= R.size (rule rl')

  let print ppf ((l,r),_) = Format.fprintf ppf "%a = %a" T.print l T.print r
end