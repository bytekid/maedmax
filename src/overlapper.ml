module T = Term
module L = List
module H = Hashtbl
module Sig = Signature
module O = Overlap
module V = Variant
module Lit = Literal

type term_cmp = Term.t -> Term.t -> bool

exception Not_orientable

class overlapper (trs : Literal.t list) = object (self)

  val unif_cache : (Term.t, Literal.t list) H.t = H.create 256
  val mutable index = FingerprintIndex.empty

  method init () =
    let indexed = [ fst (Lit.terms l),l | l <- trs; Lit.not_increasing l ] in
    index <- FingerprintIndex.create indexed
  ;;

  method trs = trs

  (* Returns terms unifiable with t. Lookup in table, otherwise use index. *)
  method unifiables t = 
    try H.find unif_cache t with
    Not_found -> (
      let us = FingerprintIndex.get_unifiables t index in
      H.add unif_cache t us;
      us)
  ;;

  (* Computes CPs with given rule. *)
  method cps rl =
    let l = fst (Lit.terms rl) in
    List.concat [ self#cps_at rl p | p <- T.function_positions l ]
  ;;

  method cp_at rli rlo p = (* rli is inner, rlo is outer *)
    if Lit.is_inequality rli && Lit.is_inequality rlo then None
    else
      match O.overlap_between_at (Lit.terms rli) (Lit.terms rlo) p with
        | None -> None
        | Some o ->
          let s,t = O.cp_of_overlap o in
          let is_equality = Lit.is_equality rli && Lit.is_equality rlo in
          let is_goal = Lit.is_goal rlo in
          if s = t && is_equality && not is_goal then None
          else Some (Lit.make (V.normalize_rule (s,t)) is_equality is_goal)
;;

  (* Computes CPs with given rule at position p in l. *)
  method cps_at rl p =
    let l,r = Lit.terms rl in
    let rs = self#unifiables (Term.subterm_at p l) in
    let add os = function None -> os | Some o -> o :: os in
    List.fold_left add [] [ self#cp_at rl' rl p | rl' <- rs ]
(*
    let os' = [ O.overlap_between_at rl (l,r) p | rl <- rs ] in
    let add os = function None -> os | Some o -> o :: os in
    let cps = [ O.cp_of_overlap o,o | o <- List.fold_left add [] os' ] in
    let os = [ (s,t),o | (s,t),o <- cps; s <> t ] in
    let res = [ Lit.make (V.normalize_rule (fst o)) is_eq is_goal | o <- os] in
    res*)
  ;;
end


class overlapper_with (trs : (Rule.t * Yicesx.t) list) = object (self)

  val unif_cache : (Term.t, (Rule.t * Yicesx.t) list) H.t = H.create 256
  val mutable index = FingerprintIndex.empty

  method init () =
    let is_rule (l,r) = Rule.is_rule (l,r) && (not (Term.is_subterm l r)) in
    index <- FingerprintIndex.create [ fst lr,(lr,v) | lr,v <- trs; is_rule lr ]
  ;;

  (* Returns terms unifiable with t. Lookup in table, otherwise use index. *)
  method unifiables t = 
    try H.find unif_cache t with
    Not_found -> (
      let us = FingerprintIndex.get_unifiables t index in
      H.add unif_cache t us;
      us)
  ;;

  (* Computes CPs with given rule. *)
  method cps rl =
    List.concat [ self#cps_at rl p | p <- T.function_positions (fst rl) ]
  ;;

  method cp_at rli rlo p = (* rli is inner, rlo is outer *)
    match O.overlap_between_at rli rlo p with
      | None -> None
      | Some o ->
        let s,t = O.cp_of_overlap o in
        if s = t then None else Some (s,t)
;;

  (* Computes CPs with given rule at position p in l. *)
  method cps_at ((l,r) as rl) p =
    let rs = self#unifiables (Term.subterm_at p l) in
    let add os = function None, _ -> os | Some o,v -> (o,v) :: os in
    List.fold_left add [] [ self#cp_at rl' rl p,v | rl', v <- rs ]
  ;;
end
