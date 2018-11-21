(*** OPENS *******************************************************************)
open Settings

(*** MODULES *****************************************************************)
module T = Term
module L = List
module H = Hashtbl
module Sig = Signature
module O = Overlap
module V = Variant
module Lit = Literal
module A = Analytics
module Trc = Trace
module Logic = Settings.Logic

(*** TYPES ********************************************************************)
type term_cmp = Term.t -> Term.t -> bool

exception Not_orientable

(*** FUNCTIONS ****************************************************************)

let mgu_table : (Rule.t, Subst.t option) Hashtbl.t = Hashtbl.create 256

let mgu s t =
  try Hashtbl.find mgu_table (s,t)
  with Not_found -> (
    let sigma = try Some (Subst.mgu s t) with _ -> None in
    Hashtbl.add mgu_table (s,t) sigma;
    sigma
  )
;;

class overlapper (h : Settings.heuristic) (trs : Literal.t list) = object (self)

  val unif_cache : (Term.t, (Literal.t * int) list) H.t = H.create 256
  val mutable index = FingerprintIndex.empty

  method init () =
    let data l = fst (Lit.terms l), (l, Term.size (snd (Lit.terms l))) in
    let ixd = [ data l | l <- trs; Lit.not_increasing l ] in
    index <- FingerprintIndex.create ixd
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

  (* Computes CPs with given (outer) rule. *)
  method cps rl =
    let l = fst (Lit.terms rl) in
    List.concat [ self#cps_at rl p | p <- T.function_positions l ]
  ;;
  
  (* as in Overlap module, but without variant optimization *)
  method overlap_between_at rule1 rule2 p =
    let l1,r1 = rule1 and l2, r2 = Rule.rename_canonical rule2 in
    match mgu (Term.subterm_at p l2) l1 with
      | Some sigma -> Some ((l1, r1), p, (l2, r2), sigma)
      | None -> None

  (* rli is inner, rlo is outer *)
  method cp_at rli rlo p =
    if Lit.is_inequality rli && Lit.is_inequality rlo then None
    else (
      let is_equality = Lit.is_equality rli && Lit.is_equality rlo in
      let is_goal = Lit.is_goal rlo in
      let bd = if is_goal then h.hard_bound_goals else h.hard_bound_equations in
      let o = self#overlap_between_at (Lit.terms rli) (Lit.terms rlo) p  in
      match o with
        | None -> None
        | Some o -> (
          let s,t = O.cp_of_overlap o in
          if Rule.size (s, t) > bd then None
          else if s = t && is_equality && not is_goal then None
          else (
            let st' = V.normalize_rule (s,t) in
            if !(Settings.do_proof) <> None then
              (if is_goal then Trc.add_overlap_goal else Trc.add_overlap) st' o;
            Some (Lit.make st' is_equality is_goal))))
;;

  (* Computes CPs with given rule at position p in l. *)
  method cps_at rl p =
    let l,r = Lit.terms rl in
    let l' = Term.subterm_at p l in
    let rs = self#unifiables l' in
    let is_goal = Lit.is_goal rl in
    let bd = if is_goal then h.hard_bound_goals else h.hard_bound_equations in
    let max_size = bd - (Lit.size rl - (Term.size l')) in
    let add os = function None -> os | Some o -> o :: os in
    let rl_cands = [rl' | rl', s <- rs; s <= max_size] in
    let res = List.fold_left add [] [ self#cp_at rl' rl p | rl' <- rl_cands ] in
    res
  ;;
end


class overlapper_with (trs : (Rule.t * Logic.t) list) = object (self)

  val unif_cache : (Term.t, (Rule.t * Logic.t) list) H.t = H.create 256
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
  let o = O.overlap_between_at rli rlo p  in
    match o with
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
