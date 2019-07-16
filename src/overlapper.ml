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

class reducibility_checker (trs : Rules.t) = object (self)

val red_table : (Term.t, bool) H.t = H.create 256
val red_table_below : (Term.t, bool) H.t = H.create 256
val mutable index = FingerprintIndex.create [ l, l | l, _ <- trs]

(* Returns whether term [t] is reducible below the root. *)
method is_reducible_below t =
let tt = Unix.gettimeofday () in
let res = 
let t = Variant.normalize_term t in
try H.find red_table_below t with
Not_found -> (
  let is_reducible = 
    match t with
      | Term.V _ -> false
      | Term.F(_, ts) -> List.exists self#is_reducible ts
  in 
  H.add red_table_below t is_reducible;
  (*if is_reducible then Format.printf "%a is reducible below root\n%!" Term.print t;*)
  is_reducible)
  in
  A.t_tmp2 := !A.t_tmp2 +. (Unix.gettimeofday () -. tt);
  res
;;

(* Returns whether term [t] is reducible. *)
method is_reducible t = 
  try H.find red_table t with
  Not_found -> (
    let is_reducible = 
      match t with
        | Term.V _ -> false
        | Term.F(_, ts) -> self#matches t || List.exists self#is_reducible ts
    in 
    H.add red_table t is_reducible;
    is_reducible)
;;

(* Finds rules that match at root *)
method matches t =
  let rs = FingerprintIndex.get_matches t index in
  List.exists (fun l -> Subst.is_instance_of t l) rs
;;
end

class overlapper (h : heuristic) (lits : Literal.t list) (trs : Rules.t)
 = object (self)

  val unif_cache : (Term.t, (Literal.t * int) list) H.t = H.create 256
  val mutable index = FingerprintIndex.empty []
  val rcheck = new reducibility_checker trs
  val pcp = false

  method init () =
    let data l = fst (Lit.terms l), (l, Term.size (snd (Lit.terms l))) in
    let ixd = [ data l | l <- lits; Lit.not_increasing l ] in
    index <- FingerprintIndex.create ixd;
  ;;

  method add_symm (s,t) =
    let l, l' = Lit.make_axiom (s,t), Lit.make_axiom (t,s) in
    let eqs = [s, (l, Term.size t); t, (l', Term.size s)] in
    index <- FingerprintIndex.add eqs index
  ;;
  
  method add (s,t) =
    let l = Lit.make_axiom (s,t) in
    index <- FingerprintIndex.add [s, (l, Term.size t)] index
  ;;

  (* Returns terms unifiable with t. Lookup in table, otherwise use index. *)
  method unifiables t = 
    try H.find unif_cache t with
    Not_found -> (
      let us = FingerprintIndex.get_unifiables t index in
      H.add unif_cache t us;
      us)
  ;;

  (* Computes CPs with given (outer) rule. *)
  method cps ?(only_new=false) rl =
    let l_pos = T.function_positions (fst (Lit.terms rl)) in
    let check (rl1, _, rl2, _) = Cache.consider_overlap rl1 rl2; true in
    let cps = [e | p <- l_pos; e <- self#cps_at only_new rl p] in
    [ cp | cp, o <- cps; check o]
  ;;
  
  (* as in Overlap module, but without variant optimization; rule2 is outer *)
  method overlap_between_at only_new rule1 rule2 p =
    if only_new && Cache.overlap_was_considered rule1 rule2 then None
    else (
    let l1,r1 = rule1 and l2, r2 = Rule.rename_canonical rule2 in
    match mgu (Term.subterm_at p l2) l1 with
      | Some sigma ->
        let t = Term.substitute sigma l1 in
        if pcp && Term.size t > 5 && rcheck#is_reducible_below t then None
        else Some ((l1, r1), p, (l2, r2), sigma)
      | None -> None
    )

  (* rli is inner, rlo is outer *)
  method cp_at only_new rli rlo p =
    if Lit.is_inequality rli && Lit.is_inequality rlo then None
    else (
      let is_equality = Lit.is_equality rli && Lit.is_equality rlo in
      let bd =
        if Lit.is_inequality rlo then h.hard_bound_goals else h.hard_bound_equations
      in
      let o = self#overlap_between_at only_new (Lit.terms rli) (Lit.terms rlo) p in
      match o with
        | None -> None
        | Some o -> (
          let s,t = O.cp_of_overlap o in
          if Rule.size (s, t) > bd then None
          else if s = t && is_equality then None
          else (
            let st' = V.normalize_rule (s,t) in
            if !(Settings.do_proof) <> None then
              (if not is_equality then
                Trc.add_overlap_goal else Trc.add_overlap) st' o;
            Some (Lit.make st' is_equality, o))))
;;

  (* Computes CPs with given rule at position p in l. *)
  method cps_at only_new rl p =
    let l,r = Lit.terms rl in
    let l' = Term.subterm_at p l in
    let rs = self#unifiables l' in
    let is_ineq = Lit.is_inequality rl in
    let bd = if is_ineq then h.hard_bound_goals else h.hard_bound_equations in
    let max_size = bd - (Lit.size rl - (Term.size l')) in
    let add os = function None -> os | Some o -> o :: os in
    let rl_cands = [rl' | rl', s <- rs; s <= max_size] in
    List.fold_left add [] [ self#cp_at only_new rl' rl p | rl' <- rl_cands ]
  ;;
end


class overlapper_with (trs : (Rule.t * Logic.t) list) = object (self)

  val unif_cache : (Term.t, (Rule.t * Logic.t) list) H.t = H.create 256
  val mutable index = FingerprintIndex.empty []

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
