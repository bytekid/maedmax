module O = Overlap
module T = Trace
module F = Format

open Settings

module LitHash = struct
  type t = literal
  let equal l l' = l.terms = l'.terms && l.is_equality = l'.is_equality
  let hash l = Hashtbl.hash (l.hash, l.is_equality)
end

module H = Hashtbl.Make(LitHash)

type t = Settings.literal

let sizes : (int, int*int) Hashtbl.t = Hashtbl.create 100

let last_id = ref 0

let terms l = l.terms

let size l = Rule.size (l.terms)

let print_sizes _ = 
  let show (k,(v,vg)) = F.printf "size %d: (%d,%d)\n%!" k v vg in
  let sz = Hashtbl.fold (fun k v l -> (k,v)::l) sizes [] in
  List.iter show (List.sort (fun (a,_) (b,_) -> compare a b) sz)
;;

let print ppf l =
  let eq = if l.is_equality then "=" else "!=" in
  F.fprintf ppf "%d: %a %s %a (%d)" l.id Term.print (fst l.terms) eq Term.print (snd l.terms) (size l)
;;

let to_string l = F.flush_str_formatter (print F.str_formatter l)

let compare l l' = compare (l.terms, l.is_equality) (l'.terms, l'.is_equality)

let is_equal l l' = compare l l' = 0

let make ts e =
  let i = !last_id in
  last_id := i + 1;
  {terms = ts; is_equality = e; hash = Hashtbl.hash ts; id = i }
;;

let change l ts = {l with terms = ts; hash = Hashtbl.hash ts}

module LightTrace = struct
  type origin =
    | Initial
    | Rewrite of literal * (Rule.t list * Rule.t list)
    | CP of literal * literal
    | Rename of literal
  
  let history : (literal * origin) H.t = H.create 128

  let origin_string =
    let soi i = string_of_int i in
    function
    | Initial -> "Initial"
    | Rewrite (l, _) -> "Rewrite(" ^ (soi l.id) ^ ")" 
    | Rename l -> "Rename(" ^ (soi l.id) ^ ")" 
    | CP (l1, l2) -> "CP(" ^ (soi l1.id) ^ "," ^ (soi l2.id) ^ ")"
  ;;

  let add l o = H.add history l (l, o)

  let find_origin l =
    let find l =
      match List.rev (H.find_all history l) with x :: _ -> Some x | _ -> None
    in
    let ln = make (Variant.normalize_rule l.terms) l.is_equality in
    let orig_l, orig_ln = find l, find ln in
    match orig_l, orig_ln with
    | Some o, None
    | None, Some o -> o
    | Some (l0,o0), Some (l1, o1) ->
      if l0.id < l1.id then (l0,o0) else (l1, o1)
    | _-> failwith ((to_string l) ^ ": literal not found in trace")
  ;;

  let find_origin_rule rl = find_origin (make rl true)

  let find_equation rl = fst (find_origin (make rl true))

  let find_goal rl = fst (find_origin (make rl false))

  let parents = function
  | Initial -> []
  | Rewrite (l, (ls, rs)) -> l :: [find_equation r | r <- ls @ rs]
  | Rename l -> [l]
  | CP (l1, l2) -> [l1; l2]
  ;;

  let trace_origin = function
  | Initial -> Initial
  | Rewrite (l, (ls, rs)) -> Rewrite (fst (find_origin l), (ls, rs))
  | Rename l -> Rename (fst (find_origin l))
  | CP (l1, l2) -> CP(fst (find_origin l1), fst (find_origin l2))
  ;;

  let add_initials eqs = List.iter (fun e -> add e Initial) eqs

  let add_overlap eq (l1, l2) = add eq (CP (l1, l2))
  
  let add_rewrite eq eq0 steps = add eq (Rewrite (eq0, steps))
  
  let add_rename eq eq0 = add eq (Rename eq0)

  let ancestors eqs =
    let diff xs ys = 
      List.filter (fun x -> not (List.exists (fun y -> x.id = y.id) ys)) xs
    in
    if Settings.do_proof_debug () then (
      Format.printf "ANCESTORS\n%!";
      List.iter (fun e -> Format.printf "  %a\n\n" print e) eqs);
    let ids ps = List.fold_left (^) "" [string_of_int p.id ^ " " | p <- ps] in
    let acc_eqs acc = [l | l, _ <- acc] in
    let lit_cmp (l,_) (l',_) = Pervasives.compare l.id l'.id in
    (* invariant: second argument does not intersect with first *)
    let rec ancestors acc = function
      | [] -> acc
      | l :: ls ->
        (*assert (not (List.mem l (acc_eqs acc)));*)
        let l0, o = find_origin l in
        if Settings.do_proof_debug () then
          Format.printf "  %a = %a (from %s)\n" print l print l0 (ids (parents o));
        (*assert (l0.id <= l.id);*)
        let accx = Listx.unique ~c:lit_cmp ((l0, trace_origin o) :: acc) in
        let acc' = ancestors accx (diff (parents o) (acc_eqs accx)) in
        ancestors acc' (diff ls (acc_eqs acc'))
    in
    ancestors [] eqs
  ;;

  let clear _ = H.reset history
end

let killed = ref 0

let is_equality l = l.is_equality

let is_inequality l = not l.is_equality

let negate l = { l with is_equality = not l.is_equality }

let flip l = change l (Rule.flip l.terms)

let is_subsumed l l' =
  Rule.is_instance l.terms l'.terms ||
  Rule.is_instance (Rule.flip l.terms) l'.terms
;;

let is_trivial l = fst l.terms = snd l.terms

let normalize l = make (Variant.normalize_rule l.terms) l.is_equality

let rename l = make (Rule.rename l.terms) l.is_equality

let not_increasing l = not (Term.is_subterm (fst l.terms) (snd l.terms))

(* Iff none of the literals is a goal, filter out trivial CPs *)
(*let cps h l l' =
  if is_inequality l && is_inequality l' then []
  else
    let r1, r2 = l.terms, l'.terms in
    let os = [ O.cp_of_overlap o,o | o <- O.overlaps_between r1 r2 ] in
    let is_eq = l.is_equality && l'.is_equality in
    let os = if is_eq then [ (s,t),o | (s,t),o <- os; s <> t ] else os in
    if !(Settings.do_proof) <> None then (
      let trace = if not is_eq then T.add_overlap_goal else T.add_overlap in
      let add ((s, t), o) =
        if s <> t then trace (Variant.normalize_rule (s, t)) o
      in List.iter add os);
    let os' = [o | o, _ <- os; Rule.size o <= h.hard_bound_goals] in
    [make (Variant.normalize_rule o) is_eq | o <- os']
;;

(* FIXME if used, hard bound should be incorporated *)
let pcps rew l l' =
  let prime ((l,_),_,_,tau) = rew#is_nf_below_root (Term.substitute tau l) in
  if not l.is_equality && not l'.is_equality then []
  else
    let r1, r2 = l.terms, l'.terms in
    let os = [ O.cp_of_overlap o,o | o <- O.overlaps_between r1 r2; prime o ] in
    let is_eq = l.is_equality && l'.is_equality in
    if !(Settings.do_proof) <> None then (
      let trace = if not is_eq then T.add_overlap_goal else T.add_overlap in
      let add ((s,t),o) =
        if s <> t then trace (Variant.normalize_rule (s, t)) o
      in List.iter add os);
    [ make (Variant.normalize_rule (fst o)) is_eq | o <- os ]
;;*)

let rewriter_nf_with ?(max_size = 0) l rewriter =
  let ts = l.terms in
  let s', rs = rewriter#nf (fst ts) in
  let sz_s = Term.size s' in
  if max_size <> 0 && sz_s > max_size then
    raise Rewriter.Max_term_size_exceeded;
  let t', rt = rewriter#nf (snd ts) in
  if max_size <> 0 && Term.size t' + sz_s > max_size then
    raise Rewriter.Max_term_size_exceeded;
  let rls = List.map (fun (rl,_,_) -> rl) (rs @ rt) in
  if s' = t' && l.is_equality then (
    if !(Settings.do_proof) = Some CPF then (
      let st' = Variant.normalize_rule (s', t') in
      T.add_rewrite st' ts (rs, rt));
    Some([], rls))
  else if Rule.equal ts (s', t') then None
  else (
    let st' = Variant.normalize_rule (s', t') in
    let g = make st' l.is_equality in
    (if !(Settings.do_proof) = Some TPTP then 
      LightTrace.add_rewrite g l ([r | r, _, _ <- rs], [r | r, _, _ <- rt])
     else if !(Settings.do_proof) = Some CPF then
      let trc = if is_inequality l then T.add_rewrite_goal else T.add_rewrite in
      trc st' ts (rs, rt));
    Some ([g], rls))
;;
  
let joins l trs =
  let _, s' = Rewriting.nf_with trs (fst l.terms) in
  let _, t' = Rewriting.nf_with trs (snd l.terms) in
  s' = t'
;;

let is_ac_equivalent l fs = Theory.Ac.equivalent fs l.terms

let equiv_table : (Rule.t * Rule.t, bool) Hashtbl.t = Hashtbl.create 256

let are_ac_equivalent acs l l' =
  if acs = [] then false
  else (
    try Hashtbl.find equiv_table (l.terms, l'.terms)
    with Not_found ->
      let (s,t),(s',t') = l.terms, l'.terms in
      let eq = Theory.Ac.equivalent acs (s,s') &&
              Theory.Ac.equivalent acs (t,t') in
      Hashtbl.add equiv_table (l.terms, l'.terms) eq;
      Hashtbl.add equiv_table (l'.terms, l.terms) eq;
      eq)
;;

let cequiv_table : (Rule.t * Rule.t, bool) Hashtbl.t = Hashtbl.create 256

let are_c_equivalent cs l l' =
  try Hashtbl.find cequiv_table (l.terms, l'.terms)
  with Not_found ->
    let (s,t),(s',t') = l.terms, l'.terms in
    let eq = Theory.Commutativity.equivalent cs (s,s') &&
             Theory.Commutativity.equivalent cs (t,t') in
    Hashtbl.add cequiv_table (l.terms, l'.terms) eq;
    Hashtbl.add cequiv_table (l'.terms, l.terms) eq;
    eq
;;

let is_ground l = Rule.is_ground l.terms

let make_axiom ts = make ts true

let make_neg_axiom ts = make ts false

let is_unifiable l = let u,v = l.terms in Subst.unifiable u v

let substitute sigma l = make (Rule.substitute sigma l.terms) l.is_equality

let substitute_uniform t l =
  let sub = Term.substitute_uniform t in
  make (sub (fst l.terms), sub (snd l.terms)) l.is_equality
;;

let signature l = Rule.signature l.terms

let variables l = Rule.variables l.terms

let compare_size l l' = Pervasives.compare (size l) (size l')
