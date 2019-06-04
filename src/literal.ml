module O = Overlap
module T = Trace
module DC = DismatchingConstraints
module F = Format

open Settings

type t = Settings.literal

let sizes : (int, int*int) Hashtbl.t = Hashtbl.create 100

let print_sizes _ = 
  let show (k,(v,vg)) = F.printf "size %d: (%d,%d)\n%!" k v vg in
  let sz = Hashtbl.fold (fun k v l -> (k,v)::l) sizes [] in
  List.iter show (List.sort (fun (a,_) (b,_) -> compare a b) sz)
;;

let print ppf l =
  let eq = if l.is_equality then "=" else "!=" in
  F.fprintf ppf "%a %s %a" Term.print (fst l.terms) eq Term.print (snd l.terms)
;;

let print_with_dconstr ppf l = F.fprintf ppf "%a [%a]" print l DC.print l.dconstr

let to_string l = F.flush_str_formatter (print F.str_formatter l)

let killed = ref 0

let make_dc ts e dc = {terms = ts; is_equality = e; dconstr = dc }

let make ts e = make_dc ts e []

let terms l = l.terms

let size l = Rule.size (l.terms)

let is_equality l = l.is_equality

let is_inequality l = not l.is_equality

let dconstr l = l.dconstr

let is_equal l l' = compare l l' = 0

let negate l = { l with is_equality = not l.is_equality }

let flip l = { l with terms = Rule.flip l.terms }

let is_subsumed l l' =
  Rule.is_instance l.terms l'.terms ||
  Rule.is_instance (Rule.flip l.terms) l'.terms
;;

let is_trivial l = fst l.terms = snd l.terms

let normalize l = { l with terms = Variant.normalize_rule l.terms }

let rename l = { l with terms = Rule.rename l.terms }

let add_dconstr l dc = { l with dconstr = DC.add dc l.dconstr}

let not_increasing l = not (Term.is_subterm (fst l.terms) (snd l.terms))

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
    if !(Settings.do_proof) <> None then (
      let st' = Variant.normalize_rule (s', t') in
      T.add_rewrite st' ts (rs, rt);
      T.add_delete st');
    Some([], rls))
  else if Rule.equal ts (s', t') then None
  else (
    let st' = Variant.normalize_rule (s', t') in
    let g = make_dc st' l.is_equality l.dconstr in
    (if !(Settings.do_proof) <> None then
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

let substitute sigma l = { l with terms = Rule.substitute sigma l.terms }

let substitute_uniform t l =
  let sub = Term.substitute_uniform t in
  { l with terms = (sub (fst l.terms), sub (snd l.terms)) }
;;

let variables l = Rule.variables l.terms

let compare_size l l' = compare (size l) (size l')
