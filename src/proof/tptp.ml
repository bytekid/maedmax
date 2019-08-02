(*** MODULES *****************************************************************)
module F = Format
module H = Hashtbl
module T = Literal.LightTrace
module Lit = Literal

module OrdInt = struct
  type t = int
  let compare = Pervasives.compare
end

module IntMap = Map.Make(OrdInt)

(*** OPENS *******************************************************************)
open Settings

(*** FUNCTIONS ***************************************************************)
let name idx l =
  let name id = "eq_" ^ (string_of_int (IntMap.find id idx)) in
  try name l.id
  with Not_found ->
    (* strange effects with nodes occuring twice *)
    let ln = Lit.make (Variant.normalize_rule l.terms) l.is_equality in
    let l', _ = T.find_origin ln in
    name l'.id
;;

let rewrite_inference idx parent (lsteps,rsteps) ppf =
  let rlname rl = name idx (fst (T.find_origin_rule rl)) in
  let rec print_steps initial = function
    | [] -> F.fprintf ppf "%s" (name idx initial)
    | rl :: steps ->
      F.fprintf ppf "@[<2>inference(rw,@ [status(thm)],@ [";
      print_steps initial steps;
      F.fprintf ppf ",@ %s])@]" (rlname rl);
  in
  print_steps parent (List.rev (lsteps @ rsteps))
;;

let cp_inference idx rl1 rl2 ppf =
  F.fprintf ppf "@[<2>inference(cp,@ [status(thm)],@ [%s, %s])@]"
    (name idx rl1) (name idx rl2)
;;

let axiom filename ppf = F.fprintf ppf "file('%s')" filename

let store_max steps =
  let cmp (me, mg) (l, _) = 
    let s = Lit.size l in
    if Lit.is_equality l then (max s me, mg) else (me, max s mg)
  in
  let me, mg = List.fold_left cmp (0,0) steps in
  Analytics.max_equation_size := me;
  Analytics.max_goal_size := mg
;;

let sort_history aged_ancestors =
  let age_compare (a, _) (b, _) = Pervasives.compare a.id b.id in
  let res = List.sort age_compare aged_ancestors in
  if Settings.do_proof_debug () then (
    Format.printf "sorted ancestors:\n";
    List.iter (fun (e,o) -> F.printf "  %a: %s\n%!"
      Lit.print e (Lit.LightTrace.origin_string o)) res);
  let add_index m (i, (l, _)) = IntMap.add l.id i m in
  let index = List.fold_left add_index IntMap.empty (Listx.index res) in
  store_max res;
  res, index
;;

let print_step ppf filename idx (lit, o) =
  let src, kind =
    match o with
    | T.Initial -> axiom filename, "axiom"
    | T.Rename parent ->
      rewrite_inference idx parent ([],[]), "plain"
    | T.Rewrite (parent, steps) ->
      rewrite_inference idx parent steps, "plain"
    | T.CP (rl1, rl2) -> cp_inference idx rl1 rl2, "plain"
  in
  let goal = not (Lit.is_equality lit) in
  let kind' = if goal then "negated_conjecture" else kind in
  let op = if goal then "!=" else "=" in
  F.fprintf ppf "@[<2>cnf(%s,@ %s,@ @[<2>(%a)@],@ "
    (name idx lit) kind' (Rule.print_with op) (Lit.terms lit);
  src ppf;
  F.fprintf ppf ").@]@."
;;

let print_trivial_model ppf es trs filename =
  F.fprintf ppf
    "%s SZS status Satisfiable\n" "%";
    F.fprintf ppf "%s SZS output start Model for %s@." "%" filename;
  F.fprintf ppf "fof(interpretation_domain, fi_domain, (! [X]: ( X = e0 ))).\n";
  let rec e0s n = if n <= 1 then "e0" else e0s (n-1) ^ ",e0" in
  let args n = if n = 0 then "" else "(" ^ (e0s n) ^ ")" in
  let print_interpretation (f, a) =
    F.fprintf ppf "fof(interpretation_terms, fi_functors, ( %s%s = e0)).\n"
      (Signature.get_fun_name f) (args a)
  in
  List.iter print_interpretation (Rules.signature es);
  F.fprintf ppf "%s SZS output end Model@." "%"
;;

let print_saturation ppf trs filename =
  let steps, idx = sort_history (T.ancestors [T.find_equation r | r <- trs]) in
  F.fprintf ppf
    "%s SZS status Satisfiable\n%s SZS output start Saturation for %s@."
      "%" "%" filename;
  List.iter (print_step ppf filename idx) steps;
  F.fprintf ppf "@.%s SZS output end Saturation@." "%"
;;

let get_goal_steps g_origs (s, t) (rs, rt) u =
  if s = t then (
    T.ancestors [T.find_goal (s, t)]
  ) else (
    let g_st = T.find_goal (s, t) in
    let l_st_orig = T.find_origin g_st in
    let l_u = Lit.make_neg_axiom (u, u) in
    let ancs = T.ancestors (g_st :: [T.find_equation r | r <- rs @ rt]) in
    [l_u, T.Rewrite (fst l_st_orig, (rs, rt))] @ ancs)
;;

let check steps =
  let has ss l =
    if List.exists (fun (l',_) -> l.id = l'.id) ss then true
    else (Format.printf "%a not found\n" Lit.print l; false)
  in
  let rec check = function
  | [] -> ()
  | (_, o) :: ss -> (assert (List.for_all (has ss) (T.parents o)); check ss)
  in check (List.rev steps)
;;

let print_goal_proof ppf filename eqs gs st (rs, rt) u sigma =
  let steps, idx = sort_history (get_goal_steps gs st (rs, rt) u) in
  F.fprintf ppf
    "%s SZS status Unsatisfiable\n%s SZS output start CNFRefutation for %s@."
      "%" "%" filename;
  List.iter (print_step ppf filename idx) steps;
  let contradiction, _ = List.hd (List.rev steps) in
  F.fprintf ppf "cnf(bot, %s, ($false), inference(cn, [status(thm)], [%s]))."
    "negated_conjecture" (name idx contradiction);
  F.fprintf ppf "@.%s SZS output end CNFRefutation@." "%";
  (*check steps*)
;;

let fprint_proof ppf filename (es,gs) = function
  | Settings.Proof (goal, (rs, rt), u, sigma)
    (*when List.for_all Literal.is_equality es && List.length gs = 1*) ->
    let eqs = List.map Literal.terms es in
    let gs = [Variant.normalize_rule (Literal.terms g) | g <- gs] in
    let rl_p_sub = List.map (fun (rl, p, r, _) -> rl) in
    print_goal_proof ppf filename eqs gs goal (rl_p_sub rs, rl_p_sub rt) u sigma
  | Settings.Completion rr ->
    print_trivial_model ppf [Lit.terms e | e <- es] rr filename
  | Settings.GroundCompletion (rr,ee,o) -> (* no goal exists *)
    print_trivial_model ppf [Lit.terms e | e <- es]  (rr @ ee) filename
  | Settings.Disproof (rr, ee, o, steps) ->
    print_saturation ppf (rr @ ee) filename
;;

let print_proof = fprint_proof F.std_formatter

let proof_string filename input prf =
  fprint_proof F.str_formatter filename input prf;
  F.flush_str_formatter ()
;;
