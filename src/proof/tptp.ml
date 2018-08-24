(*** MODULES *****************************************************************)
module F = Format
module H = Hashtbl
module T = Trace

(*** FUNCTIONS ***************************************************************)
let name eqindex eq =
  let e = Variant.normalize_rule eq in
  let c = 
    try H.find eqindex e
    with _ -> (
      let c = H.length eqindex in
      H.add eqindex e c;
      c
    )
  in
  "eq_" ^ (string_of_int c)
;;

let rewrite_inference eqindex parent (lsteps,rsteps) ppf =
  let rec print_steps initial = function
    | [] -> F.fprintf ppf "%s" initial
    | (rl, _) :: steps ->
      let n = name eqindex rl in
      F.fprintf ppf "@[<2>inference(rw,@ [status(thm)],@ [";
      print_steps initial steps;
      F.fprintf ppf ",@ %s])@]" n;
  in
  print_steps (name eqindex parent) (List.rev (lsteps @ rsteps))
;;

let cp_inference eqindex rl1 rl2 ppf =
  let n1, n2 = name eqindex rl1, name eqindex rl2 in
  F.fprintf ppf "@[<2>inference(cp,@ [status(thm)],@ [%s, %s])@]" n1 n2
;;

let axiom filename ppf = F.fprintf ppf "file('%s')" filename


let print_step ppf ?(goal = false) filename eqindex (eqn, o) =
  let src, kind =
    match o with
    | T.Initial -> axiom filename, "axiom"
    | T.Rewrite (parent, steps) ->
      rewrite_inference eqindex parent steps, "plain"
    | T.CP (rl1, _, rl2) -> cp_inference eqindex rl1 rl2, "plain"
  in
  let kind' = if goal then "negated_conjecture" else kind in
  let n = name eqindex eqn in
  let op = if goal then "!=" else "=" in
  F.fprintf ppf "@[<2>cnf(%s,@ %s,@ @[<2>(%a)@],@ "
    n kind' (Rule.print_with op) eqn;
  src ppf;
  F.fprintf ppf ").@]@."
;;

let print_saturation ppf trs filename =
  let eqindex : (Rule.t, int) H.t = H.create 128 in
  let steps = T.ancestors trs in
  F.fprintf ppf
    "%s SZS status Satisfiable\n%s SZS output start Saturation@." "%" "%";
  List.iter (print_step ppf filename eqindex) steps;
  F.fprintf ppf "@.%s SZS output end Saturation@." "%"
;;

let print_goal_proof ppf filename eqs g_orig ((s, t) as st) (rsx, rtx) sigma =
  let rs,rt = [r, p | r, p, _ <- rsx], [r, p | r, p, _ <- rtx] in
  let goal_origin = T.Rewrite (g_orig, (rs, rt)) in
  let grls, gsteps =
    if st <> g_orig then (
      let o = try fst (H.find T.goal_trace_table st) with _ -> T.Initial in
      H.add T.goal_trace_table g_orig (T.Initial, -1);
      T.goal_ancestors st o
    ) else (
      let s' = T.last (s, T.rewrite_conv s rs) in
      let t' = T.last (t, T.rewrite_conv t rt) in
      assert (Subst.unifiable s' t');
      let u = Term.substitute (Subst.mgu s' t') s' in
      [], [g_orig, T.Initial; (u, u), goal_origin])
  in
  let rls = Listx.unique ([r | r, _ <- rs @ rt] @ grls) in
  let steps = T.ancestors rls in
  F.fprintf ppf
    "%s SZS status Unsatisfiable\n%s SZS output start CNFRefutation@." "%" "%";
  let eqindex : (Rule.t, int) H.t = H.create 128 in
  List.iter (print_step ppf filename eqindex) steps;
  List.iter (print_step ppf ~goal:true filename eqindex) gsteps;
  let contradiction, _ = List.hd (List.rev gsteps) in
  F.fprintf ppf "cnf(bot, %s, ($false), inference(cn, [status(thm)], [%s]))."
    "negated_conjecture" (name eqindex contradiction);
  F.fprintf ppf "@.%s SZS output end CNFRefutation@." "%"
;;

let fprint_proof ppf filename (es,gs) = function
  | Settings.Proof ((s,t),(rs, rt), sigma)
    when List.for_all Literal.is_equality es && List.length gs = 1 ->
    let g_orig = Literal.terms (List.hd gs) in
    let eqs = List.map Literal.terms es in
    let g = Variant.normalize_rule g_orig in
    print_goal_proof ppf filename eqs g (s, t) (rs, rt) sigma
  | Settings.Completion rr ->
    print_saturation ppf rr filename
  | Settings.GroundCompletion (rr,ee,o) -> (* no goal exists *)
    print_saturation ppf (rr @ ee) filename
(*  | Disproof (rr,ee,o,rst) -> (* goal with different normal forms exists *)
      let g = Literal.terms (List.hd gs) in
      let es = List.map Literal.terms es in
      let p = T.xml_goal_disproof es g (rr,ee,o) rst in
      result_string p*)
  | Settings.Proof _ -> failwith "Tptp.show_proof: proof type not supported"
  | Settings.Disproof _ -> failwith "Tptp.show_proof: disproof not supported"
;;

let print_proof = fprint_proof F.std_formatter

let proof_string filename input prf =
  fprint_proof F.str_formatter filename input prf;
  F.flush_str_formatter ()
;;