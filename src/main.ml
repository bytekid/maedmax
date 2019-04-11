(*** MODULES *****************************************************************)
module S = Strategy
module F = Format
module Lit = Literal
module Var = Variant
module L = List

(*** OPENS *******************************************************************)
open Format
open Settings
open Yojson.Basic

(*** GLOBALS *****************************************************************)
let short_usage = "maedmax v0.9\nUsage: maedmax <options> <file>\n"
let filenames = ref []
let track_file = ref None
let classify_file = ref None

let settings = ref Settings.default
let heuristic = ref Settings.default_heuristic

(*let k = ref (-1)*)
let use_ac = ref false
let analyze = ref false
let only_termination = ref false
let only_gcr = ref false
let timeout = ref None

let strategy = ref []

let do_ordered _ =
  let h = !heuristic in
  settings := { !settings with unfailing = true };
  heuristic := { h with k = (fun _ -> 2); strategy = S.strategy_ordered }
;;

let do_concon _ =
  settings := { !settings with unfailing = true };
  heuristic := { !heuristic with
    full_CPs_with_axioms = true;
    k = (fun _ -> 2); max_oriented = 2;
    strategy = S.strategy_ordered
  }
;;

let do_unordered _ =
  settings := { !settings with unfailing = false };
  heuristic := { !heuristic with k = (fun _ -> 2); strategy = S.strategy_auto }
;;

let set_normalized th =
  match Read.file th with
  | Unit (es, [])-> settings := { !settings with norm = es }
  | _ -> failwith "Main.set_normalized: theory not found"
;;

let track_proof file =
  match Read.file file with
  | Unit (es,gs) -> Settings.track_equations := es @ gs;
  | _ -> failwith "Main.track_file: proof tracking only supports unit equality"
;;

let set_classification json =
  let classify = Select.get_classification json in
  settings := {!settings with select_classify = Some classify}
;;

let split_on_char c = Str.split (Str.regexp (String.make 1 c))

let remove_extension f =
  try Filename.chop_extension f with Invalid_argument _ -> f
;;

let set_restart_frequency s =
  let is = [int_of_string i | i <- split_on_char ',' s] in
  let order i = if i mod 2 = 0 then Strategy.ts_kbo else Strategy.ts_lpo in
  let tuple i = (order i, [], [Oriented], IterationLimit i, Size) in
  let rec build is strat =
    match is, strat with
    | [], _ -> strat
    | i :: is, [] -> tuple i :: (build is [])
    | i :: is, (o, cs, ms, _, c) :: strat ->
      (o, cs, ms, IterationLimit i, c) :: (build is strat)
  in
  heuristic := {!heuristic with strategy = build is S.strategy_ordered}
;;

let options =
  Arg.align 
  [("-ac", Arg.Unit (fun _ ->
      settings := { !settings with modulo_ac = true};
      heuristic := { !heuristic with strategy = S.strategy_ac }),
    " use AC-completion");
   ("--analyze", Arg.Unit (fun _ -> analyze := true),
     " print problem characteristics");
   ("--casc", Arg.Unit (fun _ ->
     settings := { !settings with complete_if_no_goal = false}),
     " CASC strategy");
   ("--benchmark", Arg.Set Settings.benchmark,
     " produce benchmarks");
   ("--concon", Arg.Unit do_concon,
     " satisfiability-preferring strategy");
   ("-D", Arg.Int (fun d -> settings := { !settings with debug = d };
       Settings.do_debug := d > 0),
     " print debugging output");
   ("--gcr", Arg.Unit (fun _ -> only_gcr := true),
       " check ground confluence");
   ("--interactive", Arg.Set Settings.interactive,
     " enter interactive mode once a complete system was found");
   ("--infeasible", Arg.Unit ( fun _ ->
       heuristic := { !heuristic with strategy = S.strategy_ordered_kbo };
       settings := {!settings with auto = false; infeasible = true}),
       " answers according to CoCo infeasibility semantics");
   ("--json", Arg.Unit (fun _ -> settings := { !settings with json = true }),
     " output result and stats in JSON format");
   ("-K", Arg.Int (fun k -> heuristic := { !heuristic with k = (fun _ -> k) }),
     "<k> compute k maximal terminating TRSs");
   ("--kb", Arg.Unit do_unordered,
     " Knuth-Bendix completion (unordered)");
   ("-M", Arg.String (fun s ->
      let strategy = 
        if s = "kbauto" then S.strategy_auto
        else if s = "lpo" then S.strategy_lpo
        else if s = "olpo" then S.strategy_ordered_lpo
        else if s = "okbo" then S.strategy_ordered_kbo
        else if s = "olpoorkbo" then S.strategy_ordered_lpokbo
        else if s = "kbo" then S.strategy_kbo
        else if s = "maxcomplpo" then S.strategy_maxcomp_lpo
        else if s = "maxcompkbo" then S.strategy_maxcomp_kbo
        else if s = "okbauto" then S.strategy_ordered
        else if s = "linpoly" then S.strategy_aql
        else if s = "temp" then S.strategy_temp
        else failwith "unsupported option for -M"
      in
      heuristic := { !heuristic with strategy = strategy }),
     "<mode> strategy (olpo, okbo, olpokbo)");
   ("--checksub", Arg.Int (fun n ->
     heuristic := {!heuristic with check_subsumption = n}),
     " perform subsumption checks (1,2)");
   ("--complete-if-no-goal", Arg.Unit (fun _ ->
     settings := {!settings with complete_if_no_goal = true}),
     " complete system if no goal is given");
   ("--pcp", Arg.Int (fun n -> heuristic := {!heuristic with pcp = n}),
     " only consider prime critical pairs if set to 1 (but then no caching)");
   ("--no-auto", Arg.Unit (fun _ ->
     settings := {!settings with auto = false}),
     " switch off auto mode");
   ("--keep-oriented", Arg.Unit (fun _ ->
     settings := {!settings with keep_orientation = true}),
     " preserve orientation of input axioms");
   ("--growth-eqs", Arg.Int (fun n -> heuristic := {!heuristic with n = n}),
     "<n> select <n> active equations from CPs of TRS");
     ("--growth-gls",
       Arg.Int (fun n -> heuristic := {!heuristic with n_goals = n}),
       "<n> select <n> active equations from CPs of TRS");
    ("--max-oriented", Arg.Int (fun n ->
      heuristic := { !heuristic with max_oriented = n }),
     "<n> every <n> iterations, orient as many equations as possible");
   ("--full-CPs-with-axioms", Arg.Unit (fun _ ->
     heuristic := {!heuristic with full_CPs_with_axioms = true}),
     " compute CPs with axioms in both directions");
    ("--generate-order", Arg.Unit (fun _ ->
      Settings.generate_order := true;
      heuristic := { !heuristic with strategy = S.strategy_order_generation }),
      " order generation mode");
  ("--mode", Arg.String (fun s ->
      if s = "sat" then heuristic := { !heuristic with mode = OnlySAT }
      else if s = "unsat" then heuristic := { !heuristic with mode = OnlyUNSAT }
      else failwith "unsupported mode type"),
    "<m> exclusive proof mode (sat, unsat)");
   ("--norm", Arg.String (fun t -> set_normalized t),
      "<theory> normalized completion with respect to <theory>");
   ("-P", Arg.String (fun s ->
      if s = "cpf" then (
        Settings.do_proof := Some CPF;
        heuristic := { !heuristic with hard_bound_equations = 1000};
        heuristic := { !heuristic with soft_bound_equations = 1000})
      else if s = "tstp" then Settings.do_proof := Some TPTP
      else failwith "unsupported proof type"),
     "<format> output proof (cpf, tstp)");
   ("--reduceAC-CPs", Arg.Unit (fun _ ->
     heuristic := { !heuristic with reduce_AC_equations_for_CPs = true}),
     " do not use ACx equations for CPs");
   ("--restart-frequency", Arg.String (fun s -> set_restart_frequency s),
        "<r1,..,rn> number of iterations in between forced restarts");
   ("--shape", Arg.String (fun s -> Settings.fixed_shape := s),
      "<s> fixed problem shape");
   ("--selection-mode", Arg.String (fun s ->
     let sm = 
       if s = "mixed" then MixedSelect
       else if s = "random" then RandomSelect
       else if s = "age" then AgeSelect
       else if s = "size" then SizeSelect
       else if s = "cmixed" then ClassifiedMixed
       else failwith "unsupported option for selection mode"
     in
     settings := { !settings with selection = sm }),
     "<mode> random, age, classified, or mixed (default)");
   ("--selection-classify", Arg.String (fun s -> classify_file := Some s),
      "<json> json file with decision tree(s) for classification");
   ("--sizeage", Arg.Int (fun n ->
     heuristic := { !heuristic with size_age_ratio = n}), 
     "<r> percentage of size (vs age) decisions");
   ("--soft-bound-eqs", Arg.Int (fun n ->
     heuristic := { !heuristic with soft_bound_equations = n}),
     "<b> size bound for active equations");
   ("--soft-bound-gls", Arg.Int (fun n ->
     heuristic := { !heuristic with soft_bound_goals = n}),
     "<b> size bound for active goals");
   ("--hard-bound-eqs", Arg.Int (fun n ->
     heuristic := { !heuristic with hard_bound_equations = n}),
     "<b> hard size bound for equations");
   ("--hard-bound-gls", Arg.Int (fun n ->
     heuristic := { !heuristic with hard_bound_goals = n}),
      "<b> hard size bound for goals");
   ("--switch-okb", Arg.Unit (fun _ ->
     settings := { !settings with switch_to_okb = true}),
     "switch to standard oKB");
   ("--term", Arg.Set only_termination,
     " perform termination check");
   ("-T", Arg.Float (fun f -> timeout := Some f),
     "<t> timeout");
   ("--track", Arg.String (fun s -> track_file := Some s),
     "<track_file> keep track of equations in proof file");
   ("--trace-selection", Arg.Unit (fun _ ->
     Settings.do_proof := Some SelectionTrace),
     " output selection track");
   ("--tmp", Arg.Float (fun s -> Settings.tmp := s),
    "<n> various purposes");
   ("--xsig",  Arg.Unit (fun _ ->
     settings := { !settings with extended_signature = true}),
     "consider signature plus infinitely many constants (ordered completion)")
 ]

(*** FUNCTIONS ***************************************************************)
let map3 f (a,b,c) = (f a, f b, f c)

let print_trs ppf rules = fprintf ppf "%a@." Rules.print rules

let print_trs_eqs ppf (rules, eqs) =
  fprintf ppf "%a%!" Rules.print rules;
  fprintf ppf "%a%!" (Rules.print_with "=") eqs
;;

let print_es ppf eqs = fprintf ppf "%a@." (Rules.print_with "=") eqs

let trs_string rules =
 F.fprintf F.str_formatter "%a" print_trs rules;
 F.flush_str_formatter ()
;;

let trs_eqs_string re =
 F.fprintf F.str_formatter "%a" print_trs_eqs re;
 F.flush_str_formatter ()
;;

let call () =
  let rec add_arg i =
    if i < Array.length Sys.argv then Sys.argv.(i)^" "^(add_arg (i+1)) else "" 
  in add_arg 0
;;

let success_code = function UNSAT -> "Unsatisfiable" | SAT -> "Satisfiable"

let success_code_inf = function UNSAT -> "MAYBE" | SAT -> "YES"

let json_settings settings s =
 let s = "strategy", `String s in
 let n = "n", `Int !heuristic.n in
 let sa = "sizeage", `Int !heuristic.size_age_ratio in
 `Assoc [s; n; sa]
;;

let print_json (es, gs) f (a,p) settings =
  let res_str = match p with
    | Completion rr -> trs_string rr
    | GroundCompletion (rr,ee,_)
    | Disproof (rr,ee,_,_) -> (* TODO: show different normal forms? *)
      if ee <> [] then trs_eqs_string (rr, ee) else trs_string rr
    | Proof _ -> "..."
  in
  let f = `Float ((ceil (f *. 1000.)) /. 1000.) in
  let strat = !heuristic.strategy in
  let t = `Assoc [
    "result",`String (success_code a);
    "time", f;
    "trs", `String res_str;
    "statistics", Analytics.json ();
    "settings", json_settings settings (Strategy.to_string strat);
    "characteristics", Analytics.analyze es gs
  ] in
  F.printf "%s\n%!" (pretty_to_string t)
;;

let print_json_term yes f =
 let f = `Float ((ceil (f *. 1000.)) /. 1000.) in
 let t = `Assoc [
  "result",`String (if yes then "YES" else "MAYBE");
  "time", f;
  "config",`String (call())] in
 F.printf "%s\n%!" (pretty_to_string t)
;;

let print_res answer res =
  if !settings.infeasible then
    printf "%s\n%!" (success_code_inf answer)
  else (
    printf "%s SZS status " "%";
    let answer_str = success_code answer in
    match res with
    | Completion trs -> printf "Satisfiable\n\n%a@." print_trs trs;
    | GroundCompletion (rr,ee,order)
    | Disproof (rr,ee,order,_) -> (* TODO: show different normal forms? *)
      (printf "%s\n\n%a@." answer_str print_trs rr;
      if ee <> [] then printf "%a@." print_es ee;
      order#print ();
      Format.printf "\n")
    | Proof _ -> printf "%s\n%!" answer_str
  )
;;

let print_analysis es gs =
 F.printf "%s\n%!" (pretty_to_string (Analytics.analyze es gs))
;;         

let clean es0 =
  let reduce rr =
    if L.length rr < 200 then Listx.unique (Var.reduce rr) else rr
  in
  let es0n = [Lit.terms (Lit.normalize e) | e <- es0 ] in
  let clean rr ee =
    let nf = Rewriting.nf rr in
    let ee' = [ nf s, nf t | s,t <- ee; nf s <> nf t ] in
    let ee'' = Rules.subsumption_free ee' in
    let rr' = if L.length rr < 200 then Var.reduce_encomp rr else rr in
    let rr_pre =
      if not !settings.keep_orientation then []
      else Listset.diff [ r | r <- rr;L.mem (Var.normalize_rule r) es0n ] rr'
    in
    (rr' @ rr_pre, ee'')
  in function
    | Completion trs -> Completion (reduce trs)
    | GroundCompletion (rr,ee,o) ->
      let rr',ee' = clean rr ee in
      GroundCompletion (rr',ee',o)
    | Disproof (rr,ee,o,(rs,rt)) ->
      let rr',ee' = clean rr ee in
      Disproof (rr',ee',o,(rs,rt))
    | Proof p -> Proof p
;;

let cpf_proof_string ?(readable = false) (es, gs) =
  let result_string p =
      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^ 
      "<?xml-stylesheet type=\"text/xsl\" href=\"cpfHTML.xsl\"?>\n" ^
      ((if readable then Xml.to_string_fmt else Xml.to_string) p)
  in
  function
    Proof ((s,t),(rs, rt), sigma) when L.for_all Lit.is_equality es ->
      let goal = Literal.terms (L.hd gs) in
      let es = L.map Literal.terms es in
      let p = Cpf.goal_proof es goal ((s,t),(rs, rt), sigma) in
      result_string p
  | Completion rr -> (* FIXME only check ground completion new *)
      let es = L.map Literal.terms es in
      let p = Cpf.ordered_completion_proof es ([], rr, Order.default) in
      result_string p
  | GroundCompletion (rr,ee,o) -> (* no goal exists *)
      let es = L.map Literal.terms es in
      let p = Cpf.ordered_completion_proof es (ee, rr, o) in
      result_string p
  | Disproof (rr,ee,o,rst) -> (* goal with different normal forms exists *)
      let g = Literal.terms (L.hd gs) in
      let es = L.map Literal.terms es in
      let p = Cpf.goal_disproof es g (ee, rr, o) rst in
      result_string p
  | _ -> failwith "Main.show_proof: not yet supported for inequality axioms"
;;

let selection_trace (es, gs) = function
    Proof ((s, t),(rs, rt), sigma) when L.for_all Lit.is_equality es ->
      let goal = Literal.terms (L.hd gs) in
      let es = L.map Literal.terms es in
      SelectionTrace.for_goal_proof es goal ((s, t), (rs, rt), sigma)
  | Completion rr ->
      let es = L.map Literal.terms es in
      SelectionTrace.for_ground_completion es (rr, [])
  | GroundCompletion (rr, ee, o) ->
      let es = L.map Literal.terms es in
      SelectionTrace.for_ground_completion es (rr, ee)
  | Disproof (rr, ee, _, rst) ->
      SelectionTrace.for_goal_disproof (rr, ee) rst
  | _ -> failwith "Main.selection_trace: not yet supported"
;;

let show_proof filename input res = function
  | CPF -> Format.printf "%s\n%!" (cpf_proof_string input res)
  | TPTP -> Format.printf "%s\n%!" (Tptp.proof_string filename input res)
  | SelectionTrace -> selection_trace input res
  | _ -> Format.printf "some proof\n%!"
;;

let interactive_mode proof =
  let acs = !settings.ac_syms in
  let rewriter = match proof with
    | Completion rr ->
      Format.printf "Deciding equational theory.\n%!";
      let rew = new Rewriter.rewriter !heuristic rr acs Order.default in
      rew#init ();
      rew
    | GroundCompletion (rr,ee,o) ->
      Format.printf "Deciding ground theory over given signature.\n%!";
      let rew = new Rewriter.rewriter !heuristic rr acs o in
      rew#init ();
      rew#add ee;
      rew
    | _ -> failwith "No decision procedure, interactive mode not possible."
  in
  let decision_proc l =
    let s,t = Literal.terms l in
    let joined = fst (rewriter#nf s) = fst (rewriter#nf t) in
    (joined && Literal.is_equality l) || not (joined || Literal.is_equality l)
  in
  Format.printf "OK\n%!";
  let check_eq s =
    let l = Read.equation_or_inequality s in
    Format.printf "%s\n%!" (if decision_proc l then "YES" else "NO")
  in
  let rec check _ =
    try
      Format.printf "Enter equation or 'exit' to stop:\n%!";
      let s = read_line () in
      if s = "exit" then exit 0
      else (check_eq s; check ())
    with _ -> check ()
  in check ()
;;

let print_waldmeister es =
  let es = [Lit.terms e | e <- es ] in
  F.printf "NAME        Example\n%!";
  F.printf "MODE        PROOF\n%!";
  F.printf "SORTS       ANY\n%!";
  let fs = Rules.signature es in
  let str (f,a) =
    let n = Signature.get_fun_name f in
    n ^ ": " ^ (L.fold_left (^) "" (Listx.copy a "ANY ")) ^ "-> ANY\n"
  in
  F.printf "SIGNATURE   %s" (L.fold_left (fun s f -> s ^ (str f)) "" fs);
  F.printf "ORDERING    LPO %s\n%!"
    (L.fold_left (fun s (f,_) -> s ^ " > " ^(Signature.get_fun_name f))
     (Signature.get_fun_name (fst (L.hd fs))) (L.tl fs));
  let vs = Rules.variables es in
  let vs = match vs with
     [] -> ""
   | v0 :: vs' ->
     let v0s = Signature.get_var_name (L.hd vs) in
     L.fold_left (fun s v -> s ^ "," ^ Signature.get_var_name v) v0s (L.tl vs)
  in
  F.printf "VARIABLES   %s : ANY\n%!" vs;
  F.printf "EQUATIONS   %!";
  let print (l,r) = F.printf "            %a = %a\n" Term.print l Term.print r in
  L.iter print es;
  F.printf "CONCLUSION   %!\n"
;;

let run file ((es, gs) as input) =
  let timer = Timer.start () in
  let ans, proof =
    if gs = [] && !settings.unfailing && not !settings.complete_if_no_goal then
      (SAT, GroundCompletion ([], [Term.V 0, Term.V 1], Order.default))
    else if !settings.modulo_ac then
      Ckb_AC.complete (!settings, !heuristic) (fst input)
    else
      Ckb.ckb (!settings, !heuristic) input
  in
  Timer.stop timer;
  let secs = Timer.length ~res:Timer.Seconds timer in
  if !(Settings.interactive) then
    interactive_mode proof
  else if !settings.json then
    print_json (es,gs) secs (ans,clean es proof) settings
  else (
    match !(Settings.do_proof) with
    | Some fmt when not !Settings.benchmark ->
      if !settings.infeasible then print_res ans (clean es proof);
      show_proof file input proof fmt
    | None -> (
      print_res ans (clean es proof);
      if not !Settings.benchmark then (
        printf "%s %.2f %s@." "Search time:" secs "seconds";
        Analytics.print ()
      )
    )
    | _ -> ()
  )
;;

let () =
  do_ordered ();
  Arg.parse options 
   (fun x -> filenames := !filenames @ [x]) short_usage;
  strategy := !heuristic.strategy;
  if L.length !filenames <> 1 then
     (eprintf "%s%!" short_usage; exit 1)
  let f = L.hd !filenames in
  match Read.file f with
  | Unit (es,gs) -> (
    Settings.input_file := remove_extension (Filename.basename f);
    (match !track_file with | Some f -> track_proof f | _ -> ());
    (match !classify_file with | Some f -> set_classification f | _ -> ());
    if !(Settings.interactive) && gs <> [] then
      failwith "Input for interactive mode is not supposed to contain goals";
    if !settings.debug > 0 then
      printf "input problem: %s\n%!" f;
    if not !only_termination && not !analyze && not !only_gcr then
      try
        match fst (Timer.run_timed !timeout (run f) (es,gs)) with
        | None -> printf "%s SZS status Timeout\n%!" "%"
        | Some _ -> ()
      with e -> (printf "%s SZS status GaveUp\n%!" "%"; raise e)
    else if !analyze then
      print_analysis es gs
    else if !only_termination then (
      let timer = Timer.start () in
      let yes =
        Termination.check (S.get_termination !strategy) es !settings.json
      in
      Timer.stop timer;
      let secs = Timer.length ~res:Timer.Seconds timer in
      if !settings.json then print_json_term yes secs
      else (
        printf "@.%a@." print_trs [Literal.terms e | e <- es];
        let a = if yes then "YES" else "MAYBE" in
        printf "%s\n" a;
        printf "%s %.2f %s@." "time:" secs "seconds")
      )
      else (* !only_gcr *) (
        let timer = Timer.start () in
        let yes =
          Gcr.check !settings !heuristic (S.get_termination !strategy) es
        in
        Timer.stop timer;
        let secs = Timer.length ~res:Timer.Seconds timer in
        if !settings.json then print_json_term yes secs
        else (
          printf "@.%a@." print_trs [Literal.terms e | e <- es];
          let a = if yes then "YES" else "MAYBE" in
          printf "%s\n" a;
          printf "%s %.2f %s@." "time:" secs "seconds")
        )
    )
  | NonUnit (cls, gs) ->
    Format.printf "oh no, it's not unit!\n%!";
    settings := {!settings with instgen = true};
    Settings.do_proof := Some TraceForInstgen;
    match Instgen.start (!settings, !heuristic) (cls @ gs) with
    | SAT -> Format.printf "Satisfiable\n%!"
    | UNSAT -> Format.printf "Unsatisfiable\n%!"
;;
