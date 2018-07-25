(*** MODULES *****************************************************************)
module S = Strategy
module F = Format
module Lit = Literal
module Var = Variant

(*** OPENS *******************************************************************)
open Format
open Settings
open Yojson.Basic

(*** GLOBALS *****************************************************************)
let short_usage = "maedmax v0.9\nUsage: maedmax <options> <file>\n"
let filenames = ref []

let settings = Settings.default

let k = ref (-1)
let use_ac = ref false
let analyze = ref false
let only_termination = ref false
let timeout = ref 60.0

let strategy = ref []

let do_ordered _ =
  settings.unfailing := true;
  (*settings.k := (fun _ -> 2);*)
  settings.strategy := S.strategy_ordered
;;

let do_concon _ =
  settings.unfailing := true;
  settings.max_oriented := 2;
  settings.full_CPs_with_axioms := true;
  settings.k := (fun _ -> 2);
  settings.strategy := S.strategy_ordered
;;

let do_unordered _ =
  settings.unfailing := false;
  settings.k := (fun _ -> 2);
  settings.strategy := S.strategy_auto
;;

let options = Arg.align 
  [(*("-ac", Arg.Unit (fun _ -> use_ac := true),
    " use AC-completion");*)
   ("--analyze", Arg.Unit (fun _ -> analyze := true),
    " print problem characteristics");
   ("--aql", Arg.Unit (fun _ -> (*settings.strategy := S.strategy_aql;
                                settings.reduce_trss := false;
                                settings.k := (fun _ -> 4)*) ()),
    " use heuristics for AQL examples");
   ("--noauto", Arg.Clear settings.auto,
    " use heuristic settings (automatic mode)");
   ("--concon", Arg.Unit do_concon,
    " satisfiability-preferring strategy");
   ("--cpf", Arg.Set Settings.do_proof,
    " output certifiable CPF proof");
   ("--cpfd", Arg.Unit (fun _ -> Settings.do_proof := true;
                                Settings.do_proof_debug := true),
    " output CPF proof plus debug output");
   ("-D", Arg.Int (fun d -> settings.d := d),
    " print debugging output");
   ("--interactive", Arg.Set Settings.interactive,
    " enter interactive mode once a complete system was found");
   ("--json", Arg.Set settings.json,
    " output result and stats in JSON format");
   ("-I", Arg.Int (fun n -> Settings.inst_depth := n),
    "<i> instantiation depth for ground confluence check");
   ("-K", Arg.Int (fun n -> settings.k := (fun _ -> n); k := n),
    "<k> compute k maximal terminating TRSs");
   ("--kb", Arg.Unit do_unordered,
    " Knuth-Bendix completion (unordered)");
   ("-M", Arg.String (fun s -> 
       (*if s = "cpred" then settings.strategy := S.strategy_cpred
       else if s = "comp" then settings.strategy := S.strategy_comp
       else if s = "dp" then settings.strategy := S.strategy_dp
       else if s = "dg" then settings.strategy := S.strategy_dg
       else if s = "dgk" then settings.strategy := S.strategy_dgk*)
       if s = "kbauto" then settings.strategy := S.strategy_auto
       (*else if s = "auto2" then settings.strategy := S.strategy_auto2
       else if s = "red" then settings.strategy := S.strategy_red
       else if s = "no" then settings.strategy := S.strategy_not_oriented*)
       else if s = "lpo" then settings.strategy := S.strategy_lpo
       else if s = "olpo" then settings.strategy := S.strategy_ordered_lpo
       else if s = "okbo" then settings.strategy := S.strategy_ordered_kbo
       else if s = "olpoorkbo" then settings.strategy := S.strategy_ordered_lpokbo
       else if s = "kbo" then settings.strategy := S.strategy_kbo
       else if s = "maxcomplpo" then settings.strategy := S.strategy_maxcomp_lpo
       else if s = "maxcompkbo" then settings.strategy := S.strategy_maxcomp_kbo
       else if s = "okbauto" then settings.strategy := S.strategy_ordered
       (*else if s = "mpol" then settings.strategy := S.strategy_mpol
       else if s = "maxcomp" then settings.strategy := S.strategy_maxcomp
       else if s = "ordered" then settings.strategy := S.strategy_ordered*)
       else if s = "temp" then settings.strategy := S.strategy_temp
       else failwith "unsupported option for -M"),
    "<mode> strategy (olpo, okbo, olpokbo)");
   ("--checksub", Arg.Int (fun n -> settings.check_subsumption := n),
    " perform subsumption checks (1,2)");
   ("--pcp", Arg.Int (fun n -> settings.pcp := n),
    " only consider prime critical pairs if set to 1 (but then no caching)");
   ("--keep-oriented", Arg.Set settings.keep_orientation,
    " preserve orientation of input axioms");
   ("-N", Arg.Int (fun n -> settings.n := n), 
    "<n> select <n> active equations from CPs of TRS");
    ("--max-oriented", Arg.Int (fun n -> settings.max_oriented := n), 
    "<n> every <n> iterations, orient as many equations as possible");
   ("--full-CPs-with-axioms", Arg.Set settings.full_CPs_with_axioms,
    " compute CPs with axioms in both directions");
    ("--generate-order", Arg.Unit (fun _ ->
      Settings.generate_order := true;
      (*settings.auto := false;*)
      settings.strategy := S.strategy_order_generation),
     " order generation mode");
   ("--reduceAC-CPs", Arg.Set settings.reduce_AC_equations_for_CPs,
    " do not use ACx equations for CPs");
   ("--sizeage", Arg.Int (fun n -> settings.size_age_ratio := n), 
    "<r> percentage of size (vs age) decisions");
   ("--size-bound", Arg.Int (fun n -> settings.size_bound_equations := n),
    "<b> upper bound for size of active equations");
   ("--size-bound-goals", Arg.Int (fun n -> settings.size_bound_goals := n),
    "<b> upper bound for size of active goals");
   ("--term", Arg.Set only_termination,
    " perform termination check");
   ("-T", Arg.Set_float timeout,
    "<t> timeout");
   (*("-termproof", Arg.Set settings.output_tproof,
    " output termination proof");*)
   (*("--tmp", Arg.Int (fun n -> settings.tmp := n),
    "<n> various purposes");*)
   ("--xsig", Arg.Set settings.extended_signature,
    " consider signature plus infinitely many constants (ordered completion)")
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

let success_code = function UNSAT -> "UNSAT" | SAT -> "SAT"

let json_settings settings s k =
 let s = "strategy", `String s in
 let k = "k", `String (if k  < 0 then "if i < 3 then 6 else 2" else string_of_int k) in
 let n = "n", `Int !(settings.n) in
 let sa = "sizeage", `Int !(settings.size_age_ratio) in
 `Assoc [s; k; n; sa]
;;

let print_json (es, gs) f (a,p) settings proof =
  let res_str = match p with
    | Completion rr -> trs_string rr
    | GroundCompletion (rr,ee,_)
    | Disproof (rr,ee,_,_) -> (* TODO: show different normal forms? *)
      if ee <> [] then trs_eqs_string (rr, ee) else trs_string rr
    | Proof _ -> "..."
  in
  let f = `Float ((ceil (f *. 1000.)) /. 1000.) in
  let strat = !(settings.strategy) in
  let t = `Assoc [
    "result",`String (success_code a);
    "time", f;
    "trs", `String res_str;
    "statistics", Analytics.json ();
    "settings", json_settings settings (Strategy.to_string strat) !k;
    "characteristics", Analytics.analyze es gs;
    "proof", `String (match proof with Some s -> s | _ -> "")
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
  printf "# SZS status ";
  let answer_str = success_code answer in
  match res with
   | Completion trs -> printf "SAT\n\n%a@." print_trs trs;
   | GroundCompletion (rr,ee,order)
   | Disproof (rr,ee,order,_) -> (* TODO: show different normal forms? *)
    (printf "%s\n\n%a@." answer_str print_trs rr;
    if ee <> [] then printf "%a@." print_es ee;
    order#print ();
    Format.printf "\n")
   | Proof _ -> printf "%s\n%!" answer_str
;;

let print_analysis es gs =
 F.printf "%s\n%!" (pretty_to_string (Analytics.analyze es gs))
;;         

let clean es0 =
  let reduce rr =
    if List.length rr < 200 then Listx.unique (Var.reduce rr) else rr
  in
  let es0n = [Lit.terms (Lit.normalize e) | e <- es0 ] in
  let clean rr ee =
    let nf = Rewriting.nf rr in
    let ee' = [ nf s, nf t | s,t <- ee; nf s <> nf t ] in
    let ee'' = Rules.subsumption_free ee' in
    let rr' = if List.length rr < 200 then Var.reduce_encomp rr else rr in
    let rr_pre =
      if not !(settings.keep_orientation) then []
      else Listset.diff [ r | r <- rr;List.mem (Var.normalize_rule r) es0n ] rr'
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

let proof_string ?(readable=true) (es,gs) =
  let result_string p =
      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^ 
      "<?xml-stylesheet type=\"text/xsl\" href=\"cpfHTML.xsl\"?>\n" ^
      ((if readable then Xml.to_string_fmt else Xml.to_string) p)
  in
  function
    Proof ((s,t),(rs, rt), sigma) when List.for_all Lit.is_equality es ->
      let goal = Literal.terms (List.hd gs) in
      let es = List.map Literal.terms es in
      let p = Trace.xml_goal_proof es goal ((s,t),(rs, rt), sigma) in
      result_string p
  | Completion _ ->
    failwith "Main.show_proof: not yet supported for Completion"
  | GroundCompletion (rr,ee,o) -> (* no goal exists *)
      let es = List.map Literal.terms es in
      let p = Trace.xml_ground_completion es (rr,ee,o) in
      result_string p
  | Disproof (rr,ee,o,rst) -> (* goal with different normal forms exists *)
      let g = Literal.terms (List.hd gs) in
      let es = List.map Literal.terms es in
      let p = Trace.xml_goal_disproof es g (rr,ee,o) rst in
      result_string p
  | _ -> failwith "Main.show_proof: not yet supported for inequality axioms"
;;

let show_proof (es,gs) res =
  let p = proof_string (es,gs) res in Format.printf "%s\n" p
  (*Literal.print_sizes ();
  Format.printf "max equation: %d\nmax goal: %d\n%!"
    !Trace.max_eq_size !Trace.max_goal_size *)
;;

let interactive_mode proof =
  let rewriter = match proof with
    | Completion rr ->
      Format.printf "Deciding equational theory.\n%!";
      let rew = new Rewriter.rewriter rr !(settings.ac_syms) Order.default in
      rew#init ();
      rew
    | GroundCompletion (rr,ee,o) ->
    Format.printf "Deciding ground theory over given signature.\n%!";
      let rew = new Rewriter.rewriter rr !(settings.ac_syms) o in
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
    n ^ ": " ^ (List.fold_left (^) "" (Listx.copy a "ANY ")) ^ "-> ANY\n"
  in
  F.printf "SIGNATURE   %s" (List.fold_left (fun s f -> s ^ (str f)) "" fs);
  F.printf "ORDERING    LPO %s\n%!"
    (List.fold_left (fun s (f,_) -> s ^ " > " ^(Signature.get_fun_name f))
     (Signature.get_fun_name (fst (List.hd fs))) (List.tl fs));
  let vs = Rules.variables es in
  let vs = match vs with
     [] -> ""
   | v0 :: vs' ->
     let v0s = Signature.get_var_name (List.hd vs) in
     List.fold_left (fun s v -> s ^ "," ^ Signature.get_var_name v) v0s (List.tl vs)
  in
  F.printf "VARIABLES   %s : ANY\n%!" vs;
  F.printf "EQUATIONS   %!";
  let print (l,r) = F.printf "            %a = %a\n" Term.print l Term.print r in
  List.iter print es;
  F.printf "CONCLUSION   %!\n"
;;

let () =
  do_ordered ();
  Arg.parse options 
   (fun x -> filenames := !filenames @ [x]) short_usage;
  strategy := !(settings.strategy);
  let json = !(settings.json) in
  match !filenames with
  | [f] -> 
      let (es,gs) as input = Read.file f in
      Settings.input_file := Filename.remove_extension (Filename.basename f);
      if !(Settings.interactive) && gs <> [] then
        failwith "Input for interactive mode is not supposed to contain goals";
      if !(settings.tmp) > 0 then
        print_waldmeister es
      else if not !only_termination && not !analyze then
       begin try
        let timer = Timer.start () in
        let answer, proof = Ckb.ckb settings input in
        if !(Settings.interactive) then
          interactive_mode proof
        else if json then (
         Timer.stop timer;
         let secs = Timer.length ~res:Timer.Seconds timer in
         let proofstr =
           if !(Settings.do_proof) then
             Some (proof_string ~readable:false input proof)
           else None
         in
         print_json (es,gs) secs (answer,clean es proof) settings proofstr
        ) else (
         if !(Settings.do_proof) then
           show_proof input proof
         else (
           print_res answer (clean es proof);
	         Timer.stop timer;
           let secs = Timer.length ~res:Timer.Seconds timer in
           printf "%s %.2f %s@." "Search time:" secs "seconds";
           Analytics.print ())
         )
       with e -> printf "# SZS status GaveUp\n%!"; raise e end
      else if !analyze then
       print_analysis es gs
      else (
       let timer = Timer.start () in
       let yes = Termination.check (S.get_termination !strategy) es json in
       Timer.stop timer;
       let secs = Timer.length ~res:Timer.Seconds timer in
       if json then print_json_term yes secs else (
        printf "@.%a@." print_trs [ Literal.terms e | e <- es ];
        let a = if yes then "YES" else "MAYBE" in
        printf "%s\n" a;
        printf "%s %.2f %s@." "time:" secs "seconds")
       )
  | _ -> eprintf "%s%!" short_usage; exit 1

