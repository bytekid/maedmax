(*** MODULES *****************************************************************)
module S = Strategy
module F = Format
module Lit = Literal

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
   ("--cpf", Arg.Set Settings.do_proof,
    " output certifiable CPF proof");
   (*("-cpfd", Arg.Unit (fun _ -> Settings.do_proof := true;
                                Settings.do_proof_debug := true),
    " output CPF proof plus debug output");*)
   ("-D", Arg.Set settings.d,
    " print debugging output");
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
       else if s = "olpokbo" then settings.strategy := S.strategy_ordered
       else if s = "kbo" then settings.strategy := S.strategy_kbo
       else if s = "maxcomplpo" then settings.strategy := S.strategy_maxcomp_lpo
       else if s = "okbauto" then settings.strategy := S.strategy_ordered
       (*else if s = "mpol" then settings.strategy := S.strategy_mpol
       else if s = "maxcomp" then settings.strategy := S.strategy_maxcomp
       else if s = "ordered" then settings.strategy := S.strategy_ordered
       else if s = "temp" then settings.strategy := S.strategy_temp*)
       else failwith "unsupported option for -M"),
    "<mode> strategy (olpo, okbo, olpokbo)");
   (*("-checksub", Arg.Set settings.check_subsumption,
    " perform subsumption checks");*)
   ("-N", Arg.Int (fun n -> settings.n := n), 
    "<n> select <n> active equations from CPs of TRS");
   ("--term", Arg.Set only_termination,
    " perform termination check");
   ("-T", Arg.Set_float timeout,
    "<t> timeout");
   (*("-termproof", Arg.Set settings.output_tproof,
    " output termination proof");
   ("-TMP", Arg.Set Settings.tmp,
    " various purposes");*)
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

let success_code = function Ckb.Proof _ -> "UNSAT" | _ -> "SAT"

let print_json (es, gs) f res settings =
 let res_str = match res with
  | Ckb.Completion rr -> trs_string rr
  | Ckb.GroundCompletion (rr,ee,_) ->
    if ee <> [] then trs_eqs_string (rr, ee) else trs_string rr
  | Ckb.Proof _ -> "..."
 in
 let f = `Float ((ceil (f *. 1000.)) /. 1000.) in
 let t = `Assoc [
  "result",`String (success_code res);
  "time", f;
  "trs", `String res_str;
  "statistics", Statistics.json settings 
    (Strategy.to_string !(settings.strategy)) !k;
  "chracteristics", Statistics.analyze es gs
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

let print_res res =
  printf "# SZS status ";
  match res with
   | Ckb.Completion trs -> printf "Satisfiable\n\n%a@." print_trs trs;
   | Ckb.GroundCompletion (rr,ee,order) ->
    (printf "Satisfiable\n\n%a@." print_trs rr;
    if ee <> [] then printf "%a@." print_es ee;
    order#print ();
    Format.printf "\n")
   | Ckb.Proof _ -> printf "Unsatisfiable\n%!"
;;

let print_analysis es gs =
 F.printf "%s\n%!" (pretty_to_string (Statistics.analyze es gs))
;;         

let clean =
  let reduce rr = Listx.unique (Variant.reduce rr) in function
 | Ckb.Completion trs -> Ckb.Completion (reduce trs)
 | Ckb.GroundCompletion (rr,ee,o) ->
   let nf = Rewriting.nf rr in
   let ee' = [ nf s, nf t | s,t <- ee; nf s <> nf t ] in
   let ee'' = Rules.subsumption_free ee' in
   Ckb.GroundCompletion (Variant.reduce_encomp rr, ee'',o)
 | Ckb.Proof p -> Ckb.Proof p
;;

let show_proof (es,gs) = function
    Ckb.Proof ((s,t),(rs, rt), sigma) when List.for_all Lit.is_equality es ->
      let p = Trace.xml_goal_proof es (List.hd gs) ((s,t),(rs, rt), sigma) in
      F.printf "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
      F.printf "<?xml-stylesheet type=\"text/xsl\" href=\"cpfHTML.xsl\"?>\n";
      F.printf "%s\n" (Xml.to_string_fmt p)
  | _ -> failwith "Main.show_proof: not yet supported if no goal present"
;;

let () =
  do_ordered ();
  Arg.parse options 
   (fun x -> filenames := !filenames @ [x]) short_usage;
  strategy := !(settings.strategy);
  let json = !(settings.json) in
  match !filenames with
  | [f] -> 
      let (es,gs) as input = Read.read f in
      if not !only_termination && not !analyze then
       begin try
        let timer = Timer.start () in
	      let res = Ckb.ckb settings input in
        if json then (
         Timer.stop timer;
         let secs = Timer.length ~res:Timer.Seconds timer in
         print_json (es,gs) secs (clean res) settings
        ) else (
         if !(Settings.do_proof) then
           show_proof input res
         else (
           print_res (clean res);
	         Timer.stop timer;
           let secs = Timer.length ~res:Timer.Seconds timer in
           printf "%s %.2f %s@." "Search time:" secs "seconds";
           Statistics.print ())
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
        printf "@.%a@." print_trs [ e#terms | e <- es ];
        let a = if yes then "YES" else "MAYBE" in
        printf "%s\n" a;
        printf "%s %.2f %s@." "time:" secs "seconds")
       )
  | _ -> eprintf "%s%!" short_usage; exit 1

