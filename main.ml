(*** MODULES *****************************************************************)
module S = Strategy;;

(*** OPENS *******************************************************************)
open Format
open Settings
open Yojson.Basic

(* command line option *)

let short_usage = "ckb v0.1\nUsage: ckb <options> <file>\n"
let filenames = ref []

let settings = Settings.default

let k = ref (-1)
let use_ac = ref false
let only_termination = ref false
let timeout = ref 60.0

let strategy = ref []
       
(* main *)
let options = Arg.align 
  [("-ac", Arg.Unit (fun _ -> use_ac := true),
    " use AC-completion");
   ("-d", Arg.Set settings.d,
    " print debugging output");
   ("-json", Arg.Set settings.json,
    " output result and stats in JSON format");
   ("-K", Arg.Int (fun n -> settings.k := (fun _ -> n); k := n),
    "<n> compute n maximal terminating TRSs");
   ("-M", Arg.String (fun s -> 
       (*if s = "maxcomp" then settings.max_constraint := Oriented
       else*) if s = "cpred" then settings.strategy := S.strategy_cpred
       else if s = "comp" then settings.strategy := S.strategy_comp
       else if s = "dp" then settings.strategy := S.strategy_dp
       else if s = "dg" then settings.strategy := S.strategy_dg
       else if s = "dgk" then settings.strategy := S.strategy_dgk
       else if s = "auto" then settings.strategy := S.strategy_auto
       else if s = "auto2" then settings.strategy := S.strategy_auto2
       else if s = "red" then settings.strategy := S.strategy_red
       else if s = "no" then settings.strategy := S.strategy_not_oriented
       else if s = "lpo" then settings.strategy := S.strategy_lpo
       else if s = "olpo" then settings.strategy := S.strategy_ordered_lpo
       else if s = "okbo" then settings.strategy := S.strategy_ordered_kbo
       else if s = "kbo" then settings.strategy := S.strategy_kbo
       else if s = "mpol" then settings.strategy := S.strategy_mpol
       else if s = "maxcomp" then settings.strategy := S.strategy_maxcomp
       else if s = "maxcomplpo" then settings.strategy := S.strategy_maxcomp_lpo
       else if s = "ordered" then settings.strategy := S.strategy_ordered
       else if s = "temp" then settings.strategy := S.strategy_temp
       else failwith "unsupported option for -M"),
    " strategy (auto, lpo, kbo, mpol, dp, dg, dgk, maxcomp, red, cpred, or comp)");
   ("-CS", Arg.Set settings.check_subsumption,
    " perform subsumption checks");
   ("-N", Arg.Int (fun n -> settings.n := n), 
    " number of selected equations");
   ("-o", Arg.Unit (fun _ -> settings.unfailing := true;
                             settings.k := (fun _ -> 2);
                             settings.strategy := S.strategy_ordered),
    " ordered completion");
   ("-term", Arg.Set only_termination,
    " perform termination check");
   ("-time", Arg.Set_float timeout,
    " set timeout");
   ("-tproof", Arg.Set settings.output_tproof,
    " output termination proof");
   ("-TMP", Arg.Set_int settings.tmp,
    " various purposes")
 ]

let print_trs ppf rules = 
  fprintf ppf "(VAR %s)@.(RULES@.%a@.)@."
    (String.concat " " (List.map Signature.get_var_name (Rules.variables rules)))
    Rules.print rules

let print_trs_eqs ppf (rules, eqs) =
  fprintf ppf "(VAR %s)@.(RULES@.%a@.)(EQUATIONS@.%a@.)@."
    (String.concat " " (List.map Signature.get_var_name (Rules.variables rules)))
    Rules.print rules (Rules.print_with "=") eqs

let print_es ppf eqs = fprintf ppf "(EQUATIONS@.%a@.)@." (Rules.print_with "=") eqs

let trs_string rules =
 Format.fprintf Format.str_formatter "%a" print_trs rules;
 Format.flush_str_formatter ()
;;

let trs_eqs_string re =
 Format.fprintf Format.str_formatter "%a" print_trs_eqs re;
 Format.flush_str_formatter ()
;;

let call () =
 let rec add_arg i =
  if i < Array.length Sys.argv then Sys.argv.(i)^" "^(add_arg (i+1)) else "" 
 in add_arg 0
;;

let print_json f res settings =
 let s = Strategy.to_string !strategy in
 let res_str = match res with
  | Ckb.Completion rr -> trs_string rr
  | Ckb.GroundCompletion (rr,ee) ->
    if ee <> [] then trs_eqs_string (rr, ee) else trs_string rr
  | Ckb.Proof -> "..."
 in
 let f = `Float ((ceil (f *. 1000.)) /. 1000.) in
 let t = `Assoc [
  "result",`String "YES";
  "time", f;
  (*"config",`String (call());*)
  "trs", `String res_str;
  "ac symbols", `Int (List.length !(settings.ac_syms));
  "statistics", Statistics.json s !k !(settings.n)
 ] in
 Format.printf "%s\n%!" (pretty_to_string t)
;;

let print_json_term yes f =
 let f = `Float ((ceil (f *. 1000.)) /. 1000.) in
 let t = `Assoc [
  "result",`String (if yes then "YES" else "MAYBE");
  "time", f;
  "config",`String (call())] in
 Format.printf "%s\n%!" (pretty_to_string t)
;;

let print_res res =
  printf "YES@.";
  match res with
   | Ckb.Completion trs -> printf "%a@." print_trs trs;
   | Ckb.GroundCompletion (rr,ee) ->
    (printf "%a@." print_trs rr;
    if ee <> [] then printf "ES:@.%a@." print_es ee)
   | Ckb.Proof -> printf "(proof)\n"
;;
         

let clean =
  let reduce rr = Listx.unique (Variant.reduce rr) in function
 | Ckb.Completion trs -> Ckb.Completion (reduce trs)
 | Ckb.GroundCompletion (rr,ee) -> Ckb.GroundCompletion (reduce rr, reduce ee)
 | Ckb.Proof -> Ckb.Proof
;;

let () =
  Arg.parse options 
   (fun x -> filenames := !filenames @ [x]) short_usage;
  strategy := !(settings.strategy);
  let json = !(settings.json) in
  match !filenames with
  | [f] -> 
      let rs, goals = Read.read f in
      let es,gs = Rules.rpl_spcl_char rs, Rules.rpl_spcl_char goals in
      if not !only_termination then
       begin try
        let timer = Timer.start () in
	      let res =
          (*if !use_ac then Ac_ckb.ckb th else*) Ckb.ckb settings es gs in
        if json then (
         Timer.stop timer;
         let secs = Timer.length ~res:Timer.Seconds timer in
         print_json secs (clean res) settings
        ) else (
         print_res (clean res);
	       Timer.stop timer;
         let secs = Timer.length ~res:Timer.Seconds timer in
         printf "%s %.2f %s@." "Search time:" secs "seconds";
         Statistics.print ()
         )
       with e -> printf "MAYBE@."; raise e end
      else (
       let timer = Timer.start () in
       let yes = Termination.check (S.get_termination !strategy) es json in
       Timer.stop timer;
       let secs = Timer.length ~res:Timer.Seconds timer in
       if json then print_json_term yes secs else (
        printf "@.%a@." print_trs es;
        let a = if yes then "YES" else "MAYBE" in
        printf "%s\n" a;
        printf "%s %.2f %s@." "time:" secs "seconds")
       )
  | _ -> eprintf "%s%!" short_usage; exit 1

