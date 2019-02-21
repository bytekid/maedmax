open Format
open Formatx
open Term

type t = Rule.t list

let print ppf rs =
  fprintf ppf "@[%a@]" (print_list Rule.print "\n ") rs

let print_with sep ppf rules =
  fprintf ppf "@[%a@]" (print_list (Rule.print_with sep)  "\n ") rules

let variables rules =
  Listx.unique [ x | rule <- rules; x <- Rule.variables rule ]

let functions rules =
  Listx.unique [ x | rule <- rules; x <- Rule.functions rule ]

let signature rules =
  Listx.unique [ x | rule <- rules; x <- Rule.signature rule ]

let defined_symbols rules =
  Listx.unique [ Term.root l | l, _ <- rules ]

let is_non_duplicating rules = List.for_all Rule.is_non_duplicating rules

let variable_condition rules =
  List.for_all Rule.variable_condition rules

let is_constructor_system rules =
  let ds = defined_symbols rules in
  let p = function
    | Term.V _, _ -> true
    | Term.F (_, ts), _ -> 
        List.for_all (fun t -> Listset.inter (Term.functions t) ds = []) ts in
  List.for_all p rules

let linear rules = List.for_all Rule.linear rules

let left_linear rules = List.for_all Rule.left_linear rules

let right_linear rules = List.for_all Rule.right_linear rules

let rec remove rls = function
 | [] -> rls
 | st :: stt ->
     remove (Rule.remove rls st) stt

let flatten ac ls = 
 [ Term.flatten ac s, Term.flatten ac t | s,t <- ls ]

let rules_over es =
 let rev es1 = [ t,s | s,t <- es1 ] in
 [ rule | rule <- es @ rev es; Rule.is_rule rule ]



let rpl_spcl_char rules =
 let rec rpl_trm t = t (*function
  | V x -> V x
  | F (f,fs) -> (
     match f with
     | "*" -> F ("times", [ rpl_trm fi | fi <- fs])
     | "+" -> F ("plus", [ rpl_trm fi | fi <- fs])
     | "@" -> F ("app", [ rpl_trm fi | fi <- fs])
     | "." -> F ("cons", [ rpl_trm fi | fi <- fs])
     | "-" -> F ("minus", [ rpl_trm fi | fi <- fs])
     | "div" ->  F ("divi", [ rpl_trm fi | fi <- fs])
     | "/" -> F ("slash", [ rpl_trm fi | fi <- fs])
     | "false" ->  F ("false_", [ rpl_trm fi | fi <- fs])
     | "true" ->  F ("true_", [ rpl_trm fi | fi <- fs])
     | "or" ->  F ("or_", [ rpl_trm fi | fi <- fs])
     | "and" ->  F ("and_", [ rpl_trm fi | fi <- fs])
     | "not" -> F("not_", [ rpl_trm fi | fi <- fs])
     | _ -> F (f, [ rpl_trm fi | fi <- fs])
 )*)
 in
 [ rpl_trm s, rpl_trm t | s,t <- rules ]

let is_srs rs = List.for_all (fun (_,a) -> a = 1) (signature rs)

let is_ground = List.for_all Rule.is_ground

let to_xml rs = Xml.Element("rules", [], List.map Rule.to_xml rs)

let subsumption_free ee =
  let pinst = Rule.is_proper_instance in
  (* n ist proper instance of n' *)
  let psub n n' = pinst n n' || pinst (Rule.flip n) n' in
  let ee' = List.filter (fun e -> not (List.exists (psub e) ee)) ee in
  let var rs r = if List.exists (Rule.variant r) rs then rs else r::rs in
  List.fold_left var [] ee'
;;

let flip rr = [ Rule.flip r | r <- rr ]
