(*** MODULES *****************************************************************)
module Lit = Literal
module Logic = Settings.Logic
module Sig = Signature

module Clause = struct

type t = Lit.t list

let variables c = List.concat [ Lit.variables l | l <- c ]

let substitute sigma = List.map (Lit.substitute sigma)

let print ppf c =
  Format.fprintf ppf "@[%a@]" (Formatx.print_list Literal.print " | ") c
;;

end

(*** OPENS *******************************************************************)
open Settings

(*** GLOBALS *****************************************************************)
let settings = ref Settings.default
let heuristic = ref Settings.default_heuristic

(*** FUNCTIONS ***************************************************************)
let print_clauses ppf cs =
  Format.fprintf ppf "@[%a@]" (Formatx.print_list Clause.print " | ") cs
;;

let print_literals ppf ls =
  Format.fprintf ppf "@[%a@]" (Formatx.print_list Literal.print "\n ") ls
;;

let ground cls =
  let vars = List.fold_left (fun vs c -> Clause.variables c @ vs) [] cls in
  let bot = Signature.fun_called "bot" in
  let sub_bot = [ v, Term.F (bot, []) | v <- Listx.unique vars ] in
  [ c, Clause.substitute sub_bot c | c <- cls ]
;;

let lit_vars : (Rule.t, Logic.t) Hashtbl.t = Hashtbl.create 256

let rule_var ctx l lg = 
  let x_eq = Cache.rule_var ctx lg.terms in
  if not (Hashtbl.mem lit_vars l.terms) then
    Hashtbl.add lit_vars l.terms x_eq;
  x_eq
;;

let to_logical ctx cls =
  let negate_unless b v = if b then v else Logic.(!!) v in
  let lit_var (l, lg) = negate_unless (Lit.is_equality l) (rule_var ctx l lg) in
  let disj c cg = Logic.big_or ctx [ lit_var l | l <- Listx.zip c cg ] in 
  [ disj c cg | c, cg <- cls ]
;;

let check_sat ctx cls =
  Logic.push ctx;
  List.iter Logic.require cls;
  if not (Logic.check ctx) then (
    Logic.pop ctx;
    None
  ) else (
    let m = Logic.get_model ctx in
    let literal b = if b then Lit.make_axiom else Lit.make_neg_goal in
    let add_eq rl x eqs = literal (Logic.eval m x) rl :: eqs in
    let eqs = Hashtbl.fold add_eq lit_vars [] in
    Logic.pop ctx;
    Some eqs
  )
;;

let rec run ctx cls =
  Format.printf "starting Instgen iteration:\n  %a\n%!" print_clauses cls;
  let gcls = ground cls in
  Format.printf "grounded:\n  %a\n%!" print_clauses (List.map snd gcls);
  match check_sat ctx (to_logical ctx gcls) with
  | None -> UNSAT
  | Some eqs -> (
    Format.printf "check_sat:\n%a\n%!" print_literals eqs;
    let pos, neg = List.partition Lit.is_equality eqs in
    let flags = !settings, !heuristic in
    let res, _ = Ckb.ckb_with_context (*ctx*) flags (pos, neg) in
    if res = SAT then
      SAT
    else
      let c = List.map Lit.negate pos @ neg in
      run ctx (c :: cls)
  )
;;

let start (s, h) cls =
  settings := s;
  heuristic := h;
  let ctx = Logic.mk_context () in
  let res = run ctx cls in
  Logic.del_context ctx;
  res
;;
