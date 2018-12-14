(*** MODULES *****************************************************************)
module L = List
module Lit = Literal
module Logic = Settings.Logic
module Sig = Signature
module H = Hashtbl

module Clause = struct

type t = Lit.t list

let bot = Term.F (Signature.fun_called "bot", [])

let variables c = L.concat [ Lit.variables l | l <- c ]

let substitute sigma = L.map (Lit.substitute sigma)

let substitute_uniform t = L.map (Lit.substitute_uniform t)

let ground = substitute_uniform bot

let print ppf c =
  Format.fprintf ppf "@[%a@]" (Formatx.print_list Literal.print " | ") c
;;

let normalize c =
  let c' = [l, Lit.substitute_uniform bot l | l <- c] in
  let c' = L.sort (fun (_, g) (_, g') -> compare g g') c' in
  let oriented l = fst (Lit.terms l) < snd (Lit.terms l) in
  let c = [ if oriented lg then l else Lit.flip l | l, lg <- c'] in
  let ren = [ x, Term.V i | i, x <- Listx.ix (variables c) ] in
  substitute ren c
;;

let norm_subst sigma c = normalize (substitute sigma c)

let simplify c = [l | l <- c; not (Lit.is_inequality l && Lit.is_trivial l)]

end

(*** OPENS *******************************************************************)
open Settings

(*** GLOBALS *****************************************************************)
let settings = ref Settings.default
let heuristic = ref Settings.default_heuristic

(*** FUNCTIONS ***************************************************************)
let debug _ = true

let print_clauses ppf cs =
  Format.fprintf ppf "@[(%a)@]\n" (Formatx.print_list Clause.print ", ") cs
;;

let print_literals ppf ls =
  Format.fprintf ppf "@[%a@]" (Formatx.print_list Literal.print "\n ") ls
;;

let replace_with f h k v =
  (try H.replace h k (f v (H.find h k)) with Not_found -> H.add h k v);
  h
;;

let ground cls = [c, Clause.ground c | c <- cls]

(* map non-ground literal to variable *)
let lit_vars : (Rule.t, Logic.t) Hashtbl.t = Hashtbl.create 256

let lit_var rl = try H.find lit_vars rl with _ -> failwith "Instgen: lit_var"

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

let print_assignment eval =
  if debug () then (
    Format.printf "Assignment:\n%!";
    H.iter (fun (l, r) x -> 
      let eq = if eval x then "=" else "!=" in
      Format.printf " %a %s %a\n" Term.print l eq Term.print r)
    lit_vars
  )
;;

let check_sat ctx cls_vars cls =
  Logic.push ctx;
  L.iter Logic.require cls_vars;
  let res = 
  if not (Logic.check ctx) then (
    None
  ) else (
    let eval = Logic.eval (Logic.get_model ctx) in
    let eval_lit l = not (Lit.is_equality l) || eval (lit_var l.terms) in
    print_assignment eval;
    let lit b = if b then Lit.make_axiom else Lit.make_neg_axiom in
    let sel = H.fold (fun r x ss -> lit (eval x) r :: ss) lit_vars [] in
    let sat c =
      try Lit.terms (L.find eval_lit c)
      with _ -> Format.printf "%a\n%!" Clause.print c; failwith "Instgen: no literal selected in clause"
    in
    let add h c = replace_with (@) h (sat c) [c] in
    let smap = L.fold_left add (H.create 128) cls in
    Some (sel, smap)
  )
  in
  Logic.pop ctx;
  res
;;

let rec run i ctx cls =
  if i > 10 then failwith "too long";
  Format.printf "A. Instgen iteration %d:\n  %a\n%!" i print_clauses cls;
  let gcls = ground cls in
  Format.printf "B. grounded:\n  %a\n%!" print_clauses (L.map snd gcls);
  match check_sat ctx (to_logical ctx gcls) cls with
  | None -> UNSAT
  | Some (sel, smap) -> (
    Format.printf "C. check_sat:\n%a\n%!" print_literals sel;
    let flags = !settings, !heuristic in
    match Ckb.ckb_for_instgen ctx flags sel with
    | SAT, _ -> SAT
    | UNSAT, ls ->
      let cs = [ Clause.norm_subst sub c | l, sub <- ls; c <- H.find smap l] in
      Format.printf "new clauses:\n  %a\n%!" print_clauses cs;
      run (i + 1) ctx (cs @ cls)
  )
;;

let start (s, h) cls =
  settings := s;
  heuristic := h;
  let ctx = Logic.mk_context () in
  let ss = Listx.unique (L.map (fun (ts,_,_,_,_) -> ts) h.strategy) in
  L.iter (fun s -> Strategy.init s 0 ctx [ Lit.terms l | c <- cls; l <- c ]) ss;
  Format.printf "Start Instgen:\n %a\n%!" print_clauses cls;
  let cls = L.map Clause.normalize cls in
  Format.printf "Normalized:\n %a\n%!" print_clauses cls;
  let res = run 0 ctx cls in
  Logic.del_context ctx;
  res
;;
