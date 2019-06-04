(*** MODULES *****************************************************************)

module F = Format
module H = Hashtbl
module L = List
module Lx = Listx
module Lit = Literal
module Logic = Settings.Logic
module Sig = Signature
module T = Term
module DC = DismatchingConstraints

module Clause = struct

  type t = Lit.t list * Settings.dismatching_constraints

  let bot = T.F (Signature.fun_called "bot", []) (* U22A5 *)

  let variables (c, _) = L.concat [ Lit.variables l | l <- c ]

  let substitute sigma (ls, dc) =
    let ls' = L.map (Lit.substitute sigma) ls in
    let dc' = L.map (fun (ts, xs) -> ts, L.map (T.substitute sigma) xs) dc in
    ls', dc'
  ;;

  (* replace every variable with the same term t *)
  let substitute_uniform t (ls, dc) =
    let ls' = L.map (Lit.substitute_uniform t) ls in
    let dc' = L.map (fun (ts,xs) -> ts, L.map (T.substitute_uniform t) xs) dc in
    ls', dc'
  ;;

  let ground : (t -> t) = substitute_uniform bot

  let print ppf (c, dc) =
    F.fprintf ppf "(%a) %a" (Formatx.print_list Lit.print " | ") c
      DismatchingConstraints.print dc
  ;;

  let normalize c =
    let c' = [l, Lit.substitute_uniform bot l | l <- fst c] in
    let c' = L.sort (fun (_, g) (_, g') -> compare g g') c' in
    let oriented l = fst (Lit.terms l) < snd (Lit.terms l) in
    let ls = [ if oriented lg then l else Lit.flip l | l, lg <- c'] in
    let ren = [ x, T.V i | i, x <- Lx.ix (variables c) ] in
    substitute ren (ls, snd c)
  ;;

  let norm_subst sigma c = normalize (substitute sigma c)

  let simplify (ls, dc) =
    let ls' = [l | l <- ls; not (Lit.is_inequality l && Lit.is_trivial l)] in
    ls', DC.simplify dc
  ;;

  let add_dconstr (ls, dc) dc' = (ls, dc @ dc')

  let is_unsat (_, dc) = DC.is_unsat dc

end

module Clauses = struct
  type t = (Clause.t, bool) Hashtbl.t

  let empty () : t = H.create 128
  
  let is_empty ns = H.length ns = 0
  
  let size = H.length
  
  let mem = H.mem
  
  let rec add n ns = if not (H.mem ns n) then H.add ns n true; ns
  
  let rec remove n ns = H.remove ns n; ns
  
  let add_all ns ns' = H.fold (fun n _ h -> add n h) ns ns'
  
  let add_list l ns = L.fold_left (fun h n -> add n h) ns l
  
  let of_list l = add_list l (H.create (L.length l * 2))

  let to_list ns = (H.fold (fun n _ l -> n :: l) ns [])

  let map f cs = H.fold (fun c _ cs -> add (f c) cs) cs (empty ())

  let simplify = map Clause.simplify

  let print ppf ns =
    F.fprintf ppf " %a\n" (Formatx.print_list Clause.print "\n  ")
      (to_list ns)
end

(*** OPENS *******************************************************************)
open Settings

(*** GLOBALS *****************************************************************)
let settings = ref Settings.default
let heuristic = ref Settings.default_heuristic

(*** FUNCTIONS ***************************************************************)
let debug d = !settings.debug >= d

let print_clause_list ppf cs =
  F.fprintf ppf "@[(%a)@]\n" (Formatx.print_list Clause.print ", ") cs
;;

let print_literals ppf ls =
  F.fprintf ppf "@[%a@]" (Formatx.print_list Lit.print_with_dconstr "\n ") ls
;;

(* various shorthands *)
let is_negative l = not (Lit.is_equality l);;
let is_positive l = Lit.is_equality l;;
let (<=>) = Logic.(<=>);;
let (<&>) = Logic.(<&>);;
let (!!) = Logic.(!!);;

let ground cls = [c, Clause.ground c | c <- Clauses.to_list cls]

let replace_by f h k v =
  (try H.replace h k (f v (H.find h k)) with Not_found -> H.add h k v);
  h
;;

(* map non-ground term pair (s,t) to logical expression encoding [s = t] *)
let eq_exprs : (Rule.t, Logic.t) Hashtbl.t = Hashtbl.create 256

(* compute encoding [e] of literal l if e = l.terms; encodings get cached *)
let eq_expr ctx l lg =
  let equality_expr (s,t) =
    let rec term_expr = function
      | T.F (f, ts) ->
        Logic.apply ctx (Sig.get_fun_name f) (List.map term_expr ts)
      | _ -> failwith "Instgen.lit_expr: ground term expected" 
    in
    (term_expr s) <=> (term_expr t)
  in
  try Hashtbl.find eq_exprs l.terms
  with Not_found -> (
    let expr = equality_expr lg.terms in
    Hashtbl.add eq_exprs l.terms expr;
    expr)
;;

let to_smt ctx (cls_gcls : (Clause.t * Clause.t) list) =
  let disj c cg = [ eq_expr ctx l lg | l, lg <- Lx.zip (fst c) (fst cg) ] in 
  [ c, cg, disj c cg | c, cg <- cls_gcls ]
;;

let print_assignment eval cls_vars =
  if debug 2 then (
    let lxs = [ lg,x | _, (cg, _), xs <- cls_vars; lg, x <- Lx.zip cg xs] in
    F.printf "\nAssignment:\n%!";
    let print (lg, x) =
      let e = eval x in
      let eq = if e then "=" else "!=" in
      let l, r = Lit.terms lg in
      (* expressions not occurring in formula can evaluate to false in Yices
         even if according to the model they should become true (not in Z3) *)
      F.printf "  %a %s %a \n%!" T.print l eq T.print r
    in
    List.iter print lxs
  )
;;

let print_constraints ctx cls_vars =
  if debug 2 then (
    F.printf "Constraints:%!";
    let negate_if_ineq x l = if is_negative l then !! x else x in
    let lits ((ls,_), _, xs) = [negate_if_ineq x l | l, x <- Lx.zip ls xs] in
    let disj c = Logic.big_or ctx (lits c) in
    List.iter (fun c -> Logic.show (disj c); F.printf "\n%!") cls_vars)
;;

(* cls_vars are triples (c, cg, disj_cg) of a clause c, its grounded version cg,
   and an SMT expression list disj_cg representing the latter.
*)
let check_sat ctx cls_vars =
  Logic.push ctx;
  let negate_if_ineq x l = if is_negative l then !! x else x in
  let disj ((ls, _), _, xs) = [negate_if_ineq x l | l,x <- Lx.zip ls xs] in
  print_constraints ctx cls_vars;
  L.iter (fun c -> Logic.require (Logic.big_or ctx (disj c))) cls_vars;
  let res = 
    if not (Logic.check ctx) then None
    else (
      (*Logic.dump ctx;*)
      let eval = Logic.eval (Logic.get_model ctx) in
      print_assignment eval cls_vars;
      let rec true_lit = function
        | [] -> failwith "Instgen.check_sat: no true literal found in clause"
        | (l, lx) :: c ->
          if (is_positive l && eval lx) ||
             (is_negative l && not (eval lx)) then l
          else true_lit c
      in
      let add h ((ls, _) as c,_,cx) =
        replace_by (@) h (true_lit (Lx.zip ls cx)) [c]
      in
      (* smap maps selected literals (first true literal in clause for now) to
         list of clauses in which they were selected *)
      let smap = L.fold_left add (H.create 128) cls_vars in
      let constrain l cs =  Lit.add_dconstr l (L.concat [d | _, d <- cs]) in
      let sel = H.fold (fun l cs sel -> constrain l cs :: sel) smap [] in
      Some (sel, smap)
    )
  in
  Logic.pop ctx;
  res
;;

let restrict_dconstr cs_subs c =
  let subs = [sub | c', sub <- cs_subs; c = c'] in
  let xs = Listx.unique [T.V x | x <- Clause.variables c] in
  let constr_sub sub =
    let add (ls,ys) x =
      let t = T.substitute sub x in if t = x then (ls,ys) else (t :: ls,x :: ys)
    in
    L.fold_left add ([],[]) xs
  in 
  let dc_new = [ constr_sub sub | sub <- subs] in
  Clause.add_dconstr c [ dc | dc <- dc_new; dc <> ([],[])]
;;

let rec run i ctx (cls : Clauses.t) =
  (*if i > 10 then failwith "too long";*)
  if debug 1 then
    F.printf "A. Instgen iteration %d:\n  %a\n%!" i Clauses.print cls;
  let cls_gcls = ground cls in
  if debug 1 then
    F.printf "B. grounded:\n  %a\n%!" print_clause_list (L.map snd cls_gcls);
  match check_sat ctx (to_smt ctx cls_gcls) with
  | None -> UNSAT
  | Some (sel, smap) -> (
    (*if debug 1 then (
    F.printf "smap:\n";
    H.iter (fun l cs ->
      F.printf "  %a -> %a\n" Lit.print l print_clause_list cs) smap);*)
    if debug 1 then
      F.printf "C. check_sat:\n%a\n%!" print_literals sel;
    let flags = !settings, !heuristic in
    match Instgen_eq.check ctx flags sel with
    | SAT, _ -> F.printf "equation set SAT\n%!"; SAT
    | UNSAT, ls ->
      if debug 1 then (
        F.printf "equation set UNSAT\n%!";
        F.printf "new literals:\n%!";
        List.iter (fun (r , sigma) -> F.printf " %a (substituted %a)\n%!"
          Lit.print r Lit.print (Lit.substitute sigma r)) ls);
      let find l =
        try H.find smap l
        with _ -> (
          try H.find smap (Lit.flip l)
          with _ ->
          F.printf "%a not found\n%!" Lit.print l;
          failwith "smap fail")
      in
      let cs_subs = [c, sub | l, sub <- ls; c <- find l] in
      let cs = [ Clause.norm_subst sub c | c, sub <- cs_subs] in
      let cs_new = Lx.unique cs in
      F.printf "new clauses:\n  %a\n%!" print_clause_list cs_new;
      let cls' = Clauses.map (restrict_dconstr cs_subs) cls in
      let cls'' = Clauses.add_list cs_new cls' in
      run (i + 1) ctx (Clauses.simplify cls'')
  )
;;

let start (s, h) cls =
  settings := s;
  heuristic := h;
  let ctx = Logic.mk_context () in
  let ss = Lx.unique (L.map (fun (ts,_,_,_,_) -> ts) h.strategy) in
  L.iter (fun s -> Strategy.init s 0 ctx [ Lit.terms l | c <- cls; l <- c ]) ss;
  let cls_ds = [ c, [] | c <- cls ] in
  F.printf "Start Instgen:\n %a\n%!" print_clause_list cls_ds;
  let cls_ds = L.map Clause.normalize cls_ds in
  F.printf "Normalized:\n %a\n%!" print_clause_list cls_ds;
  let res = run 0 ctx (Clauses.of_list cls_ds) in
  Logic.del_context ctx;
  res
;;
