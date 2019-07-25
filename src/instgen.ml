(*** MODULES *****************************************************************)
module L = List
module Lit = Literal
module Logic = Settings.Logic
module Sig = Signature
module H = Hashtbl
module Sub = Term.Sub

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
    substitute (List.fold_left (fun s (x,t) -> Sub.add x t s) Sub.empty ren) c
  ;;

  let norm_subst sigma c = normalize (substitute sigma c)

  let simplify c = [l | l <- c; not (Lit.is_inequality l && Lit.is_trivial l)]

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

  let print ppf ns =
    Format.fprintf ppf "@[(%a)@]\n" (Formatx.print_list Clause.print ", ")
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
  Format.fprintf ppf "@[(%a)@]\n" (Formatx.print_list Clause.print ", ") cs
;;

let print_literals ppf ls =
  Format.fprintf ppf "@[%a@]" (Formatx.print_list Literal.print "\n ") ls
;;

(* various shorthands *)
let is_negative l = not (Lit.is_equality l);;
let is_positive l = Lit.is_equality l;;
let (<&>) = Logic.(<&>);;
let (<=>) = Logic.(<=>);;
let (!!) = Logic.(!!);;

let ground cls = [c, Clause.ground c | c <- Clauses.to_list cls]

let replace_with f h k v =
  (try H.replace h k (f v (H.find h k)) with Not_found -> H.add h k v);
  h
;;

(* map non-ground term pair (s,t) to logical expression encoding [s = t] *)
let eq_exprs : (Rule.t, Logic.t) Hashtbl.t = Hashtbl.create 256

(* compute encoding [e] of literal l if e = l.terms; encodings get cached *)
let eq_expr ctx l lg =
  let equality_expr (s,t) =
    let rec term_expr = function
      | Term.F (f, ts) ->
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

let to_logical ctx cls =
  let disj c cg = [ eq_expr ctx l lg | l,lg <- Listx.zip c cg ] in 
  [ c, cg, disj c cg | c, cg <- cls ]
;;

let print_assignment eval cls_vars =
  if debug 2 then (
    let lxs = [ lg,x | _, cg, xs <- cls_vars; lg, x <- Listx.zip cg xs] in
    Format.printf "\nAssignment:\n%!";
    let print (lg, x) =
      let e = eval x in
      let eq = if e then "=" else "!=" in
      let l, r = Lit.terms lg in
      (* expressions not occurring in formula can evaluate to false in Yices
         even if according to the model they should become true (not in Z3) *)
      Format.printf "  %a %s %a \n%!" Term.print l eq Term.print r
    in
    List.iter print lxs
  )
;;

let print_constraints ctx cls_vars =
  if debug 2 then (
    Format.printf "Constraints:%!";
    let negate_if_ineq x l = if is_negative l then !! x else x in
    let lits (ls, _, xs) = [negate_if_ineq x l | l, x <- Listx.zip ls xs] in
    let disj c = Logic.big_or ctx (lits c) in
    List.iter (fun c -> Logic.show (disj c); Format.printf "\n%!") cls_vars)
;;

(* cls_vars are triples (c, cg, disj_cg) of a clause c, its grounded version cg,
   and a logical expression disj_cg representing the latter.
*)
let check_sat ctx cls_vars =
  Logic.push ctx;
  let negate_if_ineq x l = if is_negative l then !! x else x in
  let disj (ls, _, xs) = [negate_if_ineq x l | l,x <- Listx.zip ls xs] in
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
      let add h (c,_,cx) = replace_with (@) h (true_lit (Listx.zip c cx)) [c] in
      (* smap maps selected literals (first true literal in clause for now) to
         list of clauses in which they were selected *)
      let smap = L.fold_left add (H.create 128) cls_vars in
      let sel = H.fold (fun l _ sel -> l :: sel) smap [] in
      Some (sel, smap)
    )
  in
  Logic.pop ctx;
  res
;;

let rec run i ctx cls =
  (*if i > 10 then failwith "too long";*)
  if debug 1 then
    Format.printf "A. Instgen iteration %d:\n  %a\n%!" i Clauses.print cls;
  let gcls = ground cls in
  if debug 1 then
    Format.printf "B. grounded:\n  %a\n%!" print_clause_list (L.map snd gcls);
  match check_sat ctx (to_logical ctx gcls) with
  | None -> UNSAT
  | Some (sel, smap) -> (
    if debug 1 then (
    Format.printf "smap:\n";
    H.iter (fun l cs ->
      Format.printf "  %a -> %a\n" Literal.print l print_clause_list cs) smap);
    if debug 1 then
      Format.printf "C. check_sat:\n%a\n%!" print_literals sel;
    let flags = !settings, !heuristic in
    match Instgen_eq.check ctx flags sel with
    | SAT, _ -> Format.printf "equation set SAT\n%!"; SAT
    | UNSAT, ls ->
      if debug 1 then (
        Format.printf "equation set UNSAT\n%!";
        Format.printf "new literals:\n%!";
        List.iter (fun (r , sigma) -> Format.printf " %a (substituted %a)\n%!"
          Lit.print r Lit.print (Lit.substitute sigma r)) ls);
      let find l =
        try H.find smap l
        with _ -> Format.printf "%a not found\n%!" Literal.print l;
        failwith "smap fail"
      in
      let cs = [ Clause.norm_subst sub c | l, sub <- ls; c <- find l] in
      let cs = Listx.unique cs in
      Format.printf "new clauses:\n  %a\n%!" print_clause_list cs;
      run (i + 1) ctx (Clauses.add_list cs cls)
  )
;;

let start (s, h) cls =
  settings := s;
  heuristic := h;
  let ctx = Logic.mk_context () in
  let ss = Listx.unique (L.map (fun (ts,_,_,_,_) -> ts) h.strategy) in
  L.iter (fun s -> Strategy.init s 0 ctx [ Lit.terms l | c <- cls; l <- c ]) ss;
  Format.printf "Start Instgen:\n %a\n%!" print_clause_list cls;
  let cls = L.map Clause.normalize cls in
  Format.printf "Normalized:\n %a\n%!" print_clause_list cls;
  let res = run 0 ctx (Clauses.of_list cls) in
  Logic.del_context ctx;
  res
;;
