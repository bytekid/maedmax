(*** OPENS *******************************************************************)
open Term

(*** MODULES *****************************************************************)
module Sig = Signature
module Ac = Theory.Ac

(*** TYPES *******************************************************************)
type sys = {
  trs: Rules.t;
  es: Rules.t;
  acsyms: Sig.sym list;
  order: Settings.t_term
}

type problem = {
  s: Term.t;
  t: Term.t;
  var_order: Term.t list;
  inst: int;
  id: string
}

type answer = True | False | Maybe of Yicesx.t

exception No_var_order

(*** GLOBALS *****************************************************************)
let joinable_cache : (Rules.t * Rules.t * Rule.t) list ref = ref [];;

let debug : bool ref = ref false

(*** FUNCTIONS ***************************************************************)
let (<&>) = Yicesx.(<&>)
let (<|>) = Yicesx.(<|>)

(* we assume the terms to be given descending: a condition s,t means s > t *)
let rec order_to_conditions = function
    [] -> []
  | x :: ys -> [ x,y | y <- ys] @ (order_to_conditions ys)
;;

let extend_var_orders vo (s,t) =
  (* variables not yet considered *)
  let zs = List.concat [ Term.variables x | x <- vo; Term.is_variable x ] in
  let xs = Listset.diff (Rule.variables (s, t)) zs in
  let inter os x = List.concat [ Listx.interleave (V x) o | o <- os ] in
  let vos = List.fold_left inter [vo] xs in
  let ok o =
    not (List.exists (fun (s,t) -> is_subterm s t) (order_to_conditions o))
  in
  [ o, (s,t) | o <- vos; ok o]
;;

let get_model c =
  let ctx = Yicesx.ctx c in
  Yicesx.push ctx;
  Yicesx.require c;
  let a = if Yicesx.check ctx then Some (Yicesx.get_model ctx) else None in
  Yicesx.pop ctx;
  a
;;

let check c = get_model c <> None 


let check_ordering_constraints trs c =
  match get_model (Yicesx.big_and1 (c :: [ Cache.find_rule r | r <- trs ])) with
  Some m -> true
  | None -> false
;;


let mk_sys trs es acsyms o = {
  trs = trs;
  es = es;
  acsyms = acsyms;
  order = o
}

let mk_problem st i = {
  s = fst st;
  t = snd st;
  var_order = [];
  inst = i;
  id = ""
}

let contradictory_constraints sys ctx p =
  let cs = order_to_conditions (p.var_order) in
  let cs_rem st = Listx.remove st cs in
  let contradict (s,t) = Strategy.cond_gt sys.order 1 ctx (cs_rem (s,t)) t s in
  check (Yicesx.big_or ctx [ contradict c | c <- cs ])
;;

let (<||>) a b = match a,b with
    True, _
  | _, True -> True
  | False, _ -> b 
  | _, False -> a 
  | Maybe c, Maybe c' -> Maybe (c <|> c')
;;

let (<&&>) a b = match a,b with
    False, _
  | _, False -> False
  | True, _ -> b 
  | _, True -> a 
  | Maybe c, Maybe c' -> Maybe (c <&> c')
;;

let yices_answer ctx = function
    False -> Yicesx.mk_false ctx
  | True -> Yicesx.mk_true ctx
  | Maybe c -> c
;;

let show = function
    True -> Format.printf "True"
  | False -> Format.printf "False"
  | Maybe c -> Format.printf "Maybe: "; Yicesx.show c 
;;

let print_order = Listx.print Term.print " > "

(* underapproximation of LPO and KBO assuming cs as conditional ordering
   constraints plus subterm property and lexicographic left-to-right comparison
   of arguments below same function symbol.
   If gt_simp cs (s,t) returns true then s > t holds. *)
let gt_simp cs (s,t) =
  let rec gt (s,t) = 
    if List.mem (s,t) cs then true
    else match (s,t) with
      | F (f, s0 :: ss), F (g, t0 :: ts) ->
        if f = g then
          gt (s0,t0) && (List.for_all (fun ti -> gt (s,ti)) ts)
        else
          List.exists (fun si -> si = t || gt (si,t)) (s0 :: ss)
      | F (f, ss), _ ->
        List.exists (fun si -> si = t || gt (si,t)) ss
      | _ -> false
  in gt (s,t) || List.exists (fun (s',u) -> s' = s && gt (u,t)) cs
;;

let no_order_check conds x y =
  let is_var = Term.is_variable in
  (* without fun terms in conds, LPO/KBO.cond_gt cannot do more than gt_simp *)
  List.for_all (fun (s,t) -> is_var s && is_var t) conds ||
  gt_simp conds (y,x) ||
  Term.is_subterm x y ||
  is_var x && is_var y
;;

let ordered_ac_step sys ctx conds (l,r) (u,c0) =
  try
    let sub = Subst.pattern_match l u in
    (* condition for these particular rules are instances of x and y *)
    let x', y' = substitute sub Ac.x, substitute sub Ac.y in
    if gt_simp conds (x', y') then substitute sub r, True
    else if no_order_check conds x' y' then u, True (* false/no step *)
    else ( 
    (*if !debug then Format.printf "   SAT check %a %!" Rule.print (x', y');*)
    let c = Strategy.cond_gt sys.order 1 ctx conds x' y' in
    if check_ordering_constraints sys.trs (yices_answer ctx c0 <&> c) then (
      (*if !debug then Format.printf "yes \n%!";*)
      substitute sub r, c0 <&&> Maybe c)
    else (
      (*if !debug then Format.printf "no \n%!";*) u, c0 (* no step *)
    ))
  with Subst.Not_matched -> u, c0
;;

let ac_nf ctx sys conds f u =
  let rec ac_nf c u = function
  | [] -> u, c
  | p :: ps ->
    let u0 = subterm_at p u in
    let u1 = Rewriting.nf sys.trs u0 in
    (*if u1 <> u0 then Format.printf "  R step from %a to %a \n%!" Term.print u0 Term.print u1;*)
    let u2, c2 = ordered_ac_step sys ctx conds (Ac.commutativity f) (u1,c) in
    (*if u1 <> u2 then Format.printf "  commutativity step from %a to %a \n%!" Term.print u1 Term.print u2;*)
    let u3, c3 = ordered_ac_step sys ctx conds (Ac.cassociativity f) (u2,c <&&> c2) in
    (*if u3 <> u2 then Format.printf "  cassociativity step from %a to %a \n%!" Term.print u2 Term.print u3;*)
    if u0 = u3 then ac_nf c u ps
    else let u' = replace u u3 p in
    ac_nf (c <&&> c2 <&&> c3) u' (positions u')
  in ac_nf True u (positions u)
;;

(* reducts wrt ordered rewriting with special MN90 AC rules *)
let ac_reducts ctx sys conds f (u,c) =
  let u = Rewriting.nf sys.trs u in
  Format.printf "new term %a\n" Term.print u;
  let rec reducts acc = function
    | [] -> acc
    | p :: ps ->
      let u0 = subterm_at p u in
      let u1, c1 = ordered_ac_step sys ctx conds (Ac.commutativity f) (u0,c) in
      let u2, c2 = ordered_ac_step sys ctx conds (Ac.cassociativity f) (u0,c) in
      let us1 = if u0=u1 then [] else [ replace u u1 p,c1 ] in
      let us2 = if u0=u2 then [] else [ replace u u2 p,c2 ] in
      reducts (us1@us2@acc) ps
  in reducts [] (positions u) (*@ [ r,c | r <- Rewriting.reducts sys.trs u ]*)
;;

let ac_join ctx sys conds f s t =
  let s_nf, cs = ac_nf ctx sys conds f s in 
  let t_nf, ct = ac_nf ctx sys conds f t in
  if !debug then 
    Format.printf "AC normalization: %a = %a get %a = %a\n%!"
      Term.print s Term.print t Term.print s_nf Term.print t_nf;
  if s_nf=t_nf || Theory.Ac.equivalent [f] (s_nf,t_nf) then cs <&&>ct else False
;;

let order_extensible ord (s,t) =
  let zs = List.concat [ variables x | x <- ord; is_variable x ] in
  let xs = Listset.diff (Rule.variables (s, t)) zs in
  xs <> []
;;

let rec joinable ctx sys p =
  if r_joinable ctx sys p || (e_instance ctx sys p) then True
  else ac_joinable ctx sys p
  (*let j0 = joinable_args ctx sys p in
  if j0 = True then True else
  let j1 = ac_joinable ctx sys p in
  if j1 = True then True else
  let j2 = instance_joinable ctx sys p in
  if j2 = True then True else
  j1 <||> j2
  (contradictory_constraints ctx sys) <||>*)

and r_joinable ctx sys p = 
  Rewriting.nf sys.trs p.s = (Rewriting.nf sys.trs p.t)

and e_instance ctx sys p =
  let es_symm = [ t,s | s,t <- sys.es ] @ sys.es in
  List.exists (Rule.is_instance (p.s,p.t)) es_symm

and joinable_args ctx sys p =
 match p.s,p.t with
   | F(f, ss), F(f', ts) when f = f' ->
     List.fold_left2 (fun b si ti -> joinable ctx sys p <&&> b) True ss ts
   | _ -> False

and ac_joinable ctx sys p =
  let join_for = ac_joinable_for ctx sys p in
  if Theory.Ac.equivalent sys.acsyms (p.s,p.t) then True
  else
    let jcheck b f = if b = True then b else join_for f <||> b in
    List.fold_left jcheck False sys.acsyms

and ac_joinable_for ctx sys p f =
  if !debug then Format.printf "%s. check f joinability of %a wrt %!" p.id Rule.print (p.s,p.t);
  if not (List.exists (Rule.variant (Ac.associativity f)) sys.trs)  ||
    not (order_extensible p.var_order (p.s, p.t)) ||
    (Term.is_variable p.s && Term.is_variable p.t)
  then
    False
  else
    (* add variables not yet considered in order *)
    let varords = extend_var_orders p.var_order (p.s,p.t) in
    let joinable o i =
      let id = p.id ^ (string_of_int i) ^ "-" in
      ac_joinable_for_ord ctx sys {p with var_order = o; id = id }
    in
    let jcheck a (i,(o,st)) = if a = False then a else joinable o i f <&&> a in
    List.fold_left jcheck True (Listx.index varords)

and ac_joinable_for_ord ctx sys p f =
  if !debug then (
    Format.printf "%s. check AC joinability of %a wrt %!\n%!" p.id Rule.print (p.s,p.t);
    print_order p.var_order;
    Format.printf "\n%!");
  let s,t = p.s, p.t in
  let c = ac_join ctx sys (order_to_conditions p.var_order) f s t in
  (* TODO: reducts instead? *)
  if c <> False then (
    if !debug then (
      if c = True then Format.printf "   AC joined\n%!"
      else Format.printf "   maybe AC joined\n%!");
    c)
  else (
    let s', t' = Rewriting.nf sys.trs s, Rewriting.nf sys.trs t in
    if !debug then 
      Format.printf "  Eq is %a = %a going for instantiation\n%!" Term.print s' Term.print t';
    if contradictory_constraints sys ctx p then True 
    else
      let zs = List.concat [ variables x | x <- p.var_order; is_variable x ] in
      let xs = Listset.diff (Rule.variables (s, t)) zs in
      if xs <> [] then
        (* more case distinction possible *)
        ac_joinable_for ctx sys {p with s = s'; t = t'} f
      else instance_joinable ctx sys { p with s = s'; t = t' } f)

and instance_joinable ctx sys p ac =
  if p.inst <= 0 then False else
  match List.rev p.var_order with
   | (V x :: _) -> ( (* take smallest *)
    if !debug then Format.printf "  instantiate %a \n" Term.print (V x);
    let rec vs a = if a=0 then [] else (V (Sig.fresh_var ())) :: (vs (a-1)) in 
    let sub (f, a) = substitute [(x, F(f, vs a))] in
    let fs = Rules.signature (sys.es @ sys.trs) in
    let instance_joinable (f,a) =
      let sub = sub (f,a) in (* call sub only once -> different vars*)
      let s0,t0 = sub p.s, sub p.t in
      let s1,t1 = Rewriting.nf sys.trs s0, Rewriting.nf sys.trs t0 in
      let xs = List.map sub p.var_order in
      (*if !debug then (
        Format.printf "  Instantiated to %a, reduced to %a wrt %!" Rule.print (s0, t0) Rule.print (s1,t1);
        print_order xs;
        Format.printf "\n%!");*)
      if s1 = t1 then True
      (* instantiation is not in normal form: kill TODO prove *)
      else if List.exists (Rewriting.reducible_with sys.trs) xs then 
       (if !debug then Format.printf "reducible, kill\n%!"; True) 
      else (
        let id = p.id ^ Sig.get_fun_name f ^ "-" in
        let p' = { s = s1; t = t1; inst = p.inst-1; var_order = xs; id = id } in
        ac_joinable_for_ord ctx sys p' ac)
    in
    let ijoin_check a f = if a = False then a else instance_joinable f <&&> a in
    List.fold_left ijoin_check True fs)
   | _ -> False
;;

let lookup trs es st =
  let covered (trs', es', st') =
    Listset.subset trs trs' && Listset.subset es es' &&
    Variant.eq_variant st st'
  in
  List.exists covered !joinable_cache
;;

let joinable ctx ord (trs, es, acsyms) st d =
  debug := d;
  if lookup trs es st then true
  else (
    if d then Format.printf "START\ %a n%!" Rule.print st;
    let j = match joinable ctx (mk_sys trs es acsyms ord) (mk_problem st 2) with
      | True -> true
      | False -> false
      | Maybe c -> if check_ordering_constraints trs c then
        (if d then Format.printf "Ordering constraints SAT\n%!"; true) else
        (if d then Format.printf "Ordering constraints UNSAT\n%!"; false)     
    in
    if d then (
      if not j then Format.printf "Not joinable: %a in %a\n" Rule.print st Rules.print es;
      Format.printf "END: %a %s\n%!" Rule.print st (if j then "YES" else "NO"));
    if j then joinable_cache := (trs, es, st) :: !joinable_cache;
    j)
;;