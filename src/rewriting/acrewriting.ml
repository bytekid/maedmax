(*** MODULES *****************************************************************)
module L = List
module Sub = Term.Sub
module H = Hashtbl
module ACL = Aclogic
module T = Term
module R = Rule
module Sig = Signature
module Lx = Listx

(*** TYPES *******************************************************************)
type overlap = {
  inner: Rule.t;
  pos: T.pos;
  outer: Rule.t;
  sub: Subst.t
}

(*** GLOBALS *****************************************************************)
let match_cache : (T.t * T.t, Subst.t list) H.t = H.create 256
let unify_cache : (T.t * T.t, Subst.t list) H.t = H.create 256
let cp_cache : (R.t * T.pos * R.t, overlap list) H.t = H.create 256
let reducts_cache : (T.t, T.t list) H.t = H.create 256
let reducible_cache : (T.t * Rule.t, bool) H.t = H.create 256

(*** FUNCTIONS ***************************************************************)
let pos_string = function
  | [] -> "e"
  | i :: p ->
    let si = string_of_int in
    List.fold_left (fun s i -> s ^ "." ^ (si i)) (si i) p
;;

let mk_overlap i p o s =
  (*Format.printf "  make overlap <%a, %s, %a>\n%!"
    Rule.print i (pos_string p) Rule.print o;*)
  {
  inner = i; 
  pos = p; 
  outer = o;
  sub = s
}

let next_var v = v + 1

let var_zero = 0

let root_pos = []

let flatten t = T.flatten (Sig.ac_symbols ()) t

(* caching unification/matching speeds up by > 40% on wcr for groups/rings *)
let cache c k f = try H.find c k with Not_found -> let v = f k in H.add c k v; v
let match_term t l = cache match_cache (t, l) (fun (t,l) -> ACL.match_term t l)
let unify t l = cache unify_cache (t, l) (fun (t,l) -> ACL.unify t l)

(* return all pairs (ys,zs) such that ys \cup zs = xs and both ys and zs are
nonempty. (Symmetries not eliminated, i.e., both (ys,zs) and (zs,ys) occur
in the result) *)
let bipartition xs =
  let rec bipartition acc = function
  | [] -> acc
  | x :: xs -> bipartition (L.concat [ [x :: a, b; a, x :: b] | a,b <- acc]) xs
  in L.filter (fun (ys,zs) -> ys<>[] && zs<>[]) (bipartition [[],[]] xs)
;;

(* rename variables in term, extending substitution sub and with next variable
  v. Returns renamed term, extended substitution, and the next free variable*)
let rec normalize sub v = function
| T.V x -> (
  try (Sub.find x sub, sub, v)
  with Not_found -> (T.V v, Sub.add x (T.V v) sub, next_var v))
| T.F (f, ts) ->
  let fold_norm (l,s,v) t = let (t',s,v) = normalize s v t in (t'::l,s,v) in
  let (ts', sub', v') = L.fold_left fold_norm ([], sub, v) ts in
  (T.F (f, L.rev ts'), sub', v')
;;

(* rename variables in term pair to improve caching (and readability) *)
let normalize_terms (t, u) =
  let t', s, v = normalize Sub.empty var_zero t in
  let u', _, _ = normalize s v u in
  (t', u')
;;

(* make term of AC symbol f and (arbitrary but positive number of) arguments *)
let rec fterm f = function 
    [t] -> t 
  | [_; _] as ts -> T.F(f, ts)
  | t :: ts -> T.F(f, [t; fterm f ts])
  | _ -> failwith "Acrewriting.fterm: empty argument list not allowed"
;;

(* rearrange arguments of AC symbols for canonical representation *)
let rec ac_normalize t =
  match flatten t with (* also sort arguments of AC symbols *)
  | T.F(f, ts) ->
    if not (Sig.is_ac_symbol f) then T.F(f, L.map ac_normalize ts)
    else fterm f (L.map ac_normalize ts)
  | v -> v
;;

(* check whether two terms are AC equivalent *)
let ac_equivalent t u = flatten t = flatten u

 (* given term t, return list pts of pairs (p, u) such that u is AC equivalent
to t and p is a position in u. It is complete in the sense that whenever
p and t' satisfy this condition then there is some (p', u') in pts such
that u|_p is the same as u'|_p' and p and p' coincide on the non-AC part. *)
let ac_pos pred =
  let rec ac_pos = function
  | T.V _ as x -> if pred x then [root_pos, x] else []
  | T.F (f, ts) as t ->
    if not (Sig.is_ac_symbol f) then
      (* just add argument numbers to positions in subterms *)
      let add i p u =  i :: p, T.replace t u [i] in
      let ps = [ add i p u | i, ti <- Lx.index ts; p, u <- ac_pos ti] in
      if pred t then (root_pos, t) :: ps else ps
    else
      let tfs  = T.args (flatten t) in
      let add_part (xs, zs) = match xs with
        (* for singleton partition [ti] add all positions in ti *)
      | [ti] -> [ 0 :: p, fterm f (u :: zs) | p, u <- ac_pos ti]
      (*ac_pos p ti >>= M.map (fun (p,u) -> return (0::p,fterm f (u::zs)))*)
      (* non-singleton partitions give rise to AC term *)
      | _ ->
        let ti = T.F(f, [fterm f xs; fterm f zs]) in
        (if pred ti then [[0], ti] else [])
    in
    (* split argument set of flattened term into two *)
    let ps = Lx.unique [ pu | xzs <- bipartition tfs; pu <- add_part xzs ] in
    if pred t then (root_pos, t) :: ps else ps
  in ac_pos
;;

let ac_funs_pos = ac_pos (fun t -> not (T.is_variable t))

let ac_vars_pos = ac_pos T.is_variable

let ac_pos = ac_pos (fun _ -> true)

 (* positions relevant for overlaps with extension rules: only those covering
the extension variable (supposed to be first argument) *)
let xpos = function
| T.F (f, [x; t2]) as t ->
  if not (Sig.is_ac_symbol f) || not (T.is_variable x) then
    failwith "Acrewriting.xpos requires argument to be result of AC extension"
  else
    let t2s = T.args (flatten t2) in
    let fterm xs zs = T.F(f, [fterm f (x :: xs); fterm f zs]) in
    let ps = [[0], fterm xs zs | xs, zs <- bipartition t2s] in
    (root_pos, t) :: (Lx.unique ps)
    (* 
	  flatten t2 >>= (return @.@ T.args) >>= fun t2s ->
    let fterm xs zs = T.make_fun f [fterm f (x :: xs); fterm f zs] in
		let for_partition (xs,zs) = return (P.of_list [0], fterm xs zs) in
	  M.map for_partition (bipartition t2s) >>=
    (return @.@ L.unique_hash @.@ (L.cons (P.root,t)))
    *)
| _ -> failwith "Acrewriting.xpos: invalid argument"
;;

(* AC rewrite term t at position p with rule; returns list of reducts, which is
  empty if no step is possible. The result is AC-sorted, which is crucial
  for e.g. reduct computation to avoid blowup  *)
let rewrite_at t (l, r) p =
  let s = T.subterm_at p t in
  let rdcs = [T.replace t (T.substitute sigma r) p | sigma <- match_term s l] in
  [ ac_normalize u | u <- rdcs ]
(*
let c = C.of_term p t in
let s = T.subterm p t in
let l, r = R.to_terms rule in
let rewrite_with sigma = return (C.apply (Sub.apply_term sigma r) c) in
match_term s l >>= M.map (rewrite_with >=> ac_normalize) *)
;;

let direct_reducts t trs =
  let compute t =
    let rdcts rl = L.concat [ rewrite_at t rl p | p,t <- ac_funs_pos t] in
    Lx.unique (L.concat [rdcts rl | rl <- trs])
  in
  (*cache reducts_cache*) compute t
 (* 
  M.get >>= fun c ->
  let compute t =
	 ac_funs_pos t >>= fun ps ->
	 let with_rl rl = M.flat_map (fun (p, t) -> rewrite_at t rl p) ps in
	 M.flat_map with_rl (Trs.to_list trs) >>=
	 (return @.@ L.unique_hash)
  in cache c.reducts_cache compute t
 *)
;;

let direct_reducts_list trs width (ts, acc) =
  let rs = L.concat [direct_reducts t trs | t <- ts] in
  let rs = if width < 0 then rs else Lx.take_at_most width (Lx.unique rs) in
  let acc' = acc @ ts in
  let ts' = Listset.diff rs acc' in
  (ts', acc')
  (*M.flat_map (flip direct_reducts trs) ts >>= fun rs ->
  let rs = if width < 0 then rs else L.take width (L.unique_hash rs) in
  let acc' = acc @ ts in
  let ts' = L.diff rs acc' in
 return (ts', acc')*)
 ;;

let rec reducts' n width acc ts trs =
  if n = 0 then acc
  else
    let ts', acc' = direct_reducts_list trs width (ts, acc) in
    if ts' = [] then acc'
    else reducts' (n - 1) width (L.rev_append acc' ts') ts' trs
(* match n with
  | 0 -> return acc
  | n -> (
   direct_reducts_list trs width (ts, acc) >>= fun (ts', acc') ->
   if ts' = [] then return acc'
   else reducts' (n-1) width (acc'@ts') ts' trs
  )
*)
;;

let reducts ?(n = ~-1) ?(width = ~-1) t trs = reducts' n width [] [t] trs

let rec are_joinable' n width (us, uacc) (ts, tacc) trs =
  let joined ts = L.exists (fun u -> L.exists (ac_equivalent u) ts) in
  let step = direct_reducts_list trs width in
  if n = 0 then joined (ts @ tacc) (us @ uacc)
  else
    let (ts',tacc'), (us',uacc') = step (ts, tacc), step (us, uacc) in
    let b = joined (ts' @ tacc') (us' @ uacc') in
    if b || (ts' = [] && us' = []) then b
    else are_joinable' (n - 1) width (ts', tacc') (us', uacc') trs
  (* 
  let joined ts = M.exists (fun u -> M.exists (acequivalent u) ts) in
  let step = direct_reducts_list trs width in
  match n with
   | 0 -> joined (ts@tacc) (us@uacc)
   | n ->
  M.project step ((ts, tacc), (us, uacc)) >>= fun ((ts',tacc'), (us',uacc'))  ->
  joined (ts'@tacc') (us'@uacc') >>= fun b ->
  if b || (ts' = [] && us' = []) then return b
  else are_joinable' (n-1) width (ts',tacc') (us',uacc') trs*)
;;

let are_joinable ?(n = ~-1) ?(width = ~-1) trs u t =
  are_joinable' n width ([u], []) ([t], []) trs
;;

let is_normalform t trs = direct_reducts t trs = []

(* find an AC normal form in a given list of terms *)
let find_normalform ?(n = ~-1) term trs =
  let rds = reducts ~n:n term trs in
  let find r t = 
    match r with
    | Some _ as nf -> nf
    | _ -> if is_normalform t trs then Some t else None
  in match L.fold_left find None (term :: rds) with
  | None -> (match rds with r :: _ -> r | _ -> term)
  | Some u -> u
;;

let is_reducible_rule term rl =
  let compute (term, (l,r)) =
    List.exists (fun (_,u) -> match_term u l <> []) (ac_funs_pos term)
  in
  cache reducible_cache (term, rl) compute
;;

 (* check whether <inner, p, outer> allows for an AC overlap, where p is a
position in the lhs of outer *)
let overlaps_of inner p outer =
  let compute (inner, p, outer) =
    let m = List.fold_left max 0 (Rule.variables inner) in
    let outer, _ = Rule.rename_canonical ~from:(m+1) outer in
    let s = T.subterm_at p (fst outer) in
    (*Format.printf "test overlap <%a, %s, %a>? %d\n%!"
      Rule.print inner (pos_string p) Rule.print outer
      (List.length (unify s (fst inner)));*)
    [mk_overlap inner p outer sigma | sigma <- unify s (fst inner)]
  in cache cp_cache (inner, p, outer) compute
;;
    
let has_linear_var_as_flat_arg (l, r) =
  let l, r = flatten l, flatten r in
  match l, r with
  | T.F(f, ts), T.V x -> 
    let txs, ts' = L.partition ((=) (T.V x)) ts in
    let no_sub = L.for_all (fun u -> not (L.mem (T.V x) (T.subterms u))) ts' in
    L.length txs = 1 && no_sub
  | T.F(f, ls), T.F(g, rs) when f = g -> 
    let is_lin_var ti ts =
      let tis, ts' = L.partition ((=) ti) ts in
      let as_sub = L.exists (fun tj -> L.mem ti (T.subterms tj)) ts' in
      T.is_variable ti && L.length tis = 1 && not as_sub
    in
    L.exists (fun x -> is_lin_var x ls && is_lin_var x rs) ls
  | _ -> false
  (*
  M.project flatten (R.to_terms rl) >>= fun (l,r) ->
  let f = Option.the (T.root l) in
  let ls,rs = T.args l, T.args r in
  let is_lin_var ti ts =
    let tis, ts' = L.partition ((=) ti) ts in
    let as_sub = L.exists (fun tj -> L.mem ti (T.subterms tj)) ts' in
    T.is_var ti && L.length tis = 1 && not as_sub
  in
  let is_lin_var_rhs ti = r=ti || T.root r = Some f && is_lin_var ti rs in
  return (L.exists (fun x -> is_lin_var x ls && is_lin_var_rhs x) ls)*)
;;

let extend (l, r) = 
  let f = T.root l in
  if not (Sig.is_ac_symbol f) || has_linear_var_as_flat_arg (l, r) then []
  else
    let x = Sig.fresh_var () in
    [T.F(f,[T.V x; l]), T.F(f,[T.V x; r])]
;;

(* compute AC overlaps among (extensions of) rules in trs *)
let overlaps trs =
  let rxs = [ rlx, xpos (fst rlx) | rl <- trs; rlx <- extend rl ] in
  let ros = [ rl, ac_funs_pos (fst rl) | rl <- trs ] in
  let roxs = [r, ps | (_,r),ps <- ros @ rxs] in
  let os = [ overlaps_of ri p (u, r) | ri <- trs; r, ps <- roxs; p,u <- ps] in
  Lx.unique (L.concat os)
(*
M.map (fun r -> fpos r >>= fun p -> return (r,p)) ro >>= fun rop ->
(* for extended rules positions involving fresh variable suffice *)
M.flat_map (liftM (function Some r -> [r] |_ -> [])@.@extend) ro >>= fun rx ->
M.map (fun r -> xpos (R.lhs r) >>= fun ps -> return (r, ps)) rx >>= fun rxp ->
(* combinations of outer and inner rule: extensions only required for outer *)
let rpairs = L.product (rxp @ rop) (Trs.to_list trs) in
let of_rls ((o, ps),i) =
  (* l' is AC equivalent to original lhs of outer *)
  let mk_overlap (p,l') = check_overlap i p (mk_rule l' (R.rhs o)) in
  M.flat_map mk_overlap ps
in
M.flat_map of_rls rpairs >>=
(return @.@ L.unique_hash)*)
;;

let overlaps2' trsi trso =
  let rxs = [ rlx, xpos (fst rlx) | rl <- trso; rlx <- extend rl ] in
  let ros = [ rl, ac_funs_pos (fst rl) | rl <- trso ] in
  let roxs = [r, ps | (_,r),ps <- ros @ rxs] in
  let os = [ overlaps_of ri p (u, r) | ri <- trsi; r, ps <- roxs; p,u <- ps] in
  Lx.unique (L.concat os)
;;

let overlaps2 trs1 trs2 = overlaps2' trs1 trs2 @ (overlaps2' trs2 trs1)

(* make AC critical peak from AC overlap *)
let cpeak_from_overlap o =
  let sub = T.substitute o.sub in
  let u = sub (T.replace (fst o.outer) (snd o.inner) o.pos) in
  let w = sub (snd o.outer) in
  let v = sub (fst o.outer) in
  (u,v,w)
;;

(* make AC critical pair from AC overlap *)
let cp_from_overlap o =
  let (u,v,w) = cpeak_from_overlap o in normalize_terms (u,w)
;;

let cps trs = [cp_from_overlap o | o <- overlaps trs]

let cps2 trs1 trs2 = [cp_from_overlap o | o <- overlaps2 trs1 trs2]

let is_wcr ?(n = ~-1) trs =
  let cps = cps trs in
  let cps = L.map (fun (s,t) -> if s < t then (s,t) else (t,s)) cps in
  L.for_all (fun (s, t) -> are_joinable ~n:n ~width:8 trs s t) cps
;;

let test () =
  Aclogic.test ();
  let x = Sig.var_called "x" in
  let y = Sig.var_called "y" in
  let z = Sig.var_called "z" in
  let u = Sig.var_called "u" in
  let v = Sig.var_called "v" in
  let w = Sig.var_called "w" in
  let x,y,z,u,v,w = T.V x, T.V y, T.V z, T.V u, T.V v, T.V w in
  let f = Sig.fun_called "f" in
  Sig.add_ac_symbol f;
  let a = Sig.fun_called "a" in
  let b = Sig.fun_called "b" in
  let c = Sig.fun_called "c" in
  let d = Sig.fun_called "d" in
  let e = Sig.fun_called "e" in
  let g = Sig.fun_called "g" in
  let h = Sig.fun_called "h" in
  let zero = Sig.fun_called "0" in
  let one = Sig.fun_called "1" in
  let m = Sig.fun_called "m" in
  Sig.add_ac_symbol m;
  let a_ = T.F(a, []) in
  let b_ = T.F(b, []) in
  let c_ = T.F(c, []) in
  let d_ = T.F(d, []) in
  let e_ = T.F(e, []) in
  let zero = T.F(zero, []) in
  let one = T.F(one, []) in
  let faa = T.F(f, [a_;a_]) in
  let fab = T.F(f, [a_;b_]) in
  let fac = T.F(f, [a_;c_]) in
  let fxx = T.F(f, [x;x]) in
  let ga = T.F(g, [a_]) in
  let gu = T.F(g, [u]) in
  let gx = T.F(g, [x]) in
  let gzero = T.F(g, [zero]) in
  let faaa = T.F(f, [a_;faa]) in
  let gfaa = T.F(g, [faa]) in
  let faaaa = T.F(f, [faa;faa]) in
  let fabc = T.F(f, [a_;T.F(f, [c_;b_])]) in
  let habc = T.F(h, [a_;T.F(f, [b_;c_])]) in
  let fgaab = T.F(f, [ga;T.F(f, [a_;b_])]) in
  let faby = T.F(f, [a_;T.F(f, [b_;y])]) in
  let fxy = T.F(f, [x;y]) in
  let fxyxy = T.F(f, [fxy;fxy]) in
  let t1 = T.F(f, [fxy; y]) in
  let t2 = T.F(f, [gu; faaa]) in
  let t3 = T.F(f, [habc; fxy]) in
  (* Abelian group *)
  let mk_rule s t = (s,t) in
  let g0 = mk_rule (T.F(f, [x; gx])) zero in
  let g1 = mk_rule (T.F(f, [x; zero])) x in
  let g2 = mk_rule (T.F(g, [fxy])) (T.F(f, [gx; T.F(g, [y])])) in
  let g3 = mk_rule (T.F(g, [zero])) zero in
  let g4 = mk_rule (T.F(g, [gx])) x in
  let group = [g0; g1; g2; g3; g4] in
  (* commutative ring *)
  let r1 = mk_rule (T.F(m, [fxy; z]))
                      (T.F(f, [T.F(m, [x;z]); T.F(m, [y;z])])) in
  let r2 = mk_rule (T.F(m, [one; x])) x in
  let r3 = mk_rule (T.F(m, [zero; x])) zero in
  let r4 = mk_rule (T.F(m, [gx; y])) (T.F(g, [T.F(m, [x;y])])) in
  let ring = [r1; r2; r3; r4] @ group in
  (* distributive lattice *)
  let j = Sig.fun_called "j" in
  Sig.add_ac_symbol j;
  let l1 = mk_rule (T.F(m, [T.F(j, [x;y]); z]))
                      (T.F(j, [T.F(m, [x;z]); T.F(m, [y;z])])) in
  let l2 = mk_rule (T.F(j, [T.F(m, [x; y]); x])) x in
  let l3 = mk_rule (T.F(m, [x; x])) x in
  let l4 = mk_rule (T.F(j, [x; x])) x in
  let dlattice = [l1; l2; l3; l4] in
  (* testing acpos *)
  let app_string s (p, t) =
   assert (try let _ = T.subterm_at p t in true with _ -> false);
   let ts = T.to_string t in
   (s ^ "\n (" ^ ts ^ ", pos)")
  in
  let show n ps =
   let s = List.fold_left app_string "" ps in
   Format.printf "%s\n" s;
   assert (List.length ps == n)
  in 
  let check_acpos t n =
   let ts = T.to_string t in
   Format.printf "AC positions in %s:" ts;
   show n (ac_pos t)
  in
  check_acpos faby 7;
  check_acpos fgaab 8;
  check_acpos t1 5;
  check_acpos t2 8;
  check_acpos t3 11;
  check_acpos fxy 3;
  check_acpos (fst r1) 5;
  (* testing rewrite *)
  let check_reducts t rule res =
    let ts = T.to_string t in
    let rs = R.to_string rule in
    let rds = direct_reducts t [rule] in
    let app s u = let v = T.to_string u in s^"\n "^v in
    let s = List.fold_left app "" rds in
    Format.printf "Rewriting %s with %s yields %s\n%!" ts rs s;
    let eq = List.for_all (fun t -> List.exists (ac_equivalent t) rds) res in
     assert (List.length res = (List.length rds) && eq)
  in
  check_reducts fxy (mk_rule fxy d_) [d_];
  check_reducts fabc (mk_rule fxy d_)
   [d_; T.F(f, [a_;d_]); T.F(f, [b_;d_]); T.F(f, [c_;d_])];
  check_reducts t2 (mk_rule gu d_) [T.F(f, [faaa; d_])];
  check_reducts fabc (mk_rule gu d_) [];
  check_reducts fabc (mk_rule fxx gu) [];
  check_reducts faaa (mk_rule fxx x) [faa];
  check_reducts faaaa (mk_rule fxx x) [faa; faaa];
  check_reducts gfaa (mk_rule fxx x) [T.F(g, [a_])];
  check_reducts fxyxy (mk_rule fxx x)
   [fxy; T.F(f, [x; fxy]); T.F(f, [y; fxy])];
  (* testing overlaps and CPs *)
  let check_cps trs res =
    let trss = Rules.to_string trs in
    let cps = cps trs in
    let app s (u,v) = (s^"\n "^(T.to_string u)^" = "^(T.to_string v)) in
    let pair_aceq (s,t) (u,v) = ac_equivalent s u && ac_equivalent t v in
    let cps = List.filter (fun (u, v) -> not (are_joinable trs u v)) cps in
    let s = List.fold_left app "" cps in
    Format.printf "AC CPs for {%s} are %s\n%!" trss s;
    let eq = List.for_all (fun cp -> List.exists (pair_aceq cp) cps) res in
    assert (List.length res == (List.length cps) && eq)
  in
  let rl1 = mk_rule ga a_ in
  let rl2 = (mk_rule fxx x) in
  let rl3 = mk_rule fab e_ in
  let rl4 = mk_rule fac d_ in
  let rl5 = mk_rule (T.F(f, [x; one])) x in
  let rl6 = mk_rule fxy x in
  let rl7 = mk_rule (T.F(f, [x;a_])) b_ in
  let rl8 = mk_rule (T.F(f, [x;a_])) (T.F(m, [x;a_])) in
  let fce, fbd = T.F(f, [c_;e_]), T.F(f, [b_;d_]) in
  check_cps ([rl3; rl4]) [fce,fbd; fbd, fce];
  check_cps ([g0; g1]) [zero, gzero];
  let check_wcr trs res = (
    let trss = Rules.to_string trs in
    let b = is_wcr trs in
    Format.printf "TRS {%s} is AC-wcr: %B\n%!" trss b;
    assert (b == res))
  in
  check_wcr ([rl1]) true;
  check_wcr ([rl2]) true;
  check_wcr ([rl3; rl4]) false;
  check_wcr ([rl2; rl3; rl4]) false;
  check_wcr ([rl5; g1]) false;
  check_wcr ([rl6]) false;
  check_wcr ([rl7]) false;
  check_wcr ([rl8]) false;
  check_wcr (group) true;
  check_wcr (ring) true;
  check_wcr (dlattice) true
;;