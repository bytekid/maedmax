(*** SUBMODULES ***************************************************************)
module A = Array
module F = Format
module Sub = Subst
module Sig = Signature
module T = Term

(* An inefficient diophantine equation solver based on the completion procedure
   described (for instance) in Clausen and Fortenbacher: Efficient solution of
	 linear diophantine equations (1983). *)
module Dio = struct
	(* the unit vector with a 1 at position (i-1) *)
	let ei i n =
	  let a = A.make n 0 in
	  A.set a (i-1) 1;
	  A.to_list a
	;;

	let add xs ys = List.map (fun (x, y) -> x + y) (Listx.zip xs ys);;
	let add2 (a,b) (c,d) = (add a c, add b d);;
	let zero n = A.to_list (A.make n 0);;
	(* initial solution proposals:
	   fill unit vector for a positive variable up with zeros for the negatives *)
	let p0 m n = List.map (fun i -> ei i m, zero n) (Listx.range 1 m);;
	let sum = List.fold_left2 (fun s a b -> s + a*b) 0;;

	(* the defect *)
	let d xs ys (px,py) = (sum xs px) - (sum ys py);;
	(* component-wise smaller or equal *)
	let leq = List.fold_left2 (fun v a b -> v && (a <= b)) true;;

  (* check whether proposal (px, py) is minimal wrt m, i.e., there is no smaller
	  solution in m *)
	let minimal (px, py) m =
    not (List.exists (fun (x,y) -> (leq x px) && (leq y py)) m)
	;;

  (* main completion procedure to compute complete list of minimal solutions:
	   - d is a defect function
		 - en and em are lists of unit vectors
		 - p is a list of solution proposals (initially supposed to be p0)
		 - m_all is the already computed list of minimal solutions
	*)
	let rec complete d en em p m_all =
	if p = [] then Listx.unique m_all
	else
	  (* partition nonminimal proposals into negative/positive defect *)
		let pn,pp =
			List.partition (fun p -> d p < 0) (List.filter (fun x -> d x <> 0) p)
		in
		(* try to correct proposals by adding unit vector *)
    let q' =
      List.concat [ List.map (add2 ej) pn | ej <- en ] @
      List.concat [ List.map (add2 ei) pp | ei <- em ]
		in
		(* those with defect 0 are new minimal ones *)
		let m' = List.filter (fun s -> d s = 0) q' in
		let p' = List.filter (fun p -> minimal p m_all) (Listset.diff q' m') in
		complete d en em p' (m' @ m_all)
	;;

  (* Compute basis of solutions for homogeneous diophantine equation
	   a_1 x_1 + ... + a_m x_m - b_1 y_1 - ... - b_n y_n = 0
	 *)
	let basis aa bb =
		let m,n = List.length aa, List.length bb in
		let d = d aa bb in (* defect function, hiding coefficients *)
		let em = List.map (fun i -> ei i m, zero n) (Listx.range 1 m) in
		let en = List.map (fun i -> zero m, ei i n) (Listx.range 1 n) in
		complete d em en (p0 m n) []
	;;

  (* Compute basis of solutions for homogeneous diophantine equation
	   x_i_1 + ... + x_i_k - y_j_1 - ... - y_j_l = 0
		 (without coefficients)
   *)
	let solve xs ys =
		let xs', ys' = Listx.count xs, Listx.count ys in
		let bs = basis (List.map snd xs') (List.map snd ys') in
		let vars = List.map fst (xs' @ ys') in
	  List.map (fun (xb, yb) -> Listx.zip vars (xb @ yb)) bs
	;;
end


(*** FUNCTIONS ***************************************************************)
(* zero substitution list {{}} *)
let zero_list = [Sub.empty]

let is_ac_symbol = Sig.is_ac_symbol

let print_sub sub =
  let append s (x, t) =
    let t = T.to_string t in
    let x = Sig.get_var_name x in
    (s ^ " " ^ x ^ "->" ^ t)
  in
  List.fold_left append "" sub
;;

let print_subs ss =
  let add s sub = let s' = print_sub sub in s ^ s' ^ "\n " in
  let s = List.fold_left add " " ss in
  Format.printf "%s%!" s
;;

(* flatten term and sort AC arguments (order is crucial for
  algorithm by Christian/Lincoln) *)

  (* sorts list of terms such that constants come before compound
  terms where the root has positive arity come before variables *)
let rec lex = function
  | [], [] -> 0
  | [], _ -> -1
  |_, [] -> 1
  | x :: xs, y :: ys -> let c = ucmp x y in if c=0 then lex (xs,ys) else c
  and ucmp t t' =
  match t, t' with
      T.V x, T.V y -> Pervasives.compare x y
    | T.F _, T.V _ -> -1
    | T.V _, T.F _ -> 1
    | T.F(_, []), T.F(_, t::ts) -> -1
    | T.F(_, t :: ts), T.F(_, []) -> 1
    | T.F(f, fs), T.F(g, gs) when f = g -> lex (fs, gs)
    | T.F(f, _), T.F(g, _) -> Pervasives.compare f g
;;

let flatten t = T.flatten (Sig.ac_symbols ()) t

let sort_flatten t =
  match flatten t with
  | T.F(f, ts) -> T.F(f, List.sort ucmp ts)
  | v -> v
;;

(* removes common occurrences in both argument lists (like mutual
  multiset difference *)
let remove_common_args xs ys =
  let rec remove (sx, sy) = function
    | [], ys -> List.rev sx, List.rev sy @ ys
    | xs, [] -> List.rev sx @ xs, List.rev sy
    | x :: xs, y :: ys when x = y -> remove (sx, sy) (xs, ys)
    | x :: xs, y :: ys when ucmp x y < 0 -> remove (x :: sx, sy) (xs, y :: ys)
    | x :: xs, y :: ys -> remove (sx, y :: sy) (x :: xs, ys)
  in remove ([], []) (xs, ys)
;;

(* * *          auxiliary functions for Fortenbacher's algorithm         * * *)
(* For s=f(s_1,...,s_m) and t=f(t_1,...,t_n) for AC-Symbol f, abstract s t
  returns a pair (f(x_1,...,x_m), f(y_1,...,y_n)) together with pairs
  (x_i,s_i) and (y_j,t_j) where x_i, y_j are fresh variables.*)
let abstract all_fresh f ss ts =
  let var = function
    | T.V x when all_fresh -> x
    | u -> Sig.fresh_var ()
  in
  let xs = List.map var ss in
  let xst = [T.V x | x <- xs] in
  let ys = List.map var ts in
  let yst = [T.V y | y <- ys] in
  let c0 = T.F(f, xst), T.F(f, yst) in
  (c0, (Listx.zip xst ss) @ (Listx.zip yst ts), xs, ys)
;;

(* fill matrix with T.V vi lists according to solutions *)
let to_semigroup f ass =
  let ith v i = [T.V v | _ <- Listx.range 1 i] in
  let sg a (acc, vs) =
    let vi = Sig.fresh_var () in
    let a' = List.map (fun (x, i) -> ith vi i) a in
    (a' :: acc, vi :: vs)
  in
  let ass, vs = List.fold_right sg ass ([], []) in
  (A.of_list (List.map A.of_list ass), vs)
;;

(* Construct all subsets of the assignment set b such that there is no zero
  column sum. Some constraints:
  - for a column corresponding to a non-variable term, the column sum is 1
  - delete rows where ones are at positions corresponding to non-unifiable
    terms (only implemented partially here)
  where the two conditions are checked by check_row *)
let check_row terms b i =
  let a = List.nth b i in
  assert(List.length a = (List.length terms));
  let ts = [t, value | t, (_, value) <- Listx.zip terms a] in
  let compound_true (t,v) = (v > 0) && (not (T.is_variable t)) in
  let ts = List.filter compound_true ts in
  (* no entries > 1 *)
  if List.for_all (fun (_,v) -> v = 1) ts then
    (* no nonunifiable entries *)
    let ts_square = [t, u | t <- ts; u <- ts] in
    List.for_all (fun ((t,_),(u,_)) -> T.root t = (T.root u)) ts_square
  else
    false
;;

let valid m terms subset =
  (*Array.iter (fun l -> Array.iter (fun j -> Format.printf "%i " l.(j)) l; Format.printf "\n" ) m;*)
  let col i =
    let s = List.fold_left (fun s j -> s + m.(j).(i)) 0 subset in
    if not (T.is_variable (List.nth terms i)) then s = 1 else s > 0
  in List.for_all (fun (i, _) -> col i) (Listx.index terms)
;;

let rec unique ?(c = compare) = function
  | [] -> []
  | x :: xs -> x :: (unique (~c:c) [ y | y <- xs; c x y <> 0 ])
;;

let subsets (ss, ts) b =
  (* filter out equal variable *)
  let is_var = T.is_variable in
  let cmp t s = if is_var t && (is_var s) then T.compare t s else 1 in
  let terms = unique ~c:cmp (ss @ ts) in (* same order as variables *)
  let indices = Listx.range 0 (List.length b - 1) in
  let indices = List.filter (check_row terms b) indices in
  (* matrix now more convenient *)
  let b' = List.map (List.map snd) b in
  let m = A.of_list (List.map A.of_list b') in
  (* possible index subsets *)
  let ixsets = Listx.remove [] (Listx.power indices) in
  (* check *)
  List.filter (valid m terms) ixsets
;;

let sum_up subsets b' vars f =
  let vars = Listx.index (Listx.unique vars) in
  let fterm f = function [x] -> x | args -> T.F(f, args) in
  let col_sum sub i = fterm f (List.concat [ b'.(r).(i) | r <- sub ]) in
  let add_binding sub s (i, v) = (v, col_sum sub i) :: s in
  let sub_for_subset s = List.fold_left (add_binding s) Sub.empty vars in
  let subs = List.map sub_for_subset subsets in
  subs
;;

let sub_equal s s' = Listset.equal s s'

(* make substitution idempotent *)
let make_idempotent sigma =
  let rec fix sigma sigman =
    let sigman' = Sub.compose sigman sigma in
    if sub_equal sigman' sigman then sigman
    else fix sigma sigman'
  in fix sigma sigma
;;

(* * *                      main unification procedure                   * * *)
(* Given terms s and t, return complete set of unifiers for s=_{AC} t.
  Calls unify' and simplifies returned set of bindings in that all
  bindings x -> t are removed where x does not occur in s or t. *)
let rec unify s t =
  (* restrict substitution to variables of interest *)
  let vars = Listset.union (T.variables s) (T.variables t) in
  let add s (x,t) = if List.mem x vars then (x, t) :: s else s in
  let simplify s = List.fold_left add Sub.empty s in
  match unify' s t with
  | Some ss -> Some (List.map simplify ss)
  | _ -> None
  (* Given terms s and t, return complete set of unifiers for s=_{AC} t.
    When matching, s is ground *)
and unify' s t =
  match s, t with
  | T.V x, _ ->
    if T.is_proper_subterm s t then None (* occur check *)
    else if s = t then (Some zero_list)
    else Some [[x, t]]
  | _, T.V y ->
    if T.is_proper_subterm t s then None (* occur check *)
    else Some [[y,s]]
  | T.F(a, []), T.F(b, []) -> (* both constants *)
    if a = b then Some zero_list
    else None
  | T.F(f, _), T.F(g, _) when f <> g -> None
  | T.F(f,ss), T.F(_, ts) -> ((* same root symbol *)
    if not (is_ac_symbol f) then (* assume length ss = length ts *)
      unify_with_list (Listx.zip ss ts) zero_list
    else
      let s', t' = sort_flatten s, sort_flatten t in
      let ss', ts' = remove_common_args (T.args s') (T.args t') in
      if ss' = [] && ts' = [] then
        Some zero_list
      else if ss' = [] || ts' = [] then
        None
      else
        (* (1) abstract non-variable terms *)
        let (_, cs, xs, ys) = abstract true f ss' ts' in
        (* (2) solve diophantine equations *)
        let b = Dio.solve xs ys in
        (* (3) make semigroup representation, fresh vars for rows *)
        let b', vars = to_semigroup f b in
        (* (4) find usable subsets of rows in b *)
        let bsubsets = subsets (ss', ts') b in
        (* (5) construct semigroup unifiers *)
        let gamma = sum_up bsubsets b' (xs @ ys) f in
        (* (6) make substitutions idempotent *)
        let theta = List.map make_idempotent gamma in
        unify_with_list cs theta
      )
  (* Given list (i.e. conjunction) of equations es+ set of substitutions
    subs, take union of CSU(es\theta) for all \theta in subs,
    where CSU(X) is complete set of unifiers for X. *)
and unify_with_list es subs =
  let add csus theta =
    let compose s = Sub.compose theta s in
    let cs = [ Term.substitute theta l, Term.substitute theta r | l,r <- es ] in
    match unify_conjunction cs with
    | None -> csus
    | Some z -> (List.rev_append (List.map compose z) csus)
  in
  match List.fold_left add [] subs with
  | [] -> None
  | subs -> (Some subs)
  (* Given a list (i.e. conjunction) of equations es, return complete set
    of unifiers for es. *)
and unify_conjunction cj =
  match cj with
  | [] -> Some zero_list (*e.g. unify (fxy,fxy) *)
  | [s, t] -> unify s t
  | (s, t) :: es ->
    match unify s t with
    | None -> None
    | Some ss -> unify_with_list es ss
;;

let unify s t =
  match unify s t with
  | Some ss -> unique ~c:(fun s t -> if Listset.equal s t then 0 else 1) ss
  | _ -> []
;;

let are_unifiable s t = unify s t <> []


let rec tsub_apply rho = function
  | T.F(_, []) as c -> if List.mem_assoc c rho then List.assoc c rho else c
  | T.F(f, ts) -> T.F(f,List.map (tsub_apply rho) ts)
  | v -> v
;;

let reverse_skolemization =
  let tsub_add s (x, t) = (t, T.V x) :: s in
  List.fold_left tsub_add []
;;

let skolemization =
  let rec skolemization s = function
    | T.V x ->
      if List.mem_assoc x s then s
      else (x, T.F(Sig.fresh_fun (), [])) :: s
    | T.F (f, ts) -> List.fold_left skolemization s ts
  in skolemization Sub.empty
;;

(* Returns a complete set of matching substitutions \sigma such that for
  every \theta in \sigma t\theta=s. *)
let match_term s t =
  let rho = skolemization s in
  let s' = Term.substitute rho s in
  let sigmas = unify s' t in
  let rho_inv = reverse_skolemization rho in
  [ [x, tsub_apply rho_inv t | x, t <- sigma] | sigma <- sigmas]
;;

let matches s t = match_term s t <> []


(* TESTS *)
let test () =
  let x = Sig.fresh_var_called "x" in
  let y = Sig.fresh_var_called "y" in
  let z = Sig.fresh_var_called "z" in
  let u = Sig.fresh_var_called "u" in
  let v = Sig.fresh_var_called "v" in
  let w = Sig.fresh_var_called "w" in
  let x,y,z,u,v,w = T.V x, T.V y, T.V z, T.V u, T.V v, T.V w in
  let f = Sig.fresh_fun_called "f" in
  Sig.add_ac_symbol f;
  let h = Sig.fresh_fun_called "h" in
  Sig.add_ac_symbol h;
  let a = Sig.fresh_fun_called "a" in
  let b = Sig.fresh_fun_called "b" in
  let c = Sig.fresh_fun_called "c" in
  let d = Sig.fresh_fun_called "d" in
  let e = Sig.fresh_fun_called "e" in
  let g = Sig.fresh_fun_called "g" in
  let a_ = T.F(a, []) in
  let b_ = T.F(b, []) in
  let c_ = T.F(c, []) in
  let d_ = T.F(d, []) in
  let e_ = T.F(e, []) in
  let faa = T.F(f, [a_;a_]) in
  let fab = T.F(f, [a_;b_]) in
  let fba = T.F(f, [b_;a_]) in
  let faaa = T.F(f, [a_;faa]) in
  let fabc = T.F(f, [a_;T.F(f, [b_;c_])]) in
  let fcab = T.F(f, [c_;T.F(f, [a_;b_])]) in
  let faby = T.F(f, [a_;T.F(f, [b_;y])]) in
  let fxy = T.F(f, [x;y]) in
  let fxx = T.F(f, [x;x]) in
  let fyy = T.F(f, [y;y]) in
  let fzz = T.F(f, [z;z]) in
  let fax = T.F(f, [a_;x]) in
  let gx = T.F(g, [x]) in
  let ga = T.F(g, [a_]) in
  let gb = T.F(g, [b_]) in
  let gu = T.F(g, [u]) in
  let fgax = T.F(f, [ga; x]) in
  let fgay = T.F(f, [ga; y]) in
  let gfaa = T.F(g,[faa]) in
  let gfax = T.F(g,[fax]) in
  let t2 = T.F(f, [T.F(h,[z;v]);T.F(h,[u;v]);w]) in
  let rec flist = function
    [s; t] -> T.F(f, [s; t])
    | s :: ts -> T.F(f, [s; flist ts])
    | _ -> failwith "Unexpected pattern"
  in
  let t_lc88_1 = flist [c_;c_;gu; x] in
  let t_lc88_2 = flist [b_;ga;y; z] in
  (* testing unification *)
  let run_unify (s, t) =
    let s = flatten s in
    let t = flatten t in
    unify s t
  in
  let print_subs (s, t) =
    let s = flatten s in
    let t = flatten t in
    let ss = T.to_string s in
    let ts = T.to_string t in
    let m = "Unify "^ss^" and "^ts^": " in
    match unify s t with
    | [] -> Format.printf "%s\n" (m ^ "none"); 0
    | us ->
      let m' = m ^ (string_of_int (List.length us)) ^ " substitutions:" in
      let app s u = let us = print_sub u in (s ^ "\n [" ^ us ^ "]") in
      let s = List.fold_left app m' us in
      Format.printf "%s\n%!" s;
      List.length us
  in
  let assert_some ts =
    assert(print_subs ts > 0) in
  let assert_more ts n =
    Format.printf "Count ...\n";
    assert (print_subs ts = n)
  in
  let assert_none ts = assert(run_unify ts == []) in
  assert_some (x,x);
  assert_some (x,y);
  assert_some (x,a_);
  assert_some (a_, y);
  assert_some (a_,a_);
  assert_none (ga,gb);
  assert_some (gx,ga);
  assert_some (faa, y);
  assert_some (gx,gfaa);
  assert_some (T.F(f, [T.F(g, [y]); y]), fax);
  assert_none (a_, gx);
  assert_none (x, gx);
  assert_some (y, gx);
  assert_none (faa, faaa);
  assert_some (fxy,t2);
  assert_some (fab, fba);
  assert_some (faaa, faaa);
  assert_some (fcab, fabc);
  assert_some (faa, fax);
  assert_some (gfaa, gfax);
  assert_some (faaa, fax);
  assert_some (fabc, fax);
  assert_some (faaa, fxy);
  assert_some (fabc, fxy);
  assert_some (faby, fxy);
  assert_some (T.F(f,[u; gfaa]), T.F(f, [gfax; y]));
  assert_none (fgax, fax);
  assert_some (fgay, fax);
  assert_none (fgay, faaa);
  assert_some (fgay, fgay);
  assert_some (T.F(f, [T.F(g,[faa]); u]), faby);
  (* some examples from christian/lincoln 88 *)
  assert_some (t_lc88_1,t_lc88_2);
  assert_some (flist [w;x;gx],flist [y;u;gu]);
  assert_more (flist [x;a_;b_],flist [u;c_;d_;e_]) 2;
  assert_more (flist [x;a_;b_],flist [u;c_;c_;d_]) 2;
  assert_more (flist [x;a_;b_],flist [u;c_;c_;c_]) 2;
  assert_more (flist [x;a_;b_],flist [u;y;c_;d_]) 12;
  assert_more (flist [x;a_;b_],flist [u;y;c_;c_]) 12;
  assert_more (flist [x;a_;b_],flist [u;y;z;c_]) 30;
  assert_more (flist [x;a_;b_],flist [u;y;z;v]) 56;
  assert_more (flist [x;a_;a_],flist [u;c_;d_;e_]) 2;
  assert_more (flist [x;a_;a_],flist [u;c_;c_;d_]) 2;
  assert_more (flist [x;a_;a_],flist [u;c_;c_;c_]) 2;
  assert_more (flist [x;a_;a_],flist [u;y;c_;d_]) 8;
  assert_more (flist [x;a_;a_],flist [u;y;v;c_]) 18;
  assert_more (flist [x;a_;a_],flist [u;y;z;v]) 32;
  assert_more (flist [x;y;a_],flist [u;c_;d_;e_]) 28;
  assert_more (flist [x;y;a_],flist [u;c_;c_;d_]) 20;
  assert_more (flist [x;y;a_],flist [u;v;c_;d_]) 88;
  assert_more (flist [x;y;a_],flist [u;v;z;c_]) 204;
  assert_more (flist [x;y;z],flist [u;v;c_;d_]) 336;
  assert_more (flist [x;y;z],flist [u;v;w;c_]) 870;
  (* examples with repeated variables *)
  assert_some (T.F(f,[x]), T.F(f,[y]));
  assert_some (fxy,fzz);
  assert_some (fxx,fyy);
  assert_some (flist [x;x;gx], flist[u;u;gu]);
  (* testing matching *)
  let run_matches (s,t) = match_term s t in
  let print_msubs (s,t) =
    let (s,n) =
      let ss = T.to_string s in
      let ts = T.to_string t in
      let m = "To match "^ss^" with "^ts^", " in
      match match_term s t with
      | [] -> ("none", 0)
      | us ->
        let m' = m ^ (string_of_int (List.length us)) ^ " substitutions\n" in
        let app s u = let us = print_sub u in (s ^ "\n or\n" ^ us) in
        let s = List.fold_left app m' us in
        (s, List.length us)
    in
    Format.printf "%s\n" s; n in
  let assert_msome ts =
    assert([] <> run_matches ts); ignore (print_msubs ts) in
  let assert_mnone ts = assert([] == (run_matches ts)) in
  assert_msome (x,x);
  assert_mnone (x,a_);
  assert_msome (a_, y);
  assert_msome (a_,a_);
  assert_mnone (gx,ga);
  assert_msome (faa, y);
  assert_msome (gfaa,gx);
  assert_mnone (a_, gx);
  assert_msome (gx, x); (* ! - but with renamed rules no problem *)
  assert_mnone (y, gx);
  assert_mnone (faa, faaa);
  assert_msome (fab, fba);
  assert_msome (fcab, fabc);
  assert_msome (faa, fax);
  assert_msome (gfaa, gfax);
  assert_msome (faaa, fax);
  assert_msome (fabc, fax);
  assert_msome (faaa, fxy);
  assert_msome (fabc, fxy);
  assert_msome (faby, fxy);
  assert_msome (T.F(f,[u; gfaa]), T.F(f, [gfax; y]));
  assert_msome (flist[ga;u;w], fxy);
  assert_mnone (fgay, fax);
  assert_mnone (fgay, faaa);
  assert_msome (fgay, fgay);
  assert_msome (flist [a_;ga;b_;x], flist[a_;y;ga;b_])
;;