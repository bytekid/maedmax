open Yices
open Format
open Rules
open Arith
open Lpo
open Kbo

let maximality c a_gt trss =
  let f trs = disj c [ v | rule, v <- a_gt; not (List.mem rule trs) ] in
  conj c [ f trs | trs <- trss ]

let maximal_terminating_trs ~order rules trss = 
  let c = mk_context () in
  let a_gt = order c rules in
  assert_simple c (maximality c a_gt trss);
  let a_rules = 
    [ rule, assert_weighted c v 1L | rule, v <- a_gt ] in
  let result =
    match max_sat c with
    | True -> let m = get_model c in
	      Some [ rule | rule, v <- a_rules; get_assertion_value m v = true ]
    | _ -> None in
  del_context c;
  result

let rec max_aux ~order n rules trss =
  if n = 0 then trss else
    match maximal_terminating_trs ~order rules trss with
    | None -> trss
    | Some trs -> max_aux ~order (n - 1) rules (trs :: trss)

let max ~order n es = 
  max_aux ~order n (Variant.unique ~eq:Rule.variant (Rules.rules_over es)) []

let rpo gt c rules =
  let fs = Rules.functions rules in
  let ty  = mk_type c "int" in
  let a = [ f, mk_var_from_decl c (mk_var_decl c f ty) | f <- fs ] in
  let bnd_0 = mk_num c 0 in
  let bnd_n = mk_num c (List.length fs) in
  let f (_, x) =
    assert_simple c (mk_ge c x bnd_0);
    assert_simple c (mk_ge c bnd_n x) in 
  List.iter f a;
  [ (s, t), gt c a s t | s, t <- rules ]
						
let lpo = rpo ylpo

let mpo = rpo yrpo

let kbo ctx rls = 
  let ty  = mk_type ctx "int" in
  let fs = Rules.signature rls in 
  let vars = 
    [ f, a , mk_var_decl ctx f ty, mk_var_decl ctx (f^"p") ty | f,a <- fs ] in
  let wfs_a = 
    [ f, mk_var_from_decl ctx w, mk_var_from_decl ctx p, a | f,a,w,p <- vars ] in
  let wfs = [ w, p, f | f,w,p,a <- wfs_a ] in
  let wcs = [ w, p, f | f,w,p,a <- wfs_a; a = 0 ] in
  let w1s = [ w, p, f | f,w,p,a <- wfs_a; a = 1 ] in
  let var_w0 = mk_var_decl ctx "w0" ty in
  let w0 =  mk_var_from_decl ctx var_w0 in 
  assert_simple ctx (adm_smt ctx (wfs,wcs,w1s,w0));
  [ (s,t), ykbo ctx (wfs,w0) s t | s,t <- rls ] 
