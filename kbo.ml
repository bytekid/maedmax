(*** MODULES *****************************************************************)
module St = Statistics
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yices
open Yicesx
open Arith

(*** GLOBALS *****************************************************************)
(*let env = ref {sign=[]; w0=mk_num (mk_context ()) 0; wfs=[]}*)
(* settings for KBO *)
(*let flags = { af = ref false }*)

(* signature *)
let funs = ref []

(* map function symbol and strategy stage to variable for weight *)
let weights : (int * Signature.sym, Yices.var_decl * Yices.expr) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Signature.sym, Yices.var_decl * Yices.expr) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable expressing whether
   argument filtering for symbol is list *)
let af_is_list : (int * Signature.sym, Yices.expr) Hashtbl.t = Hashtbl.create 32
(* variable whether argument position for symbol is contained in filtering *)
let af_arg : ((int * Signature.sym) * int, Yices.var_decl * Yices.expr) Hashtbl.t 
 = Hashtbl.create 64

(*** FUNCTIONS ***************************************************************)
let name = Signature.get_fun_name

let w k f = snd (Hashtbl.find weights (k,f))

let prec k f = snd (Hashtbl.find precedence (k,f))

let adm_smt (ctx,k) =
  let p = prec k in
  let z, o = mk_num ctx 0, mk_num ctx 1 in
  let nat_f f = yand ctx (mk_ge ctx (w k f) z) (mk_ge ctx (p f) z) in
  let ensure_nat = ybig_and ctx [ nat_f f | f,_ <- !funs] in
  (* constants *)
  let cs = [ c | c,a <- !funs; a = 0 ] in
  let cadm = ybig_and ctx [ mk_ge ctx (w k c) o | c <- cs ] in (* w0 = 1 *)
  let us = [ f | f,a <- !funs; a = 1 ] in
  let f0 f = mk_eq ctx (w k f) z in
  let max f = ybig_and ctx [ mk_gt ctx (p f) (p g) | g,_<- !funs; g <> f ] in
  let uadm = ybig_and ctx [ yimp ctx (f0 f) (max f) | f <- us ] in
  ybig_and ctx [ensure_nat; cadm; uadm]
;;
    
let weight (ctx,k) t =
 let rec weight = function
  | V _ -> mk_num ctx 1 (* w0 = 1 *)
  | F(f,ss) -> ysum ctx ((w k f) :: [weight si | si <- ss ])
 in weight t
;;

let rec remove_equals ss tt =
  match ss,tt with
  | [], [] -> [],[]
  | s::sss, t::ttt -> 
     if s <> t then ss,tt else remove_equals sss ttt
  | _ -> failwith "remove_equals: different lengths"
;;


let rec ykbo_gt (ctx,k) s t =
 if (s = t || not (Rule.is_non_duplicating (s,t))) then mk_false ctx 
 else 
  let ws, wt = weight (ctx,k) s, weight (ctx,k) t in
  let cmp = 
   match s,t with
    | V _,_ -> mk_false ctx
    | F(f,ss), V _ -> mk_true ctx (* var condition already checked *)
    | F(f,ss), F(g,ts) when f = g ->
     (match remove_equals ss ts with
      | si :: _, ti :: _ -> ykbo_gt (ctx,k) si ti
      | _ -> failwith "ykbo: different lengths")
    | F(f,ss), F(g,ts) -> mk_gt ctx (prec k f) (prec k g) 
   in
   yor ctx (mk_gt ctx ws wt) (yand ctx (mk_eq ctx ws wt) cmp)
;;

let ykbo_ge (ctx,k) s t = if s = t then mk_true ctx else ykbo_gt (ctx,k) s t

let init_kbo (ctx,k) fs =
  let add (f,_) =
   let s = (name f) ^ (string_of_int k) in
   let ty  = mk_type ctx "int" in
   let dp = mk_var_decl ctx (s^"p") ty in
   let dw = mk_var_decl ctx s ty in
   let xp = mk_var_from_decl ctx dp in
   let xw = mk_var_from_decl ctx dw in
   Hashtbl.add precedence (k,f) (dp,xp);
   Hashtbl.add weights (k,f) (dw,xw)
  in List.iter add fs;
  funs := fs;
  adm_smt (ctx,k)
;;

let init c = init_kbo c

(*
let make_kbo_constr ctx ce =
 let _,w0,wfs = get_env () in
 let w = (wfs,w0) in
 let f ctx s t = ykbo ctx w s t in
 C.assert_with ctx f ce

let make_constr ctx = St.take_time St.t_ord (make_kbo_constr ctx)
*)

let decode m k = () 
