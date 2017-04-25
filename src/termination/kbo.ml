(*** MODULES *****************************************************************)
module L = List
module T = Term
module St = Statistics
module C = Cache
module Sig = Signature

(*** OPENS *******************************************************************)
open Term
open Yicesx
open Arith

(*** GLOBALS *****************************************************************)
(*let env = ref {sign=[]; w0=mk_num (mk_context ()) 0; wfs=[]}*)
(* settings for KBO *)
(*let flags = { af = ref false }*)

(* signature *)
let funs = ref []

(* map function symbol and strategy stage to variable for weight *)
let weights : (int * Sig.sym, Yicesx.t) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Sig.sym, Yicesx.t) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable expressing whether
   argument filtering for symbol is list *)
let af_is_list : (int * Sig.sym, Yicesx.t) Hashtbl.t = Hashtbl.create 32
(* variable whether argument position for symbol is contained in filtering *)
let af_arg : ((int * Sig.sym) * int, Yicesx.t) Hashtbl.t = Hashtbl.create 64

(*** FUNCTIONS ***************************************************************)
let name = Sig.get_fun_name

let w k f = Hashtbl.find weights (k,f)

let prec k f = Hashtbl.find precedence (k,f)

let adm_smt (ctx,k) =
  let p = prec k in
  let zero, one = mk_zero ctx, mk_one ctx in
  let nat_f f = (w k f <>=> zero) <&> (p f <>=> zero) in
  let ensure_nat = big_and ctx [ nat_f f | f,_ <- !funs] in
  (* constants *)
  let cadm = big_and ctx [ w k c <>=> one | c,a <- !funs; a=0 ] in (* w0 = 1 *)
  (* unary symbols *)
  let f0 f = w k f <=> zero in
  let max f = big_and ctx [ p f <>> (p g) | g,_<- !funs; g <> f ] in
  let uadm = big_and ctx [ f0 f <=>> (max f) | f,a <- !funs; a = 1 ] in
  (* total *)
  let ps = [ f,g | f,_ <- !funs; g,_ <- !funs; f <> g ] in
  let total_prec = big_and ctx [ !! (p f <=> (p g)) | f, g <- ps ] in
  big_and1 [ensure_nat; cadm; uadm; total_prec]
;;
    
let weight (ctx,k) t =
 let rec weight = function
  | V _ -> mk_one ctx (* w0 = 1 *)
  | F(f,ss) -> sum1 ((w k f) :: [weight si | si <- ss ])
 in weight t
;;

let rec remove_equals ss tt =
  match ss,tt with
  | [], [] -> [],[]
  | s::sss, t::ttt -> 
     if s <> t then ss,tt else remove_equals sss ttt
  | _ -> failwith "remove_equals: different lengths"
;;


let rec gt (ctx,k) s t =
 if (s = t || not (Rule.is_non_duplicating (s,t))) then mk_false ctx 
 else 
  let ws, wt = weight (ctx,k) s, weight (ctx,k) t in
  let cmp = 
   match s,t with
    | V _,_ -> mk_false ctx
    | F(f,ss), V _ -> mk_true ctx (* var condition already checked *)
    | F(f,ss), F(g,ts) when f = g ->
     (match remove_equals ss ts with
      | si :: _, ti :: _ -> gt (ctx,k) si ti
      | _ -> failwith "ykbo: different lengths")
    | F(f,ss), F(g,ts) -> (prec k f) <>> (prec k g) 
   in
   ws <>> wt <|> ((ws <=> wt) <&> cmp)
;;

let ge (ctx,k) s t = if s = t then mk_true ctx else gt (ctx,k) s t

let init_kbo (ctx,k) fs =
  let add (f,_) =
   let s = "kbo" ^ (name f) ^ (string_of_int k) in
   Hashtbl.add precedence (k,f) (mk_int_var ctx (s^"p"));
   Hashtbl.add weights (k,f) (mk_int_var ctx s)
  in List.iter add fs;
  funs := fs;
  adm_smt (ctx,k)
;;

let init c = init_kbo c



let cond_gt k ctx conds s t =
 let rec gt s t =
   if List.mem (s,t) conds then mk_true ctx
   else if (s = t || not (Rule.is_non_duplicating (s,t))) then mk_false ctx 
   else 
     let ws, wt = weight (ctx,k) s, weight (ctx,k) t in
     let cmp = 
       match s,t with
         | V _,_ -> mk_false ctx
         | F(f,ss), V _ -> mk_true ctx (* var condition already checked *)
         | F(f,ss), F(g,ts) when f = g ->
           (match remove_equals ss ts with
             | si :: _, ti :: _ -> gt si ti
             | _ -> failwith "ykbo: different lengths")
         | F(f,ss), F(g,ts) -> (prec k f) <>> (prec k g) 
     in ws <>> wt <|> ((ws <=> wt) <&> cmp)
  in big_or1 (gt s t :: [ gt u t | (s',u) <- conds; s' = s ])
;;


let eval_table k m h =
 let add (k',f) x p =
   if k <> k' then p
   else (
     try
       let v = eval_int_var m x in
       Hashtbl.add p f v; p
     with _ -> p)
 in Hashtbl.fold add h (Hashtbl.create 16)
;;

let decode_term_gt k m =
 let w = Hashtbl.find (eval_table k m weights) in
 let rec weight = function
  | T.V _ -> 1 (* w0 = 1 *)
  | T.F (f, ts) -> List.fold_left (fun s ti -> s + (weight ti)) (w f) ts
 in
 let prec = Hashtbl.find (eval_table k m precedence) in
 let rec gt s t =
  if Term.is_subterm s t || not (Rule.is_non_duplicating (s,t)) then false
  else if Term.is_subterm t s then true
  else (
   let ws, wt = weight s, weight t in
   let cmp = match s,t with
    | T.V _, _
    | _, T.V _  -> false (* no subterm *)
    | T.F(f,ss), T.F(g,ts) ->
      let lex (gt_lex,ge) (si,ti) = gt_lex || (ge && gt si ti), ge && si=ti in
      if f <> g then prec f > prec g
      else fst (L.fold_left lex (false, true) (List.combine ss ts))
   in ws > wt || (ws = wt && cmp))
  in gt
;;

let eval k m =
  let name = Signature.get_fun_name in
  let prec f = try Hashtbl.find (eval_table k m precedence) f with _ -> 42 in
  let w f = try Hashtbl.find (eval_table k m weights) f with _ -> 42 in
  List.sort (fun (_, p, _) (_,q, _) -> p - q) [ f, prec f, w f | f,_ <- !funs ]
;;


let print fpw = 
  Format.printf "KBO: \n %!";
  let name = Signature.get_fun_name in
  List.iter (fun (f,i,_) -> Format.printf "< %s:%d %!" (name f) i) fpw;
  Format.printf "\n%!";
  List.iter (fun (f,_,w) -> Format.printf "w(%s) = %d " (name f) w) fpw;
  Format.printf "\n%!"
;;


let decode_print k m = print (eval k m)

let decode k m =
  let gt = decode_term_gt k m in
  let cmp c d = if gt (Term.F(c,[])) (Term.F(d,[])) then d else c in
  let bot =  match [ c | c,a <- !funs; a = 0] with
      [] -> None
    | c :: cs -> Some (List.fold_left cmp c cs)
  in
  let fpw = eval k m in
  object
    method bot = bot;;
    method gt = gt;;
    method print = fun _ -> print fpw 
  end
;;
