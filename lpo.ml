(*** MODULES *****************************************************************)
module St = Statistics
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yices
open Yicesx
open Arith

(*** TYPES *******************************************************************)
type flags = {
 af : bool ref 
}

(*** GLOBALS *****************************************************************)
(* settings for LPO *)
let flags = { af = ref false }
(* signature *)
let funs = ref []
(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Signature.sym, Yices.var_decl * Yices.expr) Hashtbl.t 
 = Hashtbl.create 32
(* map function symbol and strategy stage to variable expressing whether
   argument filtering for symbol is list *)
let af_is_list : (int * Signature.sym, Yices.expr) Hashtbl.t = Hashtbl.create 32
(* variable whether argument position for symbol is contained in filtering *)
let af_arg : ((int * Signature.sym) * int, Yices.expr) Hashtbl.t = Hashtbl.create 64

(* cache results of comparison *)
let gt_encodings : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 512
let ge_encodings : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 512
let eq_encodings : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 512

(*** FUNCTIONS ***************************************************************)
let set_af _ = flags.af := true

let (<.>) f g x = f (g x)

let cache ht f k =
 try Hashtbl.find ht k with Not_found -> 
 let v = f k in Hashtbl.add ht k v; v
;;


let rec emb_geq s t = 
  match s, t with 
  | V x, V y when x = y -> true
  | F (f, ss), (F (g, ts) as t) when f = g ->
      List.exists (fun si -> emb_geq si t) ss || 
      List.for_all2 (fun si ti -> emb_geq si ti) ss ts
  | F (f, ss), t -> 
      List.exists (fun si -> emb_geq si t) ss
  | _ -> false

let emb_gt s t = s <> t && emb_geq s t

(* lpo for yices *)

let prec f = 
 try snd (Hashtbl.find precedence f) with
 Not_found -> failwith ("prec: for ("^(Signature.get_fun_name (snd f))^"="^(string_of_int (snd f))^", "^(string_of_int (fst f))^") not found")
;;

let rec ylpo_gt ((ctx,i) as c) s t =
 let helper (i,(s,t)) = 
  (* optimization *)
  if emb_gt s t then ytrue ctx else
  if not (Listset.subset (variables t) (Term.variables s)) || 
     emb_geq t s then yfalse ctx else 
  match s with
  | V _-> yfalse ctx
  | F (f, ss)  ->
      let y = 
        match t with
	| V x -> if List.mem x (variables s) then ytrue ctx else yfalse ctx
	| F (g, ts) when f = g ->
            ybig_and ctx (ylex c ss ts :: [ ylpo_gt c s ti | ti <- ts ])
	| F (g, ts) ->
            ybig_and ctx (mk_gt ctx (prec (i,f)) (prec (i,g)) :: 
				       [ ylpo_gt c s ti | ti <- ts ])
      in
      ybig_or ctx (y :: [ ylpo_ge c si t | si <- ss ])
  in cache gt_encodings helper (i,(s,t))
and ylpo_ge ((ctx,k) as c) s t = if s = t then ytrue ctx else ylpo_gt c s t
and ylex ((ctx,i) as c) l1 l2 =
  match l1, l2 with
  | s :: ss, t :: ts when s = t -> ylex c ss ts
  | s :: ss, t :: ts -> ylpo_gt c s t
  | [], [] -> yfalse ctx
  | _ -> ytrue ctx

(* * ENCODING WITH ARGUMENT FILTERS * * * * * * * * * * * * * * * * * * * * * *)

let index = Listx.index

(* argument filtering for f is list *)
let af_l (ctx,k) f =
 try Hashtbl.find af_is_list (k,f) 
 with Not_found ->
  let x = mk_fresh_bool_var ctx in Hashtbl.add af_is_list (k,f) x; x
;;

(* variable returned by [af_p c f i] determines whether argument 
   filtering for [f] includes position [i] *)
let af_p (ctx,k) f i =
 try Hashtbl.find af_arg ((k,f),i)
 with Not_found ->
  let x = mk_fresh_bool_var ctx in Hashtbl.add af_arg ((k,f),i) x; x
;;

let af_n (ctx,k) f = ynot ctx (af_l (ctx,k) f)

let exists (ctx,k) f ts p =
 ybig_or ctx [ yand ctx (af_p (ctx,k) f i) (p ti) | i,ti <- index ts ]
;;

let forall (ctx,k) f ts p =
 ybig_and ctx [ yimp ctx (af_p (ctx,k) f i) (p ti) | i,ti <- index ts ]
;;

let exists2 (ctx,k) f ss ts p =
 let ps = index (List.map2 (fun a b -> a,b) ss ts) in
 ybig_or ctx [ yand ctx (af_p (ctx,k) f i) (p si ti) | i,(si,ti) <- ps ]
;;

let forall2 (ctx,k) f ss ts p =
 let ps = index (List.map2 (fun a b -> a,b) ss ts) in
 ybig_and ctx [ yimp ctx (af_p (ctx,k) f i) (p si ti) | i,(si,ti) <- ps ]
;;

let ylpo_af is_gt ((ctx,k) as c) s t =
(* Format.printf "rule: %a %i\n%!" Rule.print (s,t) k;*)
 let af_p, af_l, af_n = af_p (ctx,k), af_l (ctx,k), af_n (ctx,k) in
 let rec gt s t =
  let helper (k,(s,t)) =
   match s with
   | V _-> yfalse ctx
   | F (f, ss)  ->
    match t with
    | V x -> yor ctx (exists c f ss (fun si -> gt si t))
                     (yand ctx (af_l f) (exists c f ss (fun si -> eq si t)))
    | F (g, ts) when f = g ->
     let a = ybig_and ctx [af_l f; lex_gt f (ss,ts); forall c f ts (gt s)] in
     let b = yand ctx (af_l f) (exists c f ss (fun si -> eq si t)) in
     let c = yand ctx (af_n f) (exists2 c f ss ts gt) in
     ybig_or ctx [a; b; c]
    | F (g, ts) ->
     let pgt = [mk_gt ctx (prec (k,f)) (prec (k,g)); af_l f; af_l g] in
     let a = yand ctx (yor ctx (af_n g) (ybig_and ctx pgt)) (forall c g ts (gt s)) in
     let b = yand ctx (af_n f) (exists c f ss (fun si -> gt si t)) in
     let c = yand ctx (af_l f) (exists c f ss (fun si -> eq si t)) in
     ybig_or ctx [a; b; c]
    in cache gt_encodings helper (k,(s,t))
 and ge s t = 
  let helper (k,(s,t)) = yor ctx (eq s t) (gt s t) in
  cache ge_encodings helper (k,(s,t))
 and eq s t =
  let helper (k,(s,t)) =
   match s,t with
   | V _, _ when s = t -> ytrue ctx
   | V _, V _ -> yfalse ctx
   | V _, F(g,ts) -> yand ctx (af_n g) (exists c g ts (fun tj -> eq s tj))
   | F (f,ss), V _ -> yand ctx (af_n f) (exists c f ss (fun si -> eq si t))
   | F (f, ss), F (g, ts) when f=g -> forall2 c f ss ts eq
   | F (f, ss), F (g, ts) -> 
    yor ctx (yand ctx (af_n f) (exists c f ss (fun si -> eq si t)))
            (yand ctx (af_n g) (exists c g ts (fun tj -> eq s tj)))
  in cache eq_encodings helper (k,(s,t))
 and lex_gt ?(i = 0) f = function
  | s :: ss, t :: ts -> yor ctx (yand ctx (af_p f i) (gt s t))
   (yand ctx (yor ctx (ynot ctx (af_p f i)) (eq s t)) (lex_gt ~i:(i+1) f (ss,ts)))
  | [], [] -> yfalse ctx
  | _ -> failwith "different lengths in lex"
 in
 if is_gt then gt s t else ge s t
;;

let ylpo_af_gt = ylpo_af true

let ylpo_af_ge (ctx,k) s t = ylpo_af false (ctx,k) s t

(* * OVERALL ENCODING * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

let make_fun_vars ctx k fs =
 let ty  = mk_type ctx "int" in
 let add f =
  let fn = Signature.get_fun_name f in
  let s = fn^"-"^(string_of_int k) in
  let d = mk_var_decl ctx (s^"l") ty in 
  let v = mk_var_from_decl ctx d in
  Hashtbl.add precedence (k,f) (d,v)
 in List.iter add fs
;;

let init (ctx,k) fs =
(*  Format.printf "init LPO for %i\n" k;*)
  funs := fs;
  let fs' = List.map fst fs in
  make_fun_vars ctx k fs';
  let bnd_0 = mk_num ctx 0 in
  let bnd_n = mk_num ctx (List.length fs') in
  let bnds f =
    let x = prec (k,f) in
    yand ctx (mk_ge ctx x bnd_0) (mk_ge ctx bnd_n x)
  in ybig_and ctx [ bnds f | f <- fs' ]
;;

let init_af (ctx,k) fs =
 let c = init (ctx,k) fs in
 let af (f,a) =
  let p = af_p (ctx,k) f in
  let is = Listx.interval 0 (a-1) in 
  let only i = ybig_and ctx (p i :: [ ynot ctx (p j) | j <- is; j <> i ]) in
  ybig_or ctx (af_l (ctx,k) f :: [ only i | i <- is ])
 in
 ybig_and ctx (c :: [af f | f <- fs ])
;;

let init ctx = (if !(flags.af) then init_af else init) ctx

let decode_prec k m fs =
 Format.printf "precedence: @\n ";
 let rec group = function
   [] -> " "
 | [f] -> (Signature.get_fun_name f)^" "
 | f :: fs ->  (Signature.get_fun_name f)^", "^(group fs)
 in
 let rec pp = function
   [] -> Format.printf "empty \n"
 | [(i,g)] -> Format.printf " %s\n" (group g)
 | (i,g) :: gs ->  Format.printf " %s >" (group g); pp gs
 in 
 let add (k',f) (d,v) fv = if (k = k') then (f,(d,v)):: fv else fv in
 let fv = Hashtbl.fold add precedence [] in
 let has_val d = try let _ = get_int_value m d in true with _ -> false in
 let dec_var d = Int32.to_int (get_int_value m d) in
 let prec = [f, d | (f,(d,_)) <- fv; has_val d] in
 let prec = [f, dec_var d | f,d <- prec] in
 let fs' = [ f | f <- fs; List.mem_assoc f prec ] in
 let pg = Listx.group_by (fun x -> List.assoc x prec) fs' in
 let pg = List.sort ( fun (a,_) (b,_) -> compare b a) pg in
 pp pg
;;

let decode_af k m =
 let dps = [ rl | rl,v <- C.get_all_strict 1; evaluate_in_model m v == True ] in
 let rls = [ rl | rl,v <- C.get_all_strict 0; evaluate_in_model m v == True] in
 let fs = Rules.functions (dps @ rls) in
 decode_prec k m fs; 
 let eval x = evaluate_in_model m x == True in
 let dec (f,a) =
  try
  Format.printf " pi(%s)=" (Signature.get_fun_name f); 
  let af_p f i = Hashtbl.find af_arg ((k,f),i) in
  let args = [ i | i <- Listx.interval 0 (a-1); eval (af_p f i) ] in
  if eval (Hashtbl.find af_is_list (k,f)) then (
   Format.printf "["; Listx.print (fun fmt -> Format.fprintf fmt "%i") ", " args;
   Format.printf "]")
  else Listx.print (fun fmt -> Format.fprintf fmt "%i") ", " args;
  Format.printf "@\n"
  with Not_found -> failwith "decode_af: Not_found"
 in
 Format.printf "argument filtering: @\n"; 
 List.iter dec [ (f,a) | (f,a) <- !funs; List.mem f fs]
;;

let decode k m = 
 let fs = Rules.functions [ rl | rl,_ <- C.get_all_strict 0] in
 decode_prec k m fs
;;

let clear () =
 Hashtbl.clear precedence; 
 Hashtbl.clear af_is_list; 
 Hashtbl.clear af_arg; 
 Hashtbl.clear gt_encodings; 
 Hashtbl.clear ge_encodings; 
 Hashtbl.clear eq_encodings
;;

