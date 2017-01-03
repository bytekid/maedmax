(*** MODULES *****************************************************************)
module C = Cache
module F = Format
module St = Statistics
module Sig = Signature

(*** OPENS *******************************************************************)
open Term
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
let precedence : (int * Sig.sym, Yicesx.t) Hashtbl.t = Hashtbl.create 32
(* map function symbol and strategy stage to variable expressing whether
   argument filtering for symbol is list *)
let af_is_list : (int * Sig.sym, Yicesx.t) Hashtbl.t = Hashtbl.create 32
(* variable whether argument position for symbol is contained in filtering *)
let af_arg : ((int * Sig.sym) * int, Yicesx.t) Hashtbl.t = Hashtbl.create 64

(* cache results of comparison *)
let gt_encodings : (int * Rule.t, Yicesx.t) Hashtbl.t = Hashtbl.create 512
let ge_encodings : (int * Rule.t, Yicesx.t) Hashtbl.t = Hashtbl.create 512
let eq_encodings : (int * Rule.t, Yicesx.t) Hashtbl.t = Hashtbl.create 512

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
;;

let emb_gt s t = s <> t && emb_geq s t

(* lpo for yices *)

let prec i f = 
 try Hashtbl.find precedence (i,f) with
 Not_found -> failwith ("Lpo.prec: unknown symbol "^(Sig.get_fun_name f))
;;

let gt (ctx,i) s t =
  let p = prec i in
  let rec ylpo_gt s t =
    let helper (i,(s,t)) =
      if emb_gt s t then mk_true ctx
      else if not (Rule.is_rule (s,t)) || emb_geq t s then mk_false ctx
      else match s, t with
	      | F(f,ss), F(g,ts) ->
          let sub = big_or ctx [ ylpo_ge si t | si <- ss ] in
          if f = g then
            big_and1 (ylex ss ts :: [ ylpo_gt s ti | ti <- ts ]) <|> sub
          else
            big_and1 ((p f <>> (p g)) :: [ ylpo_gt s ti | ti <- ts ]) <|> sub
        | _ -> mk_false ctx (* variable case already covered *)
    in cache gt_encodings helper (i,(s,t))
  and ylpo_ge s t = if s = t then mk_true ctx else ylpo_gt s t
  and ylex l1 l2 = match l1, l2 with
    | s :: ss, t :: ts when s = t -> ylex ss ts
    | s :: ss, t :: ts -> ylpo_gt s t
    | [], [] -> mk_false ctx
    | _ -> mk_true ctx
  in ylpo_gt s t
;;

let ge (ctx,i) s t = if s = t then mk_true ctx else gt (ctx,i) s t

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

let af_n (ctx,k) f = !! (af_l (ctx,k) f)

let exists (ctx,k) f ts p =
 big_or ctx [ af_p (ctx,k) f i <&> (p ti) | i,ti <- index ts ]
;;

let forall (ctx,k) f ts p =
 big_and ctx [ af_p (ctx,k) f i <=>> (p ti) | i,ti <- index ts ]
;;

let exists2 (ctx,k) f ss ts p =
 let ps = index (List.map2 (fun a b -> a,b) ss ts) in
 big_or ctx [ af_p (ctx,k) f i <&> (p si ti) | i,(si,ti) <- ps ]
;;

let forall2 (ctx,k) f ss ts p =
 let ps = index (List.map2 (fun a b -> a,b) ss ts) in
 big_and ctx [ af_p (ctx,k) f i <=>> (p si ti) | i,(si,ti) <- ps ]
;;

let ylpo_af is_gt ((ctx,k) as c) s t =
  let af_p,af_l,af_n,prec = af_p (ctx,k), af_l (ctx,k), af_n (ctx,k), prec k in
  let rec gt s t =
    let helper (k, (s,t)) =
      match s with
        | V _-> mk_false ctx
        | F(f, ss) -> match t with
          | V x -> (exists c f ss (fun si -> gt si t)) <|>
                   (af_l f <&> (exists c f ss (fun si -> eq si t)))
          | F(g, ts) when f = g ->
            let a = big_and1 [af_l f;lex_gt f (ss,ts); forall c f ts (gt s)] in
            let b = af_l f <&> (exists c f ss (fun si -> eq si t)) in
            let c = af_n f <&> (exists2 c f ss ts gt) in
            big_or1 [a; b; c]
          | F(g, ts) ->
            let pgt = [prec f <>> (prec g); af_l f; af_l g] in
            let a = (af_n g <|> (big_and1 pgt)) <&> (forall c g ts (gt s)) in
            let b = af_n f <&> (exists c f ss (fun si -> gt si t)) in
            let c = af_l f <&> (exists c f ss (fun si -> eq si t)) in
            big_or1 [a; b; c]
    in cache gt_encodings helper (k,(s,t))
  and ge s t = 
    let helper (k,(s,t)) = (eq s t) <|> (gt s t) in
    cache ge_encodings helper (k,(s,t))
  and eq s t =
    let helper (k,(s,t)) =
      match s,t with
        | V _, _ when s = t -> mk_true ctx
        | V _, V _ -> mk_false ctx
        | V _, F(g,ts) -> af_n g <&> (exists c g ts (fun tj -> eq s tj))
        | F (f,ss), V _ -> af_n f <&> (exists c f ss (fun si -> eq si t))
        | F (f, ss), F (g, ts) when f=g -> forall2 c f ss ts eq
        | F (f, ss), F (g, ts) -> ((af_n g) <&> (exists c g ts (eq s))) <|>
                               (af_n f <&> (exists c f ss (fun si -> eq si t))) 
    in cache eq_encodings helper (k,(s,t))
  and lex_gt ?(i = 0) f = function
    | s :: ss, t :: ts -> ((af_p f i) <&> (gt s t)) <|>
               (((!! (af_p f i)) <|> (eq s t)) <&> (lex_gt ~i:(i+1) f (ss,ts)))
    | [], [] -> mk_false ctx
    | _ -> failwith "different lengths in lex"
  in if is_gt then gt s t else ge s t
;;

let gt_af = ylpo_af true

let ge_af (ctx,k) s t = ylpo_af false (ctx,k) s t

(* * OVERALL ENCODING * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

let make_fun_vars ctx k fs =
 let add f =
   let fn = Sig.get_fun_name f in
   Format.printf "init %s %d\n" fn k;
   Hashtbl.add precedence (k,f) (mk_int_var ctx (fn^"-"^(string_of_int k)))
 in List.iter add fs
;;

let init (ctx,k) fs =
  funs := fs;
  let fs' = List.map fst fs in
  make_fun_vars ctx k fs';
  let bnd_0 = mk_zero ctx in
  let bnd_n = mk_num ctx (List.length fs') in
  let bounds f = let p = prec k f in (p <>=> bnd_0) <&> (bnd_n <>=> p) in
  big_and ctx [ bounds f | f <- fs' ]
;;

let init_af (ctx,k) fs =
 let c = init (ctx,k) fs in
 let af (f,a) =
  let p = af_p (ctx,k) f in
  let is = Listx.interval 0 (a-1) in 
  let only i = big_and1 (p i :: [ !! (p j) | j <- is; j <> i ]) in
  big_or1 (af_l (ctx,k) f :: [ only i | i <- is ])
 in big_and1 (c :: [af f | f <- fs ])
;;

let init ctx = (if !(flags.af) then init_af else init) ctx

let decode_prec k m fs =
 F.printf "precedence: @\n ";
 let rec group = function
   [] -> " "
 | [f] -> (Sig.get_fun_name f)^" "
 | f :: fs ->  (Sig.get_fun_name f)^", "^(group fs)
 in
 let rec pp = function
   [] -> F.printf "empty \n"
 | [(i,g)] -> F.printf " %s\n" (group g)
 | (i,g) :: gs ->  F.printf " %s >" (group g); pp gs
 in 
 let add (k',f) v fv = if k = k' then (f,v) :: fv else fv in
 let fv = Hashtbl.fold add precedence [] in
 let has_val x = try let _ = eval_int_var m x in true with _ -> false in
 let prec = [f, eval_int_var m x | (f,x) <- fv; has_val x ] in
 let fs' = [ f | f <- fs; List.mem_assoc f prec ] in
 let pg = Listx.group_by (fun x -> List.assoc x prec) fs' in
 let pg = List.sort ( fun (a,_) (b,_) -> Pervasives.compare b a) pg in
 pp pg
;;

let decode_af k m =
 let dps = [ rl | rl,v <- C.get_all_strict 1; eval m v ] in
 let rls = [ rl | rl,v <- C.get_all_strict 0; eval m v ] in
 let fs = Rules.functions (dps @ rls) in
 decode_prec k m fs;
 let dec (f,a) =
  try
  F.printf " pi(%s)=" (Signature.get_fun_name f); 
  let af_p f i = Hashtbl.find af_arg ((k,f),i) in
  let args = [ i | i <- Listx.interval 0 (a-1); eval m (af_p f i) ] in
  if eval m (Hashtbl.find af_is_list (k,f)) then (
   F.printf "["; Listx.print (fun fmt -> F.fprintf fmt "%i") ", " args;
   F.printf "]")
  else Listx.print (fun fmt -> F.fprintf fmt "%i") ", " args;
  F.printf "@\n"
  with Not_found -> failwith "decode_af: Not_found"
 in
 F.printf "argument filtering: @\n"; 
 List.iter dec [ (f,a) | (f,a) <- !funs; List.mem f fs]
;;

let decode k m = 
 let fs = Rules.functions [ rl | rl,_ <- C.get_all_strict 0] in
 decode_prec k m fs
;;

let cond_gt i ctx conds s t =
  let p = prec i in
  let rec gt s t =
    if List.mem (s,t) conds || (emb_gt s t) then mk_true ctx
    else if emb_geq t s then mk_false ctx
    else match s, t with
	    | F(f,ss), F(g,ts) ->
        let sub = big_or ctx [ ylpo_ge si t | si <- ss ] in
        if f = g then
          big_and1 (ylex ss ts :: [ gt s ti | ti <- ts ]) <|> sub
        else
          big_and1 ((p f <>> (p g)) :: [ gt s ti | ti <- ts ]) <|> sub
      | _, F(g,ts) -> big_and ctx ([p f <>> (p g) | f,_ <- !funs; f <> g ] @
                                   (List.map (gt s) ts)) (* special hack *)
        | _ -> mk_false ctx (* variable case already covered *)
  and ylpo_ge s t = if s = t then mk_true ctx else gt s t
  and ylex l1 l2 = match l1, l2 with
    | s :: ss, t :: ts when s = t -> ylex ss ts
    | s :: ss, t :: ts -> gt s t
    | [], [] -> mk_false ctx
    | _ -> mk_true ctx
  in gt s t
;;

let clear () =
 Hashtbl.clear precedence; 
 Hashtbl.clear af_is_list; 
 Hashtbl.clear af_arg; 
 Hashtbl.clear gt_encodings; 
 Hashtbl.clear ge_encodings; 
 Hashtbl.clear eq_encodings
;;

