(*** MODULES *****************************************************************)
module St = Statistics
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yicesx
open Arith

(*** TYPES *****************************************************************)
type poly = Yicesx.t * (Signature.var * Yicesx.t) list

(*** GLOBALS *****************************************************************)
(* signature *)
let funs = ref []

(* weight status, a boolean for each function symbol *)
let status : (int * Signature.sym, Yicesx.t) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable for weight *)
let weights : (int * Signature.sym, Yicesx.t) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Signature.sym, Yicesx.t) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol, strategy stage and argument position to coefficient *)
let scs : (int * Signature.sym * int, Yicesx.t) Hashtbl.t
 = Hashtbl.create 32

let w0_var = ref None

(* cache results of comparison *)
let gt_encodings : (int * Rule.t, Yicesx.t) Hashtbl.t = Hashtbl.create 512
let w_encodings : (int * Term.t, poly list) Hashtbl.t = Hashtbl.create 512

(*** FUNCTIONS ***************************************************************)
let cache ht f k =
 try Hashtbl.find ht k with Not_found ->
 let v = f k in Hashtbl.add ht k v; v
;;


let index = Listx.index

let w0 _ = match !w0_var with None -> failwith "MPol: no w0" | Some w0 -> w0

let name = Signature.get_fun_name

let w k f = 
 try Hashtbl.find weights (k,f)
 with Not_found -> failwith "MPol.w: Not_found"

let prec k f = 
 try Hashtbl.find precedence (k,f)
 with Not_found -> failwith "MPol.prec: Not_found"

let sc k f i = 
 try Hashtbl.find scs (k,f,i)
 with Not_found -> failwith "MPol.sc: Not_found"

(* true if status is pol *)
let stat k f = 
 try Hashtbl.find status (k,f) 
 with Not_found -> failwith "MPol.stat: Not_found"

let assoc ctx x xs = try List.assoc x xs with Not_found -> mk_num ctx 0

(* ENCODINGS: SIDE CONDITIONS *)
let wmin (ctx,k) =
 let zero = mk_zero ctx in
 let nat = big_and ctx [w k c <>=> zero | c,a <- !funs] in
 let w0n = (w0 ()) <>=> zero in
 big_and1 (w0n :: nat :: [(w k c) <>=> (w0 ()) | c,a <- !funs; a = 0 ])
;;

(* subterm coefficients must be nonzero for functions with polynomial status *)
let coeff (ctx,k) =
 let coeff f a i = 
  let c = sc k f i in
  [(mk_num ctx 2) <>=> c; c <>=> (mk_num ctx 0); 
   (stat k f) <=>> (c <>=> (mk_num ctx 1))]
 in
 big_and ctx [ c | f,a <- !funs; i <- Listx.interval 0 (a-1); c <- coeff f a i]
;;


(* DEFINITION OF WEIGHT *)
let vars xs xs' = Listx.unique ([x | x,_ <- xs] @ [x | x,_ <- xs'])

let wadd ctx (w,xs) (w',xs') = 
 let add ctx xs xs' =
  [x, assoc ctx x xs <+> (assoc ctx x xs') | x <- vars xs xs']
 in w <+> w', add ctx xs xs'
;;

let map_cs f ws = [ f w,[x, f v | x,v <- xs] | w,xs <- ws ]

let ite_weights ctx b (w,xs) =
 let add0 x = ite b (mk_num ctx 0) x in
 let ite_all xs ys =
  [z, ite b (assoc ctx z xs) (assoc ctx z ys) | z <- vars xs ys]
 in function
  | [] -> failwith "MPol.ite_weights"
  | (w',ys) :: ws -> (ite b w w', ite_all xs ys) :: (map_cs add0 ws)
;;

let mul ctx c x =
 let zero, one = mk_num ctx 0, mk_num ctx 1 in
 ite (c <=> zero) zero (ite (c <=> one) x (x <+> x))
;;

let weight (ctx,k) t =
 let rec wt = function
  | V x -> [w0 (),[x,mk_num ctx 1]]
  | F(f,ts) -> 
   let wf = w k f,[] in
   let wts = [ wti | ti <- ts; wti <- wt ti] in
   let w_pol = List.fold_left (wadd ctx) wf wts in
   let w_max = wf :: wts in
   ite_weights ctx (stat k f) w_pol w_max
 in cache w_encodings (fun (_,t) -> wt t) (k,t)
;;

let weight_compare ctx cmp k s t =
 let cmp (k,(s,t)) = 
  let ws,wt = weight (ctx,k) s, weight (ctx,k) t in
  let all_ge xs xs' =
   big_and ctx [ (assoc ctx x xs) <>=> (assoc ctx x xs') | x <- vars xs xs']
  in
  let gt (w,xs) (w',xs') = all_ge xs xs' <&> (cmp w w') in
  big_and ctx [big_or ctx [gt n m | n <- ws ] | m <- wt]
 in cmp (k,(s,t))
;;

(* ENCODINGS: COMPARISON *)
let rec first_diff xs ys =
 match xs,ys with
 | _,[]
 | [],_ -> failwith "first_diff: should not happen"
 | x :: xs, y::ys when x = y -> first_diff xs ys
 | x :: _, y :: _ -> (x,y)
;;

let gt (ctx,k) s t =
 let rec gt s t = 
  if (Term.is_subterm s t) || not (Rule.is_rule (s,t)) then mk_false ctx 
  else if (Term.is_subterm t s) then mk_true ctx
  else
  let cmp c = weight_compare ctx c k in
  let strict, weak = cmp (<>>) s t, cmp (<>=>) s t in
  let some_si ss = big_or ctx [ ge si t | si <- ss ] in
  let case2 = 
   match s,t with
    | V _,_ -> mk_false ctx
    | F(_,ss), V _ -> if Term.is_subterm t s then mk_true ctx else mk_false ctx
    | F(f,ss), F(g,ts) ->
     let tjs = big_and ctx [gt s tj | tj <- ts ] in
     if f <> g then 
      (some_si ss) <|> (tjs <&> ((prec k f) <>> (prec k g)))
     else
      let si, ti = first_diff ss ts in
      (some_si ss) <|> (tjs <&> (gt si ti))
  in strict <|> (weak <&> case2)
 and ge s t = if s = t then mk_true ctx else gt s t
 in cache gt_encodings (fun (_,(s',t')) -> gt s' t') (k,(s,t)) 
;;

let ge (ctx,k) s t = 
 if Term.is_subterm s t || not (Rule.is_rule (s,t)) then mk_false ctx else
 if Term.is_subterm t s then mk_true ctx else 
 gt (ctx,k) s t
;;

let init (ctx,k) fs =
  let add (f,a) =
   let s = (name f) ^ (string_of_int k) in
   Hashtbl.add precedence (k,f) (mk_int_var ctx (s^"p"));
   Hashtbl.add weights (k,f) (mk_int_var ctx s);
   Hashtbl.add status (k,f) (mk_fresh_bool_var ctx);
   let init_sc i =
    let s = "sc" ^ s ^ "_" ^ (string_of_int i) in
    Hashtbl.add scs (k,f,i) (mk_int_var ctx s);
   in List.iter init_sc (Listx.interval 0 (a-1))
  in List.iter add fs;
  funs := fs;
  w0_var := Some (mk_int_var ctx ("w0" ^ (string_of_int k)));  
  (wmin (ctx,k)) <&> (coeff (ctx,k))
;;

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
 let add (k',f) v fv = if (k = k') then (f,v):: fv else fv in
 let fv = Hashtbl.fold add precedence [] in
 let has_val d = try let _ = eval_int_var m d in true with _ -> false in
 let prec = [f, eval_int_var m x | f,x <- fv; has_val x] in
 let fs' = [ f | f <- fs; List.mem_assoc f prec ] in
 let pg = Listx.group_by (fun x -> List.assoc x prec) fs' in
 let pg = List.sort ( fun (a,_) (b,_) -> Pervasives.compare b a) pg in
 pp pg
;;

let decode_weights k m fs =
 Format.printf "weights: @\n ";
 let dec_var d = try eval_int_var m d with _ -> 0 in
 Format.printf " w0 = %i\n%!" 
  (dec_var (match !w0_var with Some v -> v | _ -> failwith "no w0"));
 let dec (f, a) =
  let v = Hashtbl.find weights (k,f) in  
  let s = stat k f in
  let w = eval_int_var m v in
  let fn = Signature.get_fun_name f in
  let sc i = Hashtbl.find scs (k,f,i) in
  let si = string_of_int in
  let coeff i v = match v with 0 -> "0" | 1 -> "x"^(si i) | c -> (si c)^" x"^(si i) in 
  let args = [coeff i (dec_var (sc i)) | i <- Listx.interval 0 (a-1)] in
  if eval m s then
   let args = List.fold_left (fun s a -> s ^ a ^ " + ") "" args in
   Format.printf " w(%s) = %s%i\n%!" fn args w
  else
   let args = List.fold_left (fun s a -> s ^ a ^ ", ") "" args in
   Format.printf " w(%s) = max {%s%i}\n%!" fn args w
 in List.iter dec fs
;;

let decode k m =
 let fs = Rules.functions [ rl | rl,_ <- C.get_all_strict 0] in
 decode_prec k m fs;
 decode_weights k m !funs;
;;
