(*** MODULES *****************************************************************)
module St = Statistics
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yices
open Yicesx
open Arith

(*** TYPES *****************************************************************)
type poly = Yices.expr * (Signature.var * Yices.expr) list

(*** GLOBALS *****************************************************************)
(* signature *)
let funs = ref []

(* weight status, a boolean for each function symbol *)
let status : (int * Signature.sym, Yices.expr) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable for weight *)
let weights : (int * Signature.sym, Yices.var_decl * Yices.expr) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Signature.sym, Yices.var_decl * Yices.expr) Hashtbl.t 
 = Hashtbl.create 32

(* map function symbol, strategy stage and argument position to coefficient *)
let scs : (int * Signature.sym * int, Yices.var_decl * Yices.expr) Hashtbl.t
 = Hashtbl.create 32

let w0_var = ref None

(* cache results of comparison *)
let gt_encodings : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 512
let ge_encodings : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 512
let w_encodings : (int * Term.t, poly list) Hashtbl.t = Hashtbl.create 512
let wcmp_encodings : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 512
(*** FUNCTIONS ***************************************************************)
let cache ht f k =
 try Hashtbl.find ht k with Not_found ->
 let v = f k in Hashtbl.add ht k v; v
;;


let index = Listx.index

let w0 _ = match !w0_var with None -> failwith"Msum: no w0" | Some w0 -> snd w0

let name = Signature.get_fun_name

let w k f = 
 try snd (Hashtbl.find weights (k,f))
 with Not_found -> failwith "MPol.w: Not_found"

let prec k f = 
 try snd (Hashtbl.find precedence (k,f))
 with Not_found -> failwith "MPol.prec: Not_found"

let sc k f i = 
 try snd (Hashtbl.find scs (k,f,i))
 with Not_found -> failwith "MPol.sc: Not_found"

(* true if status is pol *)
let stat k f = 
 try Hashtbl.find status (k,f) 
 with Not_found -> failwith "MPol.stat: Not_found"

let assoc ctx x xs = try List.assoc x xs with Not_found -> mk_num ctx 0

(* ENCODINGS: SIDE CONDITIONS *)
let wmin (ctx,k) = 
 let nat = ybig_and ctx [yge ctx (w k c) (mk_num ctx 0) | c,a <- !funs] in
 let w0n = yge ctx (w0 ()) (mk_num ctx 0) in
 ybig_and ctx (w0n :: nat :: [yge ctx (w k c) (w0 ()) | c,a <- !funs; a = 0 ])
;;

(* subterm coefficients must be nonzero for functions with polynomial status *)
let coeff (ctx,k) =
 let coeff f a i = 
  let c = sc k f i in
  [yge ctx (mk_num ctx 2) c; yge ctx c (mk_num ctx 0); 
   yimp ctx (stat k f) (yge ctx c (mk_num ctx 1))]
 in
 ybig_and ctx [ c | f,a <- !funs; i <- Listx.interval 0 (a-1); c <- coeff f a i ]
;;


(* DEFINITION OF WEIGHT *)
let vars xs xs' = Listx.unique ([x | x,_ <- xs] @ [x | x,_ <- xs'])

let wadd ctx (w,xs) (w',xs') = 
 let add ctx xs xs' =
  [x, ysum ctx [assoc ctx x xs; assoc ctx x xs'] | x <- vars xs xs']
 in ysum ctx [w; w'], add ctx xs xs'
;;

let map_cs f ws = [ f w,[x, f v | x,v <- xs] | w,xs <- ws ]

let ite_weights ctx b (w,xs) =
 let add0 x = yite ctx b (mk_num ctx 0) x in
 let ite_all xs ys =
  [z, yite ctx b  (assoc ctx z xs) (assoc ctx z ys) | z <- vars xs ys]
 in function
  | [] -> (*map_cs (yand ctx b) [w,xs]*) failwith "MPol.ite_weights"
  | (w',ys) :: ws -> (yite ctx b w w', ite_all xs ys) :: (map_cs add0 ws)
;;

let mul ctx c x =
 let y0, y1, y2 = mk_num ctx 0, mk_num ctx 1, mk_num ctx 2 in
 yite ctx (yiff ctx c y0) y0 (yite ctx (yiff ctx c y1) x (ysum ctx [x;x]))
;;

let weight (ctx,k) t =
 let rec wt = function
  | V x -> [w0 (),[x,mk_num ctx 1]]
  | F(f,ts) -> 
   let msc i x = mul ctx (sc k f i) x in
   let wf = w k f,[] in
   let wts = [ wti | ti <- ts; wti <- wt ti]
    (*[msc i w, [x, msc i v | x,v <- xs] | i,t <- index ts; w,xs <- wt t]*) in
   let w_pol = List.fold_left (wadd ctx) wf wts in
   let w_max = wf :: wts in
   ite_weights ctx (stat k f) w_pol w_max
 in cache w_encodings (fun (_,t) -> wt t) (k,t)
;;

let weight_compare ctx cmp k s t =
 let cmp (k,(s,t)) = 
  let ws,wt = weight (ctx,k) s, weight (ctx,k) t in
  let all_ge xs xs' =
   ybig_and ctx [yge ctx (assoc ctx x xs) (assoc ctx x xs') | x <- vars xs xs']
  in
  let gt (w,xs) (w',xs') = yand ctx (all_ge xs xs') (cmp ctx w w') in
  ybig_and ctx [ybig_or ctx [gt n m | n <- ws ] | m <- wt]
 in (*cache wcmp_encodings*) cmp (k,(s,t))
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
  if (Term.is_subterm s t) || not (Rule.is_rule (s,t)) then yfalse ctx 
  else if (Term.is_subterm t s) then ytrue ctx
  else
  let strict, weak = weight_compare ctx ygt k s t, weight_compare ctx yge k s t in
  let some_si ss = ybig_or ctx [ ge si t | si <- ss ] in
  let case2 = 
   match s,t with
    | V _,_ -> yfalse ctx
    | F(_,ss), V _ -> if Term.is_subterm t s then ytrue ctx else yfalse ctx
    | F(f,ss), F(g,ts) ->
     let tjs = ybig_and ctx [gt s tj | tj <- ts ] in
     if f <> g then 
      yor ctx (some_si ss) (yand ctx tjs (ygt ctx (prec k f) (prec k g)))
     else
      let si, ti = first_diff ss ts in
      yor ctx (some_si ss) (yand ctx tjs (gt si ti))
  in yor ctx strict (yand ctx weak case2)
 and ge s t = if s = t then ytrue ctx else gt s t
 in cache gt_encodings (fun (_,(s',t')) -> gt s' t') (k,(s,t)) 
;;

let ge (ctx,k) s t = 
 if Term.is_subterm s t || not (Rule.is_rule (s,t)) then yfalse ctx else
 if Term.is_subterm t s then ytrue ctx else 
 gt (ctx,k) s t
;;

let init (ctx,k) fs =
 let ty  = mk_type ctx "int" in
  let add (f,a) =
   let s = (name f) ^ (string_of_int k) in
   let dp = mk_var_decl ctx (s^"p") ty in
   let dw = mk_var_decl ctx s ty in
   let xp = mk_var_from_decl ctx dp in
   let xw = mk_var_from_decl ctx dw in
   let xs = mk_fresh_bool_var ctx in 
   Hashtbl.add precedence (k,f) (dp,xp);
   Hashtbl.add weights (k,f) (dw,xw);
   Hashtbl.add status (k,f) xs;
   let init_sc i =
    let s = "sc" ^ s ^ "_" ^ (string_of_int i) in
    let dsci = mk_var_decl ctx s ty in
    let xsci = mk_var_from_decl ctx dsci in
    Hashtbl.add scs (k,f,i) (dsci, xsci);
   in List.iter init_sc (Listx.interval 0 (a-1))
  in List.iter add fs;
  funs := fs;
  let d = mk_var_decl ctx ("w0" ^ (string_of_int k)) ty in
  w0_var := Some (d,mk_var_from_decl ctx d);  
  yand ctx (wmin (ctx,k)) (coeff (ctx,k))
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

let decode_weights k m fs =
 Format.printf "weights: @\n ";
 let dec_var d = try Int32.to_int (get_int_value m d) with _ -> 0 in
 Format.printf " w0 = %i\n%!" 
  (dec_var (match !w0_var with Some (d,_) -> d | _ -> failwith "no w0"));
 let dec (f, a) =
  let (v,_) = Hashtbl.find weights (k,f) in  
  let s = stat k f in
  let w = Int32.to_int (get_int_value m v) in
  let fn = Signature.get_fun_name f in
  let sc i = fst (Hashtbl.find scs (k,f,i)) in
  let si = string_of_int in
  let coeff i v = match v with 0 -> "0" | 1 -> "x"^(si i) | c -> (si c)^" x"^(si i) in 
  let args = [coeff i (dec_var (sc i)) | i <- Listx.interval 0 (a-1)] in
  if evaluate_in_model m s == True then
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
