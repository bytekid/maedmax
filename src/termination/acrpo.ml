(*** MODULES *****************************************************************)
module L = List
module C = Cache
module F = Format
module Sig = Signature
module Logic = Settings.Logic

(*** OPENS *******************************************************************)
open Term
open Logic
open Logic.Int

(*** TYPES *******************************************************************)
(*** GLOBALS *****************************************************************)

let funs = ref []
(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Sig.sym, Logic.t) Hashtbl.t = Hashtbl.create 32
let status_mul : (int * Sig.sym, Logic.t) Hashtbl.t = Hashtbl.create 32
let var_count = ref 0

(*** FUNCTIONS ***************************************************************)
let name = Sig.get_fun_name

let prec f i = 
  try Hashtbl.find precedence (i,f) with
  Not_found ->
    failwith ("Acrpo.prec: unknown " ^ (name f) ^ ", " ^ (string_of_int i))
;;

let status_is_mul i f = 
  try Hashtbl.find status_mul (i,f) with
  Not_found ->
    failwith ("Acrpo.status: unknown " ^ (name f) ^ ", " ^ (string_of_int i))
;;

let pair_map f (s,t) = (f s, f t)

let index = Listx.index

let forall2 f xs ys =
  assert (List.length xs = List.length ys);
  List.fold_left (fun b (x,y) -> f x y && b) true (Listx.zip xs ys)
;;

let diff xs ys = List.fold_left (fun xs y -> Listx.remove y xs) xs ys

(* approximation ... not complete for ac terms *)
let rec embac_ge s t = match (s,t) with
  | V x, V y -> x = y
  | F (f,ss), F (g,ts) when f=g ->
    (List.length ss = List.length ts
    && forall2 embac_ge ss ts) || List.exists (fun si -> embac_ge si t) ss
  | F (_,ss),_ -> List.exists (fun si -> embac_ge si t) ss
  | _, _ -> false
;;

let embac_gt s t = List.exists (fun si -> embac_ge si t) (direct_subterms s)

(* lex comparison *)
let rec lex ctx gt eq ts ss = match ts,ss with
 | _::_,[] -> mk_true ctx
 | [], _ -> mk_false ctx
 | ti::ts,si::ss ->
  big_or ctx [gt ti si; big_and ctx [eq ti si; lex ctx gt eq ts ss]]
;;


let mk_fresh_int_var ctx =
  var_count := !var_count + 1;
  Int.mk_var ctx ("cov"^ (string_of_int !var_count))
;;

(* multiset cover *)
let mul_cover ctx ss ts =
 let cs = [ mk_fresh_int_var ctx | j,tj <- index ts ] in
 let m = List.length ss in
 let zero = Int.mk_num ctx 0 in
 big_and ctx [(Int.mk_num ctx m <>> ci) <&> (ci <>=> zero) | ci <- cs], cs
;;

(* expresses multiset cover for arguments in ss and ts satisfying p *)
let mul_p ctx p gt eq ss ts =
 let cover, cs = mul_cover ctx ss ts in
 let is cj i = cj <=> (Int.mk_num ctx i) in
 let gtp si tj = (gt si tj <|> eq si tj) <&> p si in
 let y cj tj = big_and ctx [ (is cj i) <=>> (gtp si tj) | i,si <- index ss] in
 let tcs = index (Listx.zip ts cs) in
 big_and ctx (cover :: [p tj <=>> y cj tj | j, (tj, cj) <- tcs])
;;

let mul_ge_p ctx p gt eq ss ts =
 let ss,ts = diff ss ts, diff ts ss in
 mul_p ctx p gt eq ss ts
;;

let str = List.fold_left (fun s t -> s ^ ", " ^ (Term.to_string t)) ""

let mul_gt_p ctx p gt eq ss ts =
  let ss, ts = diff ss ts, diff ts ss in
  match ss, ts with
  | [], _ ->  mk_false ctx
  | [s], [t] -> gt s t
  | _ ->
    let cover, cs = mul_cover ctx ss ts in
    let is cj i = cj <=> (Int.mk_num ctx i) in
    let gep si tj = (gt si tj <|> eq si tj) <&> p si in
    let gtp si tj = gt si tj <&> p si in
    let yge cj tj = big_and ctx [ (is cj i) <=>> (gep si tj) | i,si <- index ss] in
    let ygt cj tj = big_and ctx [ (is cj i) <=>> (gtp si tj) | i,si <- index ss] in
    let tcs = index (Listx.zip ts cs) in
    let ge = [p tj <=>> yge cj tj | j, (tj, cj) <- tcs] in
    let strict = big_or ctx [p tj <&> ygt cj tj | j, (tj, cj) <- tcs] in
    big_and ctx (cover :: strict :: ge)
;;

let mul_gt ctx gt eq ss ts = mul_gt_p ctx (fun _ -> mk_true ctx) gt eq ss ts

(* emb_small candidates *)
let emb_sm f ts =
 let tf = function F (g, ts) when g = f -> ts | t -> [t] in
 let rec emb hd =  function
  | [] -> []
  | ((V _) as t)::ts -> emb (hd @ [t]) ts
  | F(h, hs) :: ts when f = h -> failwith ("emb_sm: not flat?!") (*emb (hd @ [t]) ts*)
  | (F(h, hs) as t)::ts -> [hd @ (tf hi) @ ts,h | hi <- hs ] @ (emb (hd@[t]) ts)
 in [F(f, ts), h | ts, h <- emb [] ts ]
;;

(* compare argument lists with respect to length*)
let size_cmp cmp ss ts =
 let (vs,fs),(vt,ft) = pair_map (List.partition Term.is_variable) (ss,ts) in
 let vs, vt = Listset.diff vs vt, Listset.diff vt vs in
 (vt = []) && (cmp (List.length (vs @ fs)) (List.length ft))
;;

(* #s > #t *)
let size_gt = size_cmp (>)
(* #s = #t *)
let size_ge = size_cmp (>=) 

let is_ac f = List.mem f (Signature.ac_symbols ())

let flatten t = flatten (Signature.ac_symbols ()) t

let acrpo_gt (ctx,i) s t =
  let prec f g = (prec f i) <>> (prec g i) in
  let is_mul f a = if a < 2 then mk_false ctx else status_is_mul i f in 
  let is_lex f a = if a < 2 then mk_true ctx else !! (status_is_mul i f) in
  let rec yrpo_gt s t =
    let (s,t) = (flatten s, flatten t) in
    if embac_ge t s || not (Rule.variable_condition (s,t)) then mk_false ctx
    else if embac_gt s t then mk_true ctx
    else
      match s,t with
      | V _, _ -> mk_false ctx
      | F _, V x -> if List.mem x (variables s) then mk_true ctx else mk_false ctx
      | F (f,ss), F (g,ts) when f <> g ->
        let one = big_or ctx [yrpo_ge si t | si <- ss] in              (* (1) *)
        (
          let two = big_and ctx ((prec f g) :: [yrpo_gt s tj | tj <- ts]) in (*(2) *)
          one <|> two
        )
      | F (f,ss), F (_,ts)  ->
        if not (is_ac f) then
          let a = List.length ss in
          let one = big_or ctx [yrpo_ge si t | si <- ss]  in                    (* (1) *)
          let three = big_and ctx [is_lex f a; lex ctx yrpo_gt yrpo_eq ss ts] in (* (3) *)
          let four = big_and ctx [is_mul f a; mul_gt ctx yrpo_gt yrpo_eq ss ts] in(* (4) *)
          one <|> three <|> four
        else 
         (
          let cover h s' = prec f h <&> yrpo_ge s' t in
          let five = big_or ctx [ cover h (flatten s') | s',h <- emb_sm f ss ] in (* (5) *)
          let embs = [ prec f h <=>> yrpo_gt s t' | t',h <- emb_sm f ts ] in
          
          let six1 = big_and ctx ((no_small_head f ss ts) :: embs) in            (* (6) *)
          let six2 = big_head_eq f ss ts in
          let case = 
            if size_gt ss ts then mk_true ctx                                  (* (6b) *)
            else if not (size_ge ss ts) then big_head f ss ts                  (* (6a) *)
            else big_or ctx [big_head f ss ts; mul_gt ctx yrpo_gt yrpo_eq ss ts](* (6c) *)
          in
          five <|> (six1 <&> six2 <&> case) 
         )

and no_small_head f ss ts =
  let p = function V _ -> mk_true ctx | F (h,_) -> !! (prec f h) in
  mul_ge_p ctx p yrpo_gt yrpo_eq ss ts

and big_head f ss ts =
  if ss = [] then mk_false ctx
  else
    let p = function V _ -> mk_false ctx | F (h,_) -> prec h f in
    mul_gt_p ctx p yrpo_gt yrpo_eq ss ts

and big_head_eq f ss ts =
  if ss = ts then mk_true ctx 
  else if ss = [] then mk_false ctx
  else
    let p = function V _ -> mk_false ctx | F (h,_) -> prec h f in
    mul_ge_p ctx p yrpo_gt yrpo_eq ss ts

and yrpo_ge s t = if flatten s = flatten t then mk_true ctx else yrpo_gt s t
 
and yrpo_eq s t = if flatten s = flatten t then mk_true ctx else mk_false ctx 
  (* ok if all terms sorted + flat *)
  in
  yrpo_gt s t
;;

let gt = acrpo_gt

let ge (ctx,i) s t = if s = t then mk_true ctx else acrpo_gt (ctx,i) s t

let init (ctx,k) fs =
  Hashtbl.clear precedence;
  let add (f,_) =
    let s = "rpo" ^ (Sig.get_fun_name f) ^ (string_of_int k) in
    Hashtbl.add precedence (k,f) (Int.mk_var ctx (s^"p"));
    Hashtbl.add status_mul (k,f) (mk_fresh_bool_var ctx);
  in List.iter add fs;
  funs := fs;
  (* total: causes stack overflow with too large signatures *)
  let total_prec =
    if List.length fs > 400 then mk_true ctx
    else
      let ps = [ f,g | f,_ <- fs; g,_ <- fs; f <> g ] in
      let p f = prec f k in
      big_and ctx [ p f <!=> p g | f, g <- ps ]
  in
  let num_0 = Int.mk_zero ctx in
  let num_n = Int.mk_num ctx (L.length fs) in
  let bounds f = let p = prec f k in (p <>=> num_0) <&> (num_n <>=> p) in
  let total = big_and1 (total_prec :: [ bounds f | f,_ <- fs ]) in
  let ac = big_and ctx [ status_is_mul k f | f,_ <- fs; is_ac f ] in
  ac <&> total
;;

let decode_prec_aux k m =
  let add (k',f) x p =
    if k <> k' then p
    else (
      try
        let v = Int.eval m x in
        Hashtbl.add p f v; p
      with _ -> p)
  in Hashtbl.fold add precedence (Hashtbl.create 16)
 ;;

 let eval_prec k m =
  let prec = Hashtbl.find (decode_prec_aux k m) in
  List.sort (fun (_, p) (_,q) -> p - q) [ (f,a), prec f | f,a <- !funs ]
 ;;
 
 let prec_to_string = function
     [] -> ""
   | ((f,_),p) :: fp ->
     let s = "AC-RPO \n " ^ (name f) in
     List.fold_left (fun s ((f,_),_) -> s ^ " < " ^ (name f)) s fp;
 ;;
 
 let print_prec p = Format.printf "%s\n%!" (prec_to_string p)
 
 let decode_print k m = print_prec (eval_prec k m)
 
 let decode_term_gt k m =
  let prec = Hashtbl.find (decode_prec_aux k m) in
  let rec gt s t =
   if Term.is_subterm s t then false
   else if Term.is_subterm t s then true
   else
    match s,t with
     | V _, _
     | _, V _  -> false (* no subterm *)
     | F(f,ss), F(g,ts) ->
       let sub_gt = L.exists (fun si -> (gt si t) || (si = t)) ss in
       if f <> g then
        sub_gt || (prec f > prec g && L.for_all (gt s) ts)
       else (
        let lex (gt_lex,ge) (si,ti) = gt_lex || (ge && gt si ti), ge && si=ti in
        let lex_gt = fst (L.fold_left lex (false, true) (List.combine ss ts)) in
        sub_gt || (lex_gt && L.for_all (gt s) ts))
   in gt
 ;;

 let encode i preclist ctx =
  let add ((f,_), p) = (prec f i <=> (Int.mk_num ctx p)) in
  Logic.big_and ctx (List.map add preclist)
 ;;

 let decode k m =
  let gt = decode_term_gt k m in
  let cmp c d = if gt (Term.F(c,[])) (Term.F(d,[])) then d else c in
  let bot =  match [ c | c,a <- !funs; a = 0] with
      [] -> None
    | c :: cs -> Some (List.fold_left cmp c cs)
  in
  let prec = eval_prec k m in
  object
    method bot = bot
    method gt = gt
    method smt_encode = encode k prec
    method to_string = prec_to_string prec
    method print = fun _ -> print_prec prec
    method to_xml = Xml.Element("acrpo", [], [])
    method print_params = fun _ -> Format.printf "-ac\n%!"
  end
;;