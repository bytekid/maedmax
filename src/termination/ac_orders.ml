open Term
open Yices
open Arith

type t = RPO

let pair_map f (s,t) = (f s, f t)

let index = Listx.index

let zip = List.map2 (fun x y -> x,y)

let forall2 f xs ys = List.fold_left (fun b (x,y) -> f x y && b) true (zip xs ys)

let mk_andl ctx l = if l = [] then mk_true ctx else mk_and ctx (Array.of_list l)

let mk_orl ctx l = if l = [] then mk_false ctx else mk_or ctx (Array.of_list l)

let mk_imp ctx a b = mk_or ctx [|mk_not ctx a; b|]

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


let vcount = ref 0

let mk_fresh_decl ctx =
 let v = !vcount in
 vcount := v + 1;
 let ty  = mk_type ctx "int" in
 mk_var_decl ctx ("v"^(string_of_int v)) ty
;;

(* lex comparison *)
let rec lex ctx gt eq ts ss = match ts,ss with
 | _::_,[] -> mk_true ctx
 | [], _ -> mk_false ctx
 | ti::ts,si::ss ->
  mk_orl ctx [gt ti si; mk_andl ctx [eq ti si; lex ctx gt eq ts ss]]
;;


(* multiset cover *)
let mul_cover ctx ss ts =
 let cs = [mk_var_from_decl ctx (mk_fresh_decl ctx) | j,tj <- index ts ] in
 let m = List.length ss in
 mk_andl ctx [mk_lt ctx ci (mk_num ctx m) | ci <- cs], cs
;;

(* expresses multiset cover for arguments in ss and ts satisfying p *)
let mul_p ctx p gt eq ss ts =
 let (cover,cs) = mul_cover ctx ss ts in
 let is cj i = mk_eq ctx cj (mk_num ctx i) in
 let gtp si tj = mk_and ctx [|gt si tj; p si|] in
 let y cj tj = mk_andl ctx [mk_imp ctx (is cj i) (gtp si tj) | i,si <- index ss] in
 let tcs = index (List.map2 (fun x y -> x,y) ts cs) in
 mk_andl ctx (cover :: [mk_imp ctx (p tj) (y cj tj) | j,(tj,cj) <- tcs])
;;

(* expresses multiset cover for all args in ss and ts *)
let mul ctx gt eq ss ts =
 let (cover,cs) = mul_cover ctx ss ts in
 let is cj i = mk_eq ctx cj (mk_num ctx i) in
 let y cj tj = mk_andl ctx [mk_imp ctx (is cj i) (gt si tj) | i,si <- index ss] in
 let tcs = index (List.map2 (fun x y -> x,y) ts cs) in
 mk_andl ctx (cover :: [y cj tj | j,(tj,cj) <- tcs])
;;

let mul_gt ctx gt eq ss ts =
 let ss,ts = Listset.diff ss ts, Listset.diff ts ss in
 if ss = [] then mk_false ctx else mul ctx gt eq ss ts
;;

let mul_ge_p ctx p gt eq ss ts =
 let ss,ts = Listset.diff ss ts, Listset.diff ts ss in
 mul_p ctx p gt eq ss ts
;;

let mul_gt_p ctx p gt eq ss ts =
 let strict = mk_orl ctx [ p si | si <- Listset.diff ss ts] in
 mk_and ctx [|mul_ge_p ctx p gt eq ss ts; strict|]
;;

(* emb_small candidates *)
let emb_sm f ts =
 let tf = function F (g,ts) when g=f -> ts | t -> [t] in
 let rec emb hd =  function
  | [] -> []
  | ((V _) as t)::ts -> emb (hd@[t]) ts
  | (F(h,hs) as t)::ts when f=h -> emb (hd@[t]) ts
  | (F(h,hs) as t)::ts -> [hd@(tf hi)@ts,h | hi <- hs ] @ (emb (hd@[t]) ts)
 in [F(f,ts),h | ts,h <- emb [] ts ]
;;

(* compare argument lists with respect to length*)
let size_cmp cmp ss ts =
 let (vs,fs),(vt,ft) = pair_map (List.partition Term.is_variable) (ss,ts) in
 let vs,vt = Listset.diff vs vt, Listset.diff vt vs in
 (vt = []) && (cmp (List.length (vs@fs)) (List.length ft))
;;
(* #s > #t *)
let size_gt = size_cmp (>)
(* #s = #t *)
let size_ge = size_cmp (>=) 

let yacrpo ctx ac (ps,ss) s t =
 let is_ac f = List.mem f ac in
 let prec f g = mk_gt ctx (List.assoc f ps) (List.assoc g ps) in
 let is_mul f a = if a < 2 then mk_false ctx else List.assoc f ss in 
 let is_lex f a = if a < 2 then mk_true ctx else mk_not ctx (List.assoc f ss) in 
 let rec yrpo_gt s t =
  let (s,t) = (flatten ac s, flatten ac t) in
   if embac_ge t s || not (Rule.variable_condition (s,t)) then mk_false ctx
   else if embac_gt s t then mk_true ctx
   else
    match s,t with
    | V _, _ -> mk_false ctx
    | F _, V x -> if List.mem x (variables s) then mk_true ctx else mk_false ctx
    | F (f,ss), F (g,ts) when f <> g ->
     let one = mk_orl ctx [yrpo_ge si t | si <- ss] in                     (* (1) *)
     (try let two = mk_andl ctx ((prec f g) :: [yrpo_gt s tj | tj <- ts]) in    (* (2) *)
     mk_or ctx [|one;two|] with _ -> failwith "f <> g")
   | F (f,ss), F (_,ts)  ->
    if not (is_ac f) then
     let a = List.length ss in
     let one = mk_orl ctx [yrpo_ge si t | si <- ss]  in                    (* (1) *)
     let three = mk_andl ctx [is_lex f a; lex ctx yrpo_gt yrpo_eq ss ts] in (* (3) *)
     let four = mk_andl ctx [is_mul f a; mul_gt ctx yrpo_gt yrpo_eq ss ts] in(* (4) *)
     mk_or ctx [| one;three;four |]
    else 
     (try let cover h s' = mk_and ctx [|prec f h; yrpo_ge s' t|] in
     let five = mk_orl ctx [ cover h (flatten ac s') | s',h <- emb_sm f ss ] in (* (5) *)
     let embs = [ mk_imp ctx (prec f h) (yrpo_gt s t') | t',h <- emb_sm f ts ] in
     let six' = mk_andl ctx ((no_small_head f ss ts)::embs) in            (* (6) *)
     let case = 
      if size_gt ss ts then mk_true ctx                                  (* (6b) *)
      else if not (size_ge ss ts) then big_head f ss ts                  (* (6a) *)
      else mk_orl ctx [big_head f ss ts; mul_gt ctx yrpo_gt yrpo_eq ss ts](* (6c) *)
     in
     mk_or ctx [| five; mk_and ctx [| six'; case |] |] 
     with _ -> failwith "here")

 and no_small_head f ss ts =
  let p = function V _ -> mk_true ctx | F (h,_) -> mk_not ctx (prec f h) in
  mul_ge_p ctx p yrpo_gt yrpo_eq ss ts

 and big_head f ss ts =
  if ss = [] then mk_false ctx
  else
   let p = function V _ -> mk_false ctx | F (h,_) -> prec h f in
   mul_gt_p ctx p yrpo_gt yrpo_eq ss ts

 and yrpo_ge s t = if s = t then mk_true ctx else yrpo_gt s t
 
 and yrpo_eq s t = if s = t then mk_true ctx else mk_false ctx 
 (* ok if all terms sorted + flat *)
in yrpo_gt s t 
