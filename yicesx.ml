(*** OPENS *******************************************************************)
open Yices

(*** GLOBALS *****************************************************************)
let yt = ref None
let yf = ref None

(*** FUNCTIONS ***************************************************************)
let ytrue ctx =
 match !yt with None -> let t = mk_true ctx in yt := Some t; t | Some t -> t

let yfalse ctx =
 match !yf with None -> let f = mk_false ctx in yf := Some f; f | Some f -> f

let yor ctx x y = 
 let t, f = ytrue ctx, yfalse ctx in
 if x == t || y == t then t else
 if x == f then y else if y == f then x else
(*
 match x,y with
   True, _
 | _, True -> mk_true ctx
 | False, _ -> y
 | _ , False -> x
 | _ ->*) mk_or ctx [| x; y |]

let yand ctx x y = 
 let t, f = ytrue ctx, yfalse ctx in
 if x == f || y == f then f else
 if x == t then y else if y == t then x else
 (*let t, f = mk_true ctx, mk_false ctx in
 match x,y with
   f, _ 
 | _, f -> mk_false ctx
 | t, _ -> y
 | _ , t -> x
 | _ ->*) mk_and ctx [| x; y |]

let yimp ctx x y = mk_or ctx [| mk_not ctx x; y |]

let yiff ctx x y = yand ctx (yimp ctx x y) (yimp ctx y x)

let ybig_and ctx xs =
 let t, f = ytrue ctx, yfalse ctx in
 if List.exists (fun x -> x == f) xs then f
 else
  match List.filter (fun x -> x != t) xs with
    []  -> ytrue ctx
  | [x] -> x
  | xs  -> mk_and ctx (Array.of_list xs)
;;

let ybig_or ctx xs =
 let t, f = ytrue ctx, yfalse ctx in
 if List.exists (fun x -> x == t) xs then t
 else
  match List.filter (fun x -> x != f) xs with 
   []  -> yfalse ctx
 | [x] -> x
 | xs  -> mk_or ctx (Array.of_list xs)
;;

let ynot ctx x = mk_not ctx x

let ysum ctx = function
   []  -> mk_num ctx 0
 | [x] -> x
 | xs  -> mk_sum ctx (Array.of_list xs)
;;

let ymul ctx = function
   []  -> mk_num ctx 1
 | [x] -> x
 | xs  -> mk_mul ctx (Array.of_list xs)
;;

let ygt ctx x y = mk_gt ctx x y

let yge ctx x y = mk_ge ctx x y

let yeq ctx x y = mk_eq ctx x y

let yneq ctx x y = mk_diseq ctx x y

let yeval m x =
 try evaluate_in_model m x = True
 with _ -> failwith "evaluate_in_model: variable unknown"
;;

let yite = mk_ite

let ymax ctx x y = yite ctx (ygt ctx x y) x y

let yone ctx = mk_num ctx 1

let yzero ctx = mk_num ctx 0
