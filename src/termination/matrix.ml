open Listx
open Yices
open Arith

(* Matrix and Vector Arithmeric *)

type v = Arith.t list
type m = v list

let zero_v c d = [ int c 0 | i <- interval 0 (d - 1) ]

let zero_m c d = [ zero_v c d | i <- interval 0 (d - 1) ]

let unit_m c d = 
  [  [ if i = j then int c 1 else int c 0 | j <- interval 0 (d-1) ] | i <- interval 0 (d-1) ]

let add_v c v1 v2 = List.map2 (add c) v1 v2

let sum_v c d vs = List.fold_left (add_v c) (zero_v c d) vs

let mul_vv c v1 v2 = sum c (List.map2 (mul c) v1 v2)

let add_m c m1 m2 = List.map2 (add_v c) m1 m2

let sum_m c d ms = List.fold_left (add_m c) (zero_m c d) ms

let mul_mv c m v = [ mul_vv c u v | u <- m ]

let mul_mm c m1 m2 = 
  let m2t = transpose m2 in
  [ [ mul_vv c v1 v2 | v2 <- m2t ] | v1 <- m1 ]

let gt_v c v1 v2 = 
  match v1, v2 with
  | x :: xs, y :: ys -> mk_and c (Array.of_list (gt c x y ::  List.map2 (geq c) xs ys))
  | _, _ -> failwith "Matrix.gt_v"

let geq_v c v1 v2 = mk_and c (Array.of_list (List.map2 (geq c) v1 v2))

let geq_m c m1 m2 = 
  mk_and c (Array.of_list (List.map2 (geq_v c) m1 m2))
