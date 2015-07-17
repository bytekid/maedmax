open Yices

let conj c = function
  | [] -> mk_true c 
  | [v] -> v
  | l -> mk_and c (Array.of_list l)

let disj c = function
  | [] -> mk_false c
  | [v] -> v
  | l -> mk_or c (Array.of_list l)

let xor c v1 v2 = 
  mk_or c [|mk_and c [|mk_not c v1; v2|]; 
            mk_and c [|v1; mk_not c v2|]|]

type t = int * expr

let rec bits n = 
  if n = 0 then 0 else bits (n / 2) + 1

let int c n = 
  let k = bits n in
  (k, mk_bv_constant c k (Int32.of_int n))

let pad c m (k, v) =
  if m < k then invalid_arg "pad" else 
  if m = k then v else 
  mk_bv_concat c (mk_bv_constant c (m - k) Int32.zero) v

let add c ((k1, _) as x) ((k2, _) as y) =
  if k1 = 0 then y else 
  if k2 = 0 then x else
  let k = Pervasives.max k1 k2 + 1 in
  (k, mk_bv_add c (pad c k x) (pad c k y))

let sum c vs = List.fold_left (add c) (int c 0) vs

let mul c ((k1, _) as x) ((k2, _) as y) =
  if k1 = 0 || k2 = 0 then 
    int c 0 
  else
    let k = if k1 = 1 then k2 else if k2 = 1 then k1 else k1 + k2 in
    (k, mk_bv_mul c (pad c k x) (pad c k y))

let geq c ((k1, _) as x) ((k2, _) as y) =
  let k = Pervasives.max k1 k2 in
  mk_bv_ge c (pad c k x) (pad c k y)

let gt c ((k1, _) as x) ((k2, _) as y) =
  let k = Pervasives.max k1 k2 in
  mk_bv_gt c (pad c k x) (pad c k y)
