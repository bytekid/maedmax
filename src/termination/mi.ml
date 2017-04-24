open Listx
open Term
open Format
open Yices
open Arith
open Matrix

(* Matrix Interpretations *)

let rec interpret ~c ~d ~a ~b ?(m = unit_m c d) = function
  | V x -> ([x, m], zero_v c d)
  | F (f,ts) -> 
      let l = 
        [ interpret ~c ~d ~a ~b ~m:(mul_mm c m (List.assoc (f, i) a)) ti 
        | i, ti <- ix ts ] in
      let al, vs = List.split l in
      ([ x, sum_m c d ms | x, ms <- group (List.concat al) ], 
       sum_v c d (mul_mv c m (List.assoc f b) :: vs))

let lookup c d x a = 
  try List.assoc x a with Not_found -> zero_m c d

let gt_rule ~c ~d ~a ~b s t = 
  let a1, v1 = interpret ~c ~d ~a ~b s 
  and a2, v2 = interpret ~c ~d ~a ~b t in
  conj c 
    (gt_v c v1 v2 :: 
     [ geq_m c (lookup c d x a1) (lookup c d x a2) 
     | x <- Rule.variables (s, t) ])

let var c k s = 
  let bv_type = mk_bitvector_type c k in
  let x = mk_var_decl c s bv_type in
  mk_var_from_decl c x

let name = Signature.get_fun_name

let vector c d k s = 
  [ k, var c k (sprintf "%s-%d" s j) | j <- interval 0 (d - 1) ] 

let matrix c d k s = 
  [ vector c d k (sprintf "%s-%d" s i) | i <- interval 0 (d - 1) ]

let fi c d k f i = matrix c d k (sprintf "%s-%d" (name f) i)

let order ~d ~k c rules =
  let fs = Rules.signature rules in
  let a = [ (f, i), fi c d k f i | f, n <- fs; i <- interval 0 (n - 1) ] in
  let b = [ f, vector c d k (name f) | f, _ <- fs ] in
  List.iter (assert_simple c)
    [ Arith.geq c (List.nth (List.nth m 0) 0) (Arith.int c 1) | x, m <- a ];
  [ (l, r), gt_rule ~c ~d ~a ~b l r | l, r <- rules ]
