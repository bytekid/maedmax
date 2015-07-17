(* $Id: listset.ml,v 1.1 2013/11/28 08:50:09 swinkler Exp $ *)
(* Set theoretical operations for `list' *)

let empty = [] 

let singleton x = [x]

let is_empty xs = xs = []

let rec unique = function
  | [] -> []
  | x :: xs -> x :: unique (List.filter (fun y -> x <> y) xs)

let add x xs = 
  if List.mem x xs then xs else x :: xs

let subset xs ys = 
  List.for_all (fun x -> List.mem x ys) xs

let equal xs ys = subset xs ys && subset ys xs

let union xs ys = unique (xs @ ys)

let big_union xss = unique (List.concat xss)

let inter xs ys = 
  List.filter (fun x -> List.mem x ys) (unique xs)

let diff xs ys = 
  List.filter (fun x -> not (List.mem x ys)) (unique xs)

let remove x xs = diff xs [x]

let concat xss = unique (List.concat xss)
