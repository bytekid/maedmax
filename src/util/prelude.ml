let flip f x y = f y x

let (<.>) f g x = f (g x)

let uncurry f (x,y) = f x y

let unique_with eq =
 let all_diff y = List.for_all (fun x -> not (eq x y)) in
 let rec unique acc = function
  | [] -> acc
  | y :: xs ->
   unique (if all_diff y xs then y :: acc else acc) xs 
 in unique []
;;