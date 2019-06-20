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

let hex2dec s =
  let rec hex2dec i v =
    if String.length s <= i then v
    else
      let c = Char.code (String.get s i) in
      let a =
        if 48 <= c && c <= 57 then c - 48
        else if 97 <= c && c <= 102 then c - 87
        else if 65 <= c && c <= 70 then c - 55
        else failwith "Constrained.hex2dec failed"
      in
      hex2dec (i + 1) (16 * v + a)
  in hex2dec 0 0
;;
