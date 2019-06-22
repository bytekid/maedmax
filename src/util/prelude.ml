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

let hex2bin s =
  let rec hex2bin i v =
    if String.length s <= i then v
    else
      let c = Char.code (String.get s i) in
      let a =
        if 48 <= c && c <= 57 then c - 48
        else if 97 <= c && c <= 102 then c - 87
        else if 65 <= c && c <= 70 then c - 55
        else failwith "Constrained.hex2bin failed"
      in
      let bit b = if b = 0 then "0" else "1" in
      let h = (bit (a / 8)) ^ (bit ((a mod 8) / 4)) ^ (bit ((a mod 4) / 2)) ^ (bit (a mod 2)) in
      hex2bin (i + 1) (v ^ h)
  in
  let s = hex2bin 0 "" in
  let rec trim s =
    if String.length s = 0 then "0"
    else if String.get s 0 = '0' then trim (String.sub s 1 (String.length s -1))
    else s
  in trim s  
;;
