let rec init n f =
  let rec loop i =
    if i < n then f i :: loop (i + 1) else [] in
  loop 0 

let rec ix ?(i = 0) = function
  | [] -> []
  | x :: xs -> (i, x) :: ix ~i:(i + 1) xs

let rec unique = function
  | [] -> []
  | x :: xs -> x :: unique (List.filter (fun y -> x <> y) xs)

let rec copy n x =
  if n > 0 then x :: copy (n - 1) x else []

let pair x y = (x, y)

let product f xs ys =
  List.concat (List.map (fun x -> List.map (f x) ys) xs)

let cons x xs = x :: xs

let pi list = List.fold_right (product cons) list [[]]

let rec nth_power l = function
  | 0 -> [ [] ]
  | n -> product cons l (nth_power l (n-1))

let rec power = function
  | [] -> [ [] ]
  | x :: xs -> 
      let l = power xs in
      l @ List.map (cons x) l

let rec prefix = function
  | [] -> [ [] ]
  | x :: xs -> [] :: List.map (cons x) (prefix xs)

let rec suffix = function
  | [] -> [ [] ]
  | x :: xs -> (x :: xs) :: suffix xs

let interleave x ys =
  List.map2 (fun ls rs -> ls @ [x] @ rs) (prefix ys) (suffix ys)

let rec permutation = function
  | [] -> [ [] ]
  | x :: xs -> List.concat (List.map (interleave x) (permutation xs))

let rec group = function
  | [] -> []
  | (x,_) :: _ as l -> 
      let us, vs = List.partition (fun (u,_) -> x = u) l in
      (x, List.map snd us) :: group vs

let rec group_by f l = 
  group (List.map (fun x -> (f x, x)) l) 

let fold_left1 f = function
  | [] -> invalid_arg "Listx.fold_left1"
  | x :: xs -> List.fold_left f x xs

let rec count = function
  | [] -> []
  | x :: _ as l ->
      let xs, ys = List.partition (fun y -> x = y) l in
      (x, List.length xs) :: count ys

let rec transpose_aux n = function
  | [] -> copy n []
  | xs :: xss -> List.map2 (fun y ys -> y :: ys) xs (transpose_aux n xss)

let transpose = function
  | [] -> invalid_arg "transpose"
  | xs :: _ as l -> transpose_aux (List.length xs) l

(* list operations for integer lists. *)

let sum xs = List.fold_left (+) 0 xs

let max = function
  | [] -> invalid_arg "Listx.max"
  | x :: xs -> List.fold_left Pervasives.max x xs

let min = function
  | [] -> invalid_arg "Listx.min"
  | x :: xs -> List.fold_left Pervasives.min x xs

let rec interval a b =
  if a <= b then a :: interval (a + 1) b else []

let rec index ?(i = 0) = function
  | [] -> []
  | x :: xs -> (i, x) :: index ~i:(i + 1) xs

let rec take n l =
  if n <= 0 then [] else 
  match l with
  | [] -> invalid_arg "Listx.take"
  | x :: xs -> x :: take (n - 1) xs

let rec take_at_most n l =
  if n < 0 then [] else
  match n, l with
  | 0, _ -> []
  | _, [] -> []
  | n, x::xs -> x :: take_at_most (n-1) xs

let rec split_at_most n l =
  if n < 0 then [],l else
  match n, l with
  | 0, _ -> [],l
  | _, [] -> [],[]
  | n, x::xs -> let ys, rs = split_at_most (n-1) xs in x::ys, rs

let rec drop n l =
  if n <= 0 then l else 
  match l with
  | [] -> invalid_arg "Listx.drop"
  | x :: xs -> drop (n - 1) xs

let print f d xs =
 let fpf = Format.fprintf in
 let rec fprintf fmt = function
  | []    -> ()
  | [x]   -> fpf fmt "%a" f x
  | x::xs -> fpf fmt "%a%a%a" f x fpf d fprintf xs
 in
 fpf Format.std_formatter "@[%a@]@\n" fprintf xs
;;

let findi p l =
 let check (i,r) x = 
  match r with Some _ -> (i,r) 
   | None -> if p x then (i,Some x) else (i+1,None)
 in
 match List.fold_left check (0,None) (index l) with 
  _,None -> raise Not_found | i,Some x -> i
;;

let fprintfi f d fmt xs =
 let fpf = Format.fprintf in
 let rec fprintfi i fmt = function
  | []    -> ()
  | [x]   -> fpf fmt "%a" (f i) x
  | x::xs -> fpf fmt "%a%a%a" (f i) x fpf d (fprintfi (i+1)) xs
 in
 fpf fmt "@[%a@]" (fprintfi 0) xs
;;

let fprintf f d fmt = fprintfi (fun _ -> f) d fmt;;

let to_string f d l = 
 let rec to_string = function
  | [] -> ""
  | [x] -> f x
  | x :: xs -> f x ^ d ^ (to_string xs)
 in "[" ^ (to_string l) ^ "]"
;;


let print f d = Format.printf "@[%a@]" (fprintf f d)

let rec remove x = function
 | [] -> []
 | y :: ys when x = y -> ys
 | y :: ys -> y:: (remove x ys)
;;

let pos x =
 let rec pos i = function
  | [] -> failwith "Not_found"
  | y :: ys when x = y -> i
  | _ :: ys -> pos (i+1) ys
 in pos 0
 ;;