module H = Hashtbl

let empty _ = H.create 256

let singleton x = H.add (empty ()) x true

let is_empty xs = H.length xs = 0

let add x xs = 
  if not (H.mem xs x) then H.add xs x true; xs

let remove x xs = H.remove xs x; xs

let add_all xs ys = H.fold (fun x _ zs -> add x zs) xs ys

(* xs - ys *)
let diff xs ys = H.fold (fun y _ xs' -> remove y xs') ys xs

let filter2new p xs =
  H.fold (fun x _ ys -> if p x then add x ys else ys) xs (empty ())
;;

let of_list l = List.fold_left (fun h x -> add x h) (empty ()) l

let map_to_list f h = H.fold (fun x _ l -> f x :: l) h []
