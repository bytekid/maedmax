open Format

type 'a printer = Format.formatter -> 'a -> unit

let print_list pr sep ppf = function
  | [] -> ()
  | x :: xs ->
      pr ppf x;
      List.iter (fprintf ppf (sep ^^ "%a") pr) xs 

let print_eq pr1 pr2 ppf (x, ys) =
  fprintf ppf "@[%a =@ %a@]" (print_list pr1 " =@ ") ys pr2 x

let print_eqs pr1 pr2 ppf l =
  fprintf ppf "@[<hv 1>[%a]@]"
    (print_list (print_eq pr1 pr2) ";@ ") 
    (Listx.group (List.map (fun (x, y) -> (y, x)) l))
