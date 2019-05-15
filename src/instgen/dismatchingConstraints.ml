type t = Settings.dismatching_constraints

let is_ok sigma (ss, ts) =
  (ss = [] && ts = []) ||
  not (Subst.are_instances_of ss [ Term.substitute sigma ti | ti <- ts])
;;

let is_ok_for sigma = List.for_all (fun c -> is_ok sigma c)

let print1 ppf (ss, ts) =
  Format.fprintf ppf "(%a) !|> (%a)"
    (Formatx.print_list Term.print ", ") ss
    (Formatx.print_list Term.print ", ") ts
;;

let print ppf = function
  | [] -> Format.fprintf ppf ""
  | [c] -> Format.fprintf ppf "[%a]%!" print1 c
  | cs -> Format.fprintf ppf "[%a]%!" (Formatx.print_list print1 ", ") cs
;;
