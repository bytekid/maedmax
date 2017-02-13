open Prelude

module L = List

module Make(N:Node.T) = struct
  type t = N.t list

  let rec insert combine n = function
      [] -> [n]
    | n' :: ns -> (match combine n n' with
        None -> n' :: (insert combine n ns)
      | Some n'' -> n'' :: ns)
  ;;

  let unique ns = L.fold_left (flip (insert N.combine)) ns []

  let union ns ns' = L.fold_left (flip (insert N.combine)) ns ns'

  let unique_subsumed ns = L.fold_left (flip (insert N.combine_subsumed)) ns []

  let cps ns = unique [ n | n1 <- ns; n2 <- ns; n <- N.cps n1 n2 ]

  let is_trivial = L.for_all N.is_trivial

  let map f = L.map f

  let normalize = map N.normalize

  let flip = map N.flip

  let terms = map N.rule

  let of_rules ctx = map (N.of_rule ctx)

  let unq_filter f = List.filter (f <.> N.terms) <.> Listx.unique

  let reduce ns =
    let nf = Rewriting.nf (terms ns) in
    let rec red acc = function
     | [] -> acc
     | n :: ns ->
       let l,r = N.rule n in
       if Rewriting.nf (terms acc) l = l then red (n :: acc) ns
       else red acc ns
    in red [] (map (N.rule_map (fun (l,r) -> (l, nf r))) ns)
  ;;

  let symmetric ns = L.rev_append ns (flip ns) 

  let sort_smaller_than t ns = 
    let small = L.filter (fun n -> Rule.size (N.rule n) < t) ns in
    let sort_by f = L.sort (fun x y -> f x - f y) in
    sort_by (Rule.size <.> N.rule) small
  ;;

  let rec variant_free = function
     [] -> []
   | e :: ee ->
     if List.exists (fun e' -> Rule.variant (N.rule e) (N.rule e')) ee then
       variant_free ee
     else
       e :: (variant_free ee)
  ;;


  let print ppf ns =
    let rs = List.sort Pervasives.compare ns in
    Format.fprintf ppf "@[<v 0> %a@]" (Formatx.print_list N.print "\n ") rs
end
