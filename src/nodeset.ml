module R = Rule

module Make(N:Node.T) = struct
  module H = UniqueHeap.Make(N)
module NL = Nodes.Make(N)

  type t = H.t

  let empty : t = H.empty

  let is_empty = H.is_empty

  let to_list = H.to_list

  let print ppf ns = H.iter (Format.fprintf ppf "@[%a@]\n%!" N.print) ns

  let print ppf ns = NL.print ppf (to_list ns)

  let printl ppf =
    Format.fprintf ppf "@[<v 0> %a@]" (Formatx.print_list N.print "\n ")

  let add n ns = H.insert n ns

  let merge = H.merge

  let add_list l ns = List.fold_left (fun ns n -> add n ns) ns l

  let of_list l = List.fold_left (fun ns n -> add n ns) empty l

  let diff = H.diff

  let terms ns = ns

  let symmetric_list = H.fold (fun l n -> n :: (N.flip n) :: l) []

  let filter = H.filter

  let fold = H.fold

  let iter = H.iter

  let select ns k th =
    let rec select sel ns k =
      if k<=0 || H.is_empty ns || Rule.size (N.rule (H.min ns)) >= th then
        (sel, ns)
      else
        let m,ns' = H.extract_min ns in
        select (add m sel) ns' (k-1)
    in select H.empty ns k
  ;;

  let min = H.min

  let size = H.size

  let for_all p = fold (fun r n -> r && (p n)) true

  (* quadratic *)
  let sym_varfree_list =
    let var n l = List.exists (fun e -> R.variant (N.rule n) (N.rule e)) l in
    let symadd n l = if var n l then l else n :: l in
    H.fold (fun l n -> symadd n (symadd (N.flip n) l)) []
  ;;

  let variant_free =
    let var n e = R.variant (N.rule n) (N.rule e) in
    let stop n e = R.size (N.rule e) > R.size (N.rule n) in
    let check_add h n = if H.exists (var n) (stop n) h then h else add n h in
    H.fold check_add empty
  ;;

  let unique = H.fold (fun ns n -> if H.mem n ns then ns else add n ns) empty

  let subsumption_free =
    let sub n n' = R.is_instance (N.rule n) (N.rule n') ||
                   R.is_instance (R.flip (N.rule n)) (N.rule n') in
    let stop n e = R.size (N.rule e) > R.size (N.rule n) in
    let check_add h n = if H.exists (sub n) (stop n) h then h else add n h in
    H.fold check_add empty
  ;;

  let add_unless_subsumed n ns =
    let generalization n n' =
      R.is_instance (N.rule n) (N.rule n') ||
      R.is_instance (R.flip (N.rule n)) (N.rule n')
    in
    let stop n e = R.size (N.rule e) > R.size (N.rule n) in
    if H.exists (generalization n) (stop n) ns then ns else add n ns 
  ;;

  let add_list_unless_subsumed l ns =
    List.fold_left (fun ns n -> add_unless_subsumed n ns) ns l
end
