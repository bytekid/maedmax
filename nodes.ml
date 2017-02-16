open Prelude

module L = List
module H = Hashtbl
module R = Rule

module Make(N:Node.T) = struct
  type t = (N.t,bool) H.t

  let empty () = H.create 128

  let is_empty ns = H.length ns = 0

  let size = H.length

  let rec add n ns = if not (H.mem ns n) then H.add ns n true; ns

  let rec remove n ns = H.remove ns n; ns

  let add_all ns ns' = H.fold (fun n _ h -> add n h) ns ns'

  let add_list l ns = L.fold_left (fun h n -> add n h) ns l

  let of_list l = add_list l (H.create (L.length l * 2))

  (*let unique_subsumed ns = L.fold_left (flip (insert N.combine_subsumed)) ns []*)

  let of_rules ctx rs =
    let h = H.create (List.length rs * 2) in
    List.fold_left (fun h n -> add n h) h rs
  ;;

  let symmetric ns =
    let nsc = H.copy ns in
    H.fold (fun n _ res -> add (N.flip n) res) ns nsc
  ;;

  let to_list ns = H.fold (fun n _ l -> n::l) ns [] 

  let cmp n1 n2 =
    let s1, s2 = Rule.size (N.rule n1), Rule.size (N.rule n2) in
    if s1 <> s2 then s1 - s2
    else
      let minsize (l,r) = min (Term.size l) (Term.size r) in
      minsize (N.rule n1) - (minsize (N.rule n2)) (* prefer equal size terms *)

  let cmp n1 n2 = Rule.size (N.rule n1) - Rule.size (N.rule n2)

  let mul_gt gt ts1 ts2 =
    let ts1' = Listset.diff ts1 ts2 in
    let ts2' = Listset.diff ts2 ts1 in
    List.for_all (fun t -> List.exists (fun s -> gt s t) ts1') ts2'
  ;;

  let cmp_gt gt n1 n2 =
    let s1, s2 = Rule.size (N.rule n1), Rule.size (N.rule n2) in
    if s1 <> s2 then s1 - s2
    else(
      let (l1,r1),(l2,r2) = N.rule n1, N.rule n2 in
      let lr,rl = mul_gt gt [l2;r2] [l1;r1], mul_gt gt [l1;r1] [l2;r2] in
      let r = if lr then -1 else if rl then 1 else 0 in
      Format.printf "%a > %a: %d\n%!" Rule.print (l1,r1) Rule.print (l2,r2) r;
      r)
  ;;

  let sort_smaller_than t ns = 
    let l = to_list ns in
    let small = L.filter (fun n -> Rule.size (N.rule n) < t) l in
    L.sort cmp small
  ;;

  let filter p ns =
    let h = Hashtbl.create (H.length ns * 2) in
    H.fold (fun n _ res -> if p n then add n res else res) ns h
  ;;

  let exists p ns = H.fold (fun n _ b -> b || p n) ns false

  let for_all p ns = H.fold (fun n _ b -> b && p n) ns true

  let variant_free ns =
    let h = Hashtbl.create (H.length ns * 2) in
    let var e e' = Rule.variant (N.rule e) (N.rule e') in
    H.fold (fun n _ hr -> if not (exists (var n) hr) then add n hr else hr) ns h 
  ;;

  let subsumption_free ns =
    let h = Hashtbl.create (H.length ns * 2) in
    let sub n n' =
      let r, r' = N.rule n, N.rule n' in
      R.is_instance r r' || R.is_instance (R.flip r) r'
    in
    H.fold (fun n _ hr -> if not (exists (sub n) hr) then add n hr else hr) ns h 
  ;;

  let diff ns d = H.fold (fun n _ nsr -> remove n nsr) d ns 

  let diff_list ns dl = L.fold_left (fun nsr n -> remove n nsr) ns dl 

  let print ppf ns = 
    let l = to_list ns in
    let rs = List.sort Pervasives.compare l in
    Format.fprintf ppf "@[<v 0> %a@]" (Formatx.print_list N.print "\n ") rs

  let iter f = H.iter (fun n _ -> f n)

  let fold f = H.fold (fun n _ -> f n)
end
