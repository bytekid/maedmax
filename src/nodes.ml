open Prelude

module L = List
module Lit = Literal
module H = Hashtbl
module R = Rule

type t = (Literal.t, bool) Hashtbl.t

let empty () = H.create 128

let is_empty ns = H.length ns = 0

let size = H.length

let rec add n ns = if not (H.mem ns n) then H.add ns n true; ns

let rec remove n ns = H.remove ns n; ns

let add_all ns ns' = H.fold (fun n _ h -> add n h) ns ns'

let add_list l ns = L.fold_left (fun h n -> add n h) ns l

let of_list l = add_list l (H.create (L.length l * 2))

let of_termss ctx rs =
  let h = H.create (List.length rs * 2) in
  List.fold_left (fun h n -> add n h) h rs
;;

let symmetric ns =
  let nsc = H.copy ns in
  H.fold (fun n _ res -> add (Lit.flip n) res) ns nsc
;;

let to_list ns = H.fold (fun n _ l -> n::l) ns [] 

let cmp n1 n2 =
  let s1, s2 = Rule.size (Lit.terms n1), Rule.size (Lit.terms n2) in
  if s1 <> s2 then s1 - s2
  else
    let minsize (l,r) = min (Term.size l) (Term.size r) in
    minsize (Lit.terms n1) - (minsize (Lit.terms n2)) (* prefer equal size *)

let cmp_size n1 n2 = Rule.size (Lit.terms n1) - Rule.size (Lit.terms n2)

let smaller_than t ns =
  L.filter (fun n -> Rule.size (Lit.terms n) < t) (to_list ns)
;;
 
let sort_size = L.sort cmp_size
 
let sort_size_unif ns =
  let sorted = L.sort cmp_size ns in
  let unif,rest = L.partition Lit.is_unifiable sorted in
  unif @ rest
;;

let exists p ns = H.fold (fun n _ b -> b || p n) ns false

let filter p ns =
  H.fold (fun n _ ns' -> if not (p n) then H.remove ns' n; ns') ns (H.copy ns)
;;

let find p ns = H.fold (fun n _ x -> if p n then Some n else x) ns None

let for_all p ns = H.fold (fun n _ b -> b && p n) ns true

let variant_free ns =
  let h = Hashtbl.create (H.length ns * 2) in
  let var e e' = Rule.variant (Lit.terms e) (Lit.terms e') in
  H.fold (fun n _ hr -> if not (exists (var n) hr) then add n hr else hr) ns h 
;;

let subsumed n n' =
  let r, r' = Lit.terms n, Lit.terms n' in
  R.is_proper_instance r r' || R.is_proper_instance (R.flip r) r'
;;

let subsumption_free ns = filter (fun n -> not (exists (subsumed n) ns)) ns

let diff ns d = H.fold (fun n _ nsr -> remove n nsr) d ns 

let diff_list ns = L.fold_left (fun nsr n -> remove n nsr) ns

let print ppf ns = 
  let l = to_list ns in
  let rs = List.sort Pervasives.compare l in
  let print_list = Formatx.print_list (fun f n -> Lit.print f n) "\n " in
  Format.fprintf ppf "@[<v 0> %a@]" print_list rs

let iter f = H.iter (fun n _ -> f n)

let fold f = H.fold (fun n _ -> f n)

let rec add_unless_subsumed n ns =
  if not (exists (subsumed n) ns) then
    H.add ns n true
  else
    Format.printf "%a is subsumed by %a\n%!" Lit.print n Lit.print (match find (subsumed n) ns with Some x -> x | None -> failwith "boo");
  ns
;;

let add_list_unless_subsumed l ns =
  L.fold_left (fun h n -> add_unless_subsumed n h) ns l
;;

let ac_equivalence_free acs ns =
  if acs = [] then ns
  else
    let has_ac_eq l = L.exists (Lit.are_ac_equivalent acs l) in
    let rec eq_free = function
      | [] -> []
      | l :: ls -> if has_ac_eq l ls then eq_free ls else l :: (eq_free ls)
    in eq_free ns
;;

let c_equivalence_free acs ns =
  if acs = [] then ns
  else
    let has_ac_eq l = L.exists (Lit.are_c_equivalent acs l) in
    let rec eq_free = function
      | [] -> []
      | l :: ls -> if has_ac_eq l ls then eq_free ls else l :: (eq_free ls)
    in eq_free ns
;;
