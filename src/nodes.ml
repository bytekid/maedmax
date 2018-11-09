open Prelude

module L = List
module Lit = Literal
module H = Hashtbl
module R = Rule

type t = (Literal.t, bool) Hashtbl.t

let empty () = H.create 128

let is_empty ns = H.length ns = 0

let size = H.length

let mem = H.mem

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

let to_rules ns = L.map Lit.terms (to_list ns)

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

let ages = ref 0
let age_table : (Rule.t,int) Hashtbl.t = Hashtbl.create 256

let reset_age _ =
  ages := 0;
  Hashtbl.clear age_table
;;

let age n =
  try Hashtbl.find age_table (Lit.terms n)
  with Not_found ->
    let a = !ages in
    ages := a + 1;
    Hashtbl.add age_table (Lit.terms n) a;
    a
;;

let max_age _ = Hashtbl.length age_table

let sort_size_age ns =
  let map_app n l = (n, Rule.size (Lit.terms n), age n) :: l in
  let nsx = List.fold_right map_app ns [] in
  let cmp (n1,s1,a1) (n2,s2,a2) =
    let d = s1 - s2 in if d <> 0 then d else a1 - a2
  in
  [ n | (n,_,_) <- L.sort cmp nsx ]
;;

let sort_size_diff ns =
  let diff n = let s,t = Lit.terms n in abs (Term.size s - Term.size t) in
  let nsx = [ n, Rule.size (Lit.terms n), diff n | n <- ns ] in
  let cmp (n1,s1,a1) (n2,s2,a2) =
    let d = s1 - s2 in if d <> 0 then d else a1 - a2
  in
  [ n | (n,_,_) <- L.sort cmp nsx ]
;;

let exists p ns = H.fold (fun n _ b -> b || p n) ns false

let filter p ns =
  H.fold (fun n _ ns' -> if not (p n) then H.remove ns' n; ns') ns (H.copy ns)
;;

let partition p ns =
  let add n _ (ps,qs) = (if p n then H.add ps else H.add qs) n true; (ps,qs) in
  H.fold add ns (empty (), empty ())
;;

let find p ns = H.fold (fun n _ x -> if p n then Some n else x) ns None

let avg_size ns =
  if is_empty ns then 0
  else (H.fold (fun n _ s -> Lit.size n + s) ns 0) / size ns

let for_all p ns = H.fold (fun n _ b -> b && p n) ns true

let subset ns1 ns2 = for_all (mem ns2) ns1

let equal ns1 ns2 = subset ns1 ns2 && subset ns2 ns1

let variant_free ns =
  let h = Hashtbl.create (H.length ns * 2) in
  let var e e' = Rule.variant (Lit.terms e) (Lit.terms e') in
  H.fold (fun n _ hr -> if not (exists (var n) hr) then add n hr else hr) ns h 
;;

let subsumption_free : t -> t =
  let instantiated = R.is_proper_instance in
  let subsumed_by r r' = instantiated r r' || instantiated (R.flip r) r' in
  let rec exists_subsumed (n, sz) = function
    | [] -> false
    | (n', sz') :: _ when sz' > sz -> false
    | (n', sz') :: ns -> subsumed_by n n' || exists_subsumed (n, sz) ns
  in
  let sfree ns =
    let nsl = [Lit.terms n, Lit.size n | n <- to_list ns] in
    let nsl = List.sort (fun (n1, s1) (n2, s2) -> s1 - s2) nsl in
    filter (fun n -> not (exists_subsumed (Lit.terms n, Lit.size n) nsl)) ns
  in
  Analytics.take_time Analytics.t_subsumption sfree
;;

let filter_out p ns =
  let rest = empty () in
  let filter n _ = if p n then (let _ = remove n ns in ignore (add n rest)) in
  H.iter filter ns;
  ns, rest
;;

let diff ns d = H.fold (fun n _ nsr -> remove n nsr) d ns 

let diff_list ns = L.fold_left (fun nsr n -> remove n nsr) ns

let print_list ppf l =
  let rs = List.sort Pervasives.compare l in
  let print_list = Formatx.print_list (fun f n -> Lit.print f n) "\n " in
  Format.fprintf ppf "@[<v 0> %a@]" print_list rs
;;

let print ppf ns = print_list ppf (to_list ns)

let iter f = H.iter (fun n _ -> f n)

let fold f = H.fold (fun n _ -> f n)

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
