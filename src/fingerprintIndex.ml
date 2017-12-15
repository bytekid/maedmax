module T = Term
module L = List
module H = Hashtbl
module Sig = Signature
module Ac = Theory.Ac

module Fingerprint = struct
  type feature = Sym of Sig.sym | A | B | N

  type t = feature list

  let poss = [[]; [0]; [1]; (*[0;0]; [1;0]*)] (* fixed for now *)

  let rec feature_of_term t p =
    match p, t with
      | [], T.V _ -> A
      | [], T.F (f,_) -> Sym f
      | _, T.V _ -> B
      | i :: q, T.F (_,ts) when i < L.length ts -> feature_of_term (L.nth ts i) q
      | _ -> N (* non-root position, not in t *)
  ;;

  let of_term t = L.map (feature_of_term t) poss

  let feature_string = function
    | Sym f -> Sig.get_fun_name f
    | A -> "A"
    | B -> "B"
    | N -> "N"
  ;;

  let to_string = L.fold_left (fun s f -> s ^ "." ^ (feature_string f)) ""
end

module F = Fingerprint

type 'a t = Leaf of 'a | Node of (F.feature, 'a t) H.t

let rec to_string = function
  | Leaf rs -> "[" ^ (string_of_int (L.length rs)) ^ "]"
  | Node h -> Hashtbl.fold (fun f t r -> (F.feature_string f) ^ " -> @[" ^ (to_string t) ^"@]\n"^ r) h ""
;;

let rec print ppf = function
  | Leaf rs -> Format.fprintf ppf "[%d]%!" (L.length rs)
  | Node h ->
    let fs = F.feature_string in
    let binding f t = Format.fprintf ppf " %s -> (@[ %a@])\n" (fs f) print t in
    Hashtbl.iter binding h
;;

let empty = Leaf []

let is_empty = function Leaf [] -> true | _ -> false

let insert trie (term, value) =
  let rec insert fs trie = match fs, trie with
    | [], Leaf rs -> Leaf (value :: rs)
    | f :: fs', Leaf [] ->
      let h = H.create 16 in
      H.add h f (insert fs' (Leaf []));
      Node h
    | f :: fs', Node h -> (
      try Hashtbl.replace h f (insert fs' (H.find h f)); Node h
      with Not_found -> (H.add h f (insert fs' (Leaf [])); Node h))
    | _ -> failwith ("FingerprintIndex insertion: unexpected pattern" ^ (F.to_string fs) ^ " and " ^ (to_string trie))
  in let res = insert (F.of_term term) trie in
  (*Format.printf "insert %a with %s yields %a\n%!" Term.print term (F.to_string (F.of_term term)) print res;*)
  res
;;

let create xs = L.fold_left insert empty xs

let get_matches t trie =
  let rec retrieve fs0 = function
    | Leaf rs -> assert (fs0 = []); rs
    | Node h ->
      let ret f fs = try retrieve fs (H.find h f) with Not_found -> [] in
      match fs0 with
        | F.Sym f :: fs -> ret (F.Sym f) fs @ ret F.A fs @ ret F.B fs
        | F.A :: fs -> ret F.A fs @ ret F.B fs
        | F.B :: fs -> ret F.B fs
        | F.N :: fs -> ret F.B fs @ ret F.N fs
        | _ -> failwith "FingerprintIndex matches: too short fingerprint"
  in
  if is_empty trie then [] else retrieve (F.of_term t) trie
;;

let get_unifiables t trie =
  let rec retrieve fs0 = function
    | Leaf rs -> rs
    | Node h ->
      let ret f fs = try retrieve fs (H.find h f) with Not_found -> [] in
      match fs0 with
        | F.Sym f :: fs -> ret (F.Sym f) fs @ ret F.A fs @ ret F.B fs
        | F.A :: fs -> (* all symbols, A, and B *)
          H.fold (fun k t rs -> if k = F.N then rs else retrieve fs t @ rs) h []
        | F.B :: fs -> (* follow all features *)
          H.fold (fun k t rs -> retrieve fs t @ rs) h []
        | F.N :: fs -> ret F.B fs @ ret F.N fs
        | _ -> failwith "FingerprintIndex overlaps: too short fingerprint"
  in let res = retrieve (F.of_term t) trie in
  (*Format.printf "%d results for %a in %a\n%!" (List.length res) Term.print t print trie;*)
  res
;;
