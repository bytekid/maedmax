module T = Term;;
module L = List;;
module H = Hashtbl;;

module Fingerprint = struct
  type feature = Sym of Signature.sym | A | B | N

  type t = feature list

  let poss = [[]; [0]; [1]] (* fixed for now *)

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
    | Sym f -> Signature.get_fun_name f
    | A -> "A"
    | B -> "B"
    | N -> "N"
  ;;

  let to_string = L.fold_left (fun s f -> s ^ "." ^ (feature_string f)) ""
end

module FingerprintIndex = struct
  module F = Fingerprint

  type t = Leaf of Rules.t | Node of (F.feature, t) H.t

  let rec to_string = function
    | Leaf rs -> "[" ^ (string_of_int (List.length rs)) ^ "]"
    | Node h -> Hashtbl.fold (fun f t r -> (F.feature_string f) ^ " -> @[" ^ (to_string t) ^"@]\n"^ r) h ""
  ;;

  let rec print ppf = function
    | Leaf rs -> Format.fprintf ppf "[%d]%!" (List.length rs)
    | Node h ->
      let fs = F.feature_string in
      let binding f t = Format.fprintf ppf " %s -> (@[ %a@])\n" (fs f) print t in
      Hashtbl.iter binding h
  ;;

  let empty = Leaf []

  let is_empty = function Leaf [] -> true | _ -> false

  let insert trie rule =
    (*Format.printf "Insert %a into \n%a\n" Term.print (fst rule) print trie;*)
    let rec insert fs trie = match fs, trie with
      | [], Leaf rs -> Leaf (rule :: rs)
      | f :: fs', Leaf [] ->
        let h = H.create 16 in
        H.add h f (insert fs' (Leaf []));
        Node h
      | f :: fs', Node h -> (
        try Hashtbl.replace h f (insert fs' (H.find h f)); Node h
        with Not_found -> (H.add h f (insert fs' (Leaf [])); Node h))
      | _ -> failwith ("FingerprintIndex insertion: unexpected pattern" ^ (F.to_string fs) ^ " and " ^ (to_string trie))
    in let res = insert (F.of_term (fst rule)) trie in
    (*Format.printf "...yields\n%a\n" print res;*)
    res
  ;;

  let create = L.fold_left insert empty

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

  let get_matches t = Statistics.take_time Statistics.t_tmp2 (get_matches t)

  let get_overlaps t trie =
    let rec retrieve fs0 = function
      | Leaf rs -> assert (fs0 = []); rs
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
    in retrieve (F.of_term t) trie
  ;;
end


class rewriter (trs : Rules.t) = object (self)
  val nf_table : (Term.t, Term.t * Rules.t) H.t = H.create 256
  val index = FingerprintIndex.create trs

  method trs = trs

  (* Returns tuple (u, rs) of some normal form u of t that was obtained using
     rules rs *)
  method nf t = self#nf' [] t

  let nf t = Statistics.take_time Statistics.t_tmp1 (insert trie)

  (* Returns tuple (u, rs@rs') where u is a normal form of t that was obtained
     using rules rs'. Lookup in table, otherwise compute. *)
  method nf' rs t = 
    try let u, urs = H.find nf_table t in u, urs @ rs with
    Not_found -> (
      let u,urs = self#nf_compute t in
      H.add nf_table t (u,urs); u, urs @ rs)

  (* Returns tuple (s, rs) where s is some normal form of t that was obtained
     using rules rs. Attempts doing a parallel step on t; if this yields a
     reduct u then recurse on nf' (to exploit table lookup), otherwise normal
     form was found. *)
  method nf_compute t =
    match self#pstep t with
      | _, [] -> t, []
      | u, rs' -> self#nf' rs' u 
    ;;

  method check t =
   let rs = L.filter (fun (l,_) -> Subst.is_instance_of t l) trs in
   let rs' = FingerprintIndex.get_matches t index in
   assert (Listset.subset rs rs')
  ;;

  (* Tries to do a parallel step on argument. Returns tuple (s, rs) where either
     s is a parallel-step innermost reduct of t that was obtained using rules rs
     or s=t and rs=[] if t is in normal form. *)
  method pstep = function
    | Term.V _ as t -> t, []
    | Term.F (f, ts) ->
      let concat (us,rs) ti = let ui,rsi = self#pstep ti in (us@[ui], rsi@rs) in
      let us, urs = List.fold_left concat ([], []) ts in
      if urs <> [] then Term.F (f, us), urs
      else (* step in arguments not possible, attempt root step *)
        begin
        (*self#check (Term.F (f, us));*)
        let rs = FingerprintIndex.get_matches (Term.F (f, us)) index in
        let opt, u = Rewriting.rewrite_at_root (Term.F (f, us)) rs in
        match opt with
          | None -> u, []
          | Some rl -> u, [rl]
        end
    ;;
end 