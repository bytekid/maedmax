module T = Term
module L = List
module H = Hashtbl
module Sig = Signature
module Ac = Theory.Ac

type term_cmp = Term.t -> Term.t -> bool

exception Not_orientable

class rewriter (trs : Rules.t) (acs : Sig.sym list) (order : Order.t) =
  object (self)

  val nf_table : (Term.t, Term.t * ((Rule.t*Term.pos) list)) H.t = H.create 256
  val mutable index = FingerprintIndex.empty

  method init () =
    let cs = [ Ac.commutativity f | f <- acs] in
    let cas = [ Ac.cassociativity f | f <- acs] in
    let eqs = [ l, ((l,r), false)| l,r <- cs @ cas ] in
    let rules = [ l,((l,r), true) | l,r <- trs ] in
    index <- FingerprintIndex.create (eqs @ rules)

  method trs = trs
  
  method order : Order.t = order

  method add es =
    let cs = [ Ac.commutativity f | f <- acs] in
    let cas = [ Ac.cassociativity f | f <- acs] in
    let es' = es @ [r,l | l,r <- es ] in
    let eqs = [ l, ((l,r), false)| l,r <- cs @ cas @ es' ] in
    let rules = [ l,((l,r), true) | l,r <- trs ] in
    index <- FingerprintIndex.create (eqs @ rules)

  method add_more es =
    let es' = es @ [r,l | l,r <- es ] in
    let eqs = [ l, ((l,r), false)| l,r <- es' ] in
    index <- L.fold_left FingerprintIndex.insert index eqs;
    Hashtbl.clear nf_table

  (* Returns tuple (u, rs) of some normal form u of t that was obtained using
     rules rs *)
  method nf t = self#nf' [] t

  (* Returns tuple (u, rs@rs') where u is a normal form of t that was obtained
     using rules rs'. Lookup in table, otherwise compute. *)
  method nf' rs t = 
    try let u, urs = H.find nf_table t in u, rs @ urs with
    Not_found -> (
      let u,urs = self#nf_compute t in
      H.add nf_table t (u,urs); u, rs @ urs)

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
   let eqs = Ac.eqs acs in
   let rs = L.filter (fun (l,_) -> Subst.is_instance_of t l) (trs @ eqs) in
   let rs' = L.map fst (FingerprintIndex.get_matches t index) in
   assert (Listset.subset rs rs')
  ;;

  method rewrite_at_root_with t ((l, r), b) =
    let lsub,rsub = Rule.substitute (Subst.pattern_match l t) (l,r) in
    if b then Some (l,r), rsub
    else
      let rho = match order#bot with
          None -> []
        | Some c -> let vs = Listset.diff (T.variables r) (T.variables l) in
          [ x, T.F(c,[]) | x <- vs ]
      in
      let rsub = Term.substitute rho rsub in
      if order#gt lsub rsub then Some (l,r), rsub
      else raise Not_orientable
  ;;

  (* FIXME: so far only for equations with same variables on both sides *)
  method rewrite_at_root t = function
    | [] -> None, t
    | ((l, r), b) :: rules -> (
      if !(Settings.do_assertions) then
        assert (Rule.is_rule (l,r));
      try self#rewrite_at_root_with t ((l, r), b)
      with _ -> self#rewrite_at_root t rules)
  ;;

  (* Tries to do a parallel step on argument. Returns tuple (s, rs) where either
     s is a parallel-step innermost reduct of t that was obtained using rules rs
     or s=t and rs=[] if t is in normal form. *)
  method pstep = function
    | Term.V _ as t -> t, []
    | Term.F (f, ts) ->
      let concat (us,rs) (i,ti) =
        let ui,rsi = self#pstep ti in 
        let rsi = L.map (fun (rl,p) -> rl,i::p) rsi in
        us @ [ui], rs @ rsi
      in
      let us, urs = L.fold_left concat ([], []) (Listx.index ts) in
      if urs <> [] then Term.F (f, us), urs
      else (* step in arguments not possible, attempt root step *)
        begin
        if !(Settings.do_assertions) then
          self#check (Term.F (f, us));
        let rs = FingerprintIndex.get_matches (Term.F (f, us)) index in
        let opt, u = self#rewrite_at_root (Term.F (f, us)) rs in
        match opt with
          | None -> u, []
          | Some rl -> u, [rl,[]]
        end
  ;;

  (* only to reconstruct rewrite sequences *)
  method rewrite_at_with t rl p =
    let t' = Term.subterm_at p t in
    let _, ti' =
      try self#rewrite_at_root_with t' (rl, false)
      with Subst.Not_matched -> self#rewrite_at_root_with t' (rl, false)
    in Term.replace t ti' p
  ;;

  method is_nf t =
    self#nf t = (t, [])
  ;;

  method is_nf_below_root = function
      Term.V _ -> true
    | Term.F (_, ts) -> List.for_all self#is_nf ts
  ;;
end
