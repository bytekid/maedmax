class rewriter (trs : Rules.t) = object (self)
  val nf_table : (Term.t, Term.t * Rules.t) Hashtbl.t = Hashtbl.create 256

  method trs = trs

  (* Returns tuple (u, rs) of some normal form u of t that was obtained using
     rules rs *)
  method nf t = self#nf' [] t

  (* Returns tuple (u, rs@rs') where u is a normal form of t that was obtained
     using rules rs'. Lookup in table, otherwise compute. *)
  method nf' rs t = 
    try let u, urs = Hashtbl.find nf_table t in u, urs @ rs with
    Not_found -> (
      let u,urs = self#nf_compute t in
      Hashtbl.add nf_table t (u,urs); u, urs @ rs)

  (* Returns tuple (s, rs) where s is some normal form of t that was obtained
     using rules rs. Attempts doing a parallel step on t; if this yields a
     reduct u then recurse on nf' (to exploit table lookup), otherwise normal
     form was found. *)
  method nf_compute t =
    match self#pstep t with
      | _, [] -> t, []
      | u, rs' -> self#nf' rs' u 
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
        let opt, u = Rewriting.rewrite_at_root (Term.F (f, us)) trs in
        match opt with
          | None -> u, []
          | Some rl -> u, [rl]
        end
    ;;
end 