class rewriter (trs : Rules.t) = object (self)
  val nf_table : (Term.t, Term.t * Rules.t) Hashtbl.t = Hashtbl.create 256

  method trs = trs

  method nf t = self#nf' [] t

  method nf' rs t = 
    try let u, urs = Hashtbl.find nf_table t in u, urs @ rs with
    Not_found -> (
      let u,urs = self#nf_compute t in
      Hashtbl.add nf_table t (u,urs); u, urs @ rs)

  method nf_compute t =
    match self#pstep t with
      | _, [] -> t, []
      | u, rs' -> self#nf' rs' u 
    ;;

  method pstep = function
    | Term.V _ as t -> t, []
    | Term.F (f, ts) ->
      let concat (us,rs) ti = let ui,rsi = self#pstep ti in (us@[ui], rsi@rs) in
      let us, urs = List.fold_left concat ([], []) ts in
      if urs <> [] then Term.F (f, us), urs
      else
        begin
        let opt, u = Rewriting.rewrite_at_root (Term.F (f, us)) trs in
        match opt with
          | None -> u, []
          | Some rl -> u, [rl]
        end
    ;;
end 