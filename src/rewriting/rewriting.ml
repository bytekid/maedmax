open Term

let rec rewrite_at_root t = function
  | [] -> None, t
  | (l, r) :: rules ->
      try
	Some (l,r), substitute (Subst.pattern_match l t) r
      with
	Subst.Not_matched -> rewrite_at_root t rules

let rec rewrite_aux rules = function
  | V _ as t -> [], t
  | F (f, ts) ->
      let tpls = [ rewrite_aux rules ti | ti <- ts ] in
      let ls = [ ti | _, ti <- tpls ] in
      let used_rules = Listx.unique (List.flatten (List.map fst tpls)) in 
      if used_rules <> [] then used_rules, F (f, ls)
      else
       let opt, u = rewrite_at_root (F (f, ls)) rules in
       match opt with
        | None -> used_rules, u
        | Some lr -> 
	  if List.mem lr used_rules 
	  then used_rules, u else (lr :: used_rules), u

let step_at_with t p (l,r) =
  let ti = Term.subterm_at p t in
  Term.replace t (substitute (Subst.pattern_match l ti) r) p 
;;

let reducts trs t =
  let step p rl = try [ step_at_with t p rl ] with Subst.Not_matched -> [] in
  let step_at p = List.concat [ step p rl | rl <- trs ] in
  List.concat [ step_at p | p <- Term.positions t ]
;;


let rec nf rules t =
 let used, u = rewrite_aux rules t in
 match used with 
 | [] -> t
 | _ -> nf rules u

let reducible_with rules t =
 let used, _ = rewrite_aux rules t in
 match used with
 | [] -> false
 | _ -> true
;;

let nf_with rules t =
 let rec nf acc rules t =
  let used, u = rewrite_aux rules t in
  match used with
   | [] -> acc,t
   | ls -> nf (ls@acc) rules u
 in nf [] rules t

let nf_with_at rules t =
  let opt_fold f =
    List.fold_left (fun r x -> match r with None -> f x | _ -> r) None
  in
  let reduct t =
    let step p rl = try Some (step_at_with t p rl,p,rl) with _ -> None in
    let step_at p = opt_fold (step p) rules in
    opt_fold step_at (Term.positions t)
  in
  let rec nf acc t =
    match reduct t with
    | None -> List.rev acc,t
    | Some (u,p,rl) -> nf ((rl,p) :: acc) u
  in nf [] t
;;

let nf_with_ht ht rules t =
 try Hashtbl.find ht t with
 Not_found -> (
  let res = nf_with rules t in
  Hashtbl.add ht t res;
  res )
;;

let u_nf rules t =
  let rec rpt acc trm =
    let used, u = rewrite_aux rules trm in
    if used = [] then acc, trm
    else rpt (used @ acc) u
  in
  let ls, nf_t = rpt [] t in
  match ls with
  | [] -> None, t
  | _ -> Some (Listx.unique ls), t

