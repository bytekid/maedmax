(*** MODULES ******************************************************************)
module L = Order.Logic
module F = Format
module BV = L.BitVector
module Sig = Signature
module Sub = Term.Sub

module Expr = struct
  open L

  type bv =
    | Var of Sig.var * int
    | HexConst of string * int (* value, bitwidth *)
    | Bv_not of bv
    | Bv_and of bv * bv
    | Bv_or of bv * bv
    | Bv_xor of bv * bv
    | Bv_neg of bv
    | Bv_add of bv * bv
    | Bv_sub of bv * bv
    | Bv_mult of bv * bv
    | Bv_udiv of bv * bv
    | Bv_sdiv of bv * bv
    | Bv_shl of bv * bv
    | Bv_ashr of bv * bv
    | Bv_lshr of bv * bv
    | Fun of string * int * bv list

  type boolean =
    | Top
    | Bot 
    | And of boolean * boolean
    | Or of boolean * boolean
    | Not of boolean
    | Equal of bv * bv
    | Bv_ult of bv * bv
    | Bv_ugt of bv * bv
    | Bv_ule of bv * bv
    | Bv_uge of bv * bv
    | Bv_slt of bv * bv
    | Bv_sgt of bv * bv
    | Bv_sle of bv * bv
    | Bv_sge of bv * bv
    | Pred of string * bv list

  exception Invalid_subst

  let rec print_bv ppf = function
    | Var (v, bits) -> F.fprintf ppf "%s.%d" (Sig.get_var_name v) bits
    | HexConst(c, bits) -> F.fprintf ppf "%s.%d" c bits
    | Bv_and(a, b) -> F.fprintf ppf "(%a & %a)" print_bv a print_bv b 
    | Bv_or(a, b) -> F.fprintf ppf "(%a | %a)" print_bv a print_bv b 
    | Bv_xor(a, b) -> F.fprintf ppf "(%a ^ %a)" print_bv a print_bv b 
    | Bv_not(a) -> F.fprintf ppf "! %a" print_bv a
    | Bv_neg(a) -> F.fprintf ppf "~ %a" print_bv a
    | Bv_add(a, b) -> F.fprintf ppf "(%a + %a)" print_bv a print_bv b  
    | Bv_sub(a, b) -> F.fprintf ppf "(%a - %a)" print_bv a print_bv b 
    | Bv_mult(a, b) -> F.fprintf ppf "(%a * %a)" print_bv a print_bv b 
    | Bv_udiv(a, b) -> F.fprintf ppf "(%a /u %a)" print_bv a print_bv b 
    | Bv_sdiv(a, b) -> F.fprintf ppf "(%a /s %a)" print_bv a print_bv b 
    | Bv_shl(a, b) -> F.fprintf ppf "(%a << %a)" print_bv a print_bv b 
    | Bv_ashr(a, b) -> F.fprintf ppf "(%a >>s %a)" print_bv a print_bv b 
    | Bv_lshr(a, b) -> F.fprintf ppf "(%a >>u %a)" print_bv a print_bv b 
    | Fun(n, b,es) ->
      F.fprintf ppf "%s.%d(%a)" n b (Formatx.print_list print_bv ",") es
  ;;

  let rec print ppf = function
    | Top -> F.fprintf ppf "T"
    | Bot -> F.fprintf ppf "F"
    | And(a, b) -> F.fprintf ppf "(%a /\\ %a)" print a print b 
    | Or(a, b) -> F.fprintf ppf "(%a \\/ %a)" print a print b 
    | Not(a) -> F.fprintf ppf "! %a" print a
    | Equal(a, b) -> F.fprintf ppf "(%a = %a)" print_bv a print_bv b 
    | Bv_ule(a, b) -> F.fprintf ppf "(%a <=u %a)" print_bv a print_bv b 
    | Bv_ult(a, b) -> F.fprintf ppf "(%a <u %a)" print_bv a print_bv b 
    | Bv_uge(a, b) -> F.fprintf ppf "(%a >=u %a)" print_bv a print_bv b 
    | Bv_ugt(a, b) -> F.fprintf ppf "(%a >u %a)" print_bv a print_bv b 
    | Bv_sle(a, b) -> F.fprintf ppf "(%a <=s %a)" print_bv a print_bv b 
    | Bv_slt(a, b) -> F.fprintf ppf "(%a <s %a)" print_bv a print_bv b 
    | Bv_sge(a, b) -> F.fprintf ppf "(%a >=s %a)" print_bv a print_bv b 
    | Bv_sgt(a, b) -> F.fprintf ppf "(%a >s %a)" print_bv a print_bv b 
    | Pred(n, es) ->
      F.fprintf ppf "%s(%a)" n (Formatx.print_list print_bv ",") es
  ;;

  let bit_width =
    let rec bw e =
      let bin a b = let i =bw a in if i = bw b then i else failwith "Expr.bw" in
      match e with
      | Var(_, i) -> i
      | HexConst(_, i) -> i
      | Bv_not e
      | Bv_neg e -> bw e
      | Bv_and(a, b)
      | Bv_or(a, b)
      | Bv_xor(a, b)
      | Bv_add(a, b)
      | Bv_sub(a, b)
      | Bv_mult(a, b)
      | Bv_udiv(a, b)
      | Bv_sdiv(a, b)
      | Bv_shl(a, b)
      | Bv_ashr(a, b)
      | Bv_lshr(a, b) -> bin a b
      | Fun(_, i, _) -> i
    in bw
  ;;

  let rename rho =
    let rec ren_bv = function
      | Var(x, i) as v -> (try
        match Sub.find x rho with
        | Term.V y -> Var(y, i)
        | _ -> raise Invalid_subst
        with Not_found -> v)
      | HexConst(_, _) as c -> c
      | Bv_not e -> Bv_not (ren_bv e)
      | Bv_neg e -> Bv_neg (ren_bv e)
      | Bv_and(a, b) -> Bv_and(ren_bv a, ren_bv b)
      | Bv_or(a, b) -> Bv_or(ren_bv a, ren_bv b)
      | Bv_xor(a, b) -> Bv_xor(ren_bv a, ren_bv b)
      | Bv_add(a, b) -> Bv_add(ren_bv a, ren_bv b)
      | Bv_sub(a, b) -> Bv_sub(ren_bv a, ren_bv b)
      | Bv_mult(a, b) -> Bv_mult(ren_bv a, ren_bv b)
      | Bv_udiv(a, b) -> Bv_udiv(ren_bv a, ren_bv b)
      | Bv_sdiv(a, b) -> Bv_sdiv(ren_bv a, ren_bv b)
      | Bv_shl(a, b) -> Bv_shl(ren_bv a, ren_bv b)
      | Bv_ashr(a, b) -> Bv_ashr(ren_bv a, ren_bv b)
      | Bv_lshr(a, b)  -> Bv_lshr(ren_bv a, ren_bv b)
      | Fun(n, i, es) -> Fun(n, i, List.map ren_bv es)
    in 
    let rec ren = function
      | And(a, b) -> And(ren a, ren b)
      | Or(a, b) -> Or(ren a, ren b)
      | Not(a) -> Not(ren a)
      | Equal(a, b) -> Equal(ren_bv a, ren_bv b)
      | Bv_ule(a, b) -> Bv_ule(ren_bv a, ren_bv b)
      | Bv_ult(a, b) -> Bv_ult(ren_bv a, ren_bv b)
      | Bv_uge(a, b) -> Bv_uge(ren_bv a, ren_bv b)
      | Bv_ugt(a, b) -> Bv_ugt(ren_bv a, ren_bv b)
      | Bv_sle(a, b) -> Bv_sle(ren_bv a, ren_bv b)
      | Bv_slt(a, b) -> Bv_slt(ren_bv a, ren_bv b)
      | Bv_sge(a, b) -> Bv_sge(ren_bv a, ren_bv b)
      | Bv_sgt(a, b) -> Bv_sgt(ren_bv a, ren_bv b)
      | Pred(n, es) -> Pred(n, List.map ren_bv es)
      | e -> e
    in ren
  ;;

  let variables e =
    let rec vars_bv = function
      | Var(x, b) -> [x,b]
      | HexConst(_, _) -> []
      | Bv_not e
      | Bv_neg e -> vars_bv e
      | Bv_and(a, b)
      | Bv_or(a, b)
      | Bv_xor(a, b)
      | Bv_add(a, b)
      | Bv_sub(a, b)
      | Bv_mult(a, b)
      | Bv_udiv(a, b)
      | Bv_sdiv(a, b)
      | Bv_shl(a, b)
      | Bv_ashr(a, b)
      | Bv_lshr(a, b)  -> vars_bv a @ (vars_bv b)
      | Fun(n, i, es) -> List.flatten (List.map vars_bv es)
    in 
    let rec vars = function
      | And(a, b)
      | Or(a, b) -> vars a @ (vars b)
      | Not(a) -> vars a
      | Equal(a, b)
      | Bv_ule(a, b)
      | Bv_ult(a, b)
      | Bv_uge(a, b)
      | Bv_ugt(a, b)
      | Bv_sle(a, b)
      | Bv_slt(a, b)
      | Bv_sge(a, b)
      | Bv_sgt(a, b) -> vars_bv a @ (vars_bv b)
      | Pred(n, es) -> List.flatten (List.map vars_bv es)
      | _ -> []
    in Listx.unique (vars e)
  ;;

  let expand_pred n es = 
    match n, es with
    | "isPowerOf2", [x] ->
      let b = bit_width x in
      let a = Equal (Bv_and (x, Bv_sub(x, HexConst("1",b))), HexConst("0",b)) in
      And(a, Not(Equal(x, HexConst("0",b))))
    | "isPowerOf2OrZero", [x] ->
      let b = bit_width x in
      Equal (Bv_and (x, Bv_sub(x, HexConst("1",b))), HexConst("0",b))
      | _ -> failwith ("Expr.expand_pred: unknown predicate" ^ n)
  ;;

  let expand_fun n bits es = 
    match n, es with
    | "computeKnownZeroBits", [x] -> x
    | "neg", [x] -> Bv_neg x
    | _ -> failwith ("Expr.expand_fun: unknown function " ^ n)
  ;;

  let to_logic ctx e =
    let rec of_bexpr ctx = function
      | Top -> L.mk_true ctx 
      | Bot -> L.mk_false ctx 
      | And(a, b) -> (of_bexpr ctx a) <&> (of_bexpr ctx b)
      | Or(a, b) -> (of_bexpr ctx a) <|> (of_bexpr ctx b)
      | Not(a) -> !! (of_bexpr ctx a)
      | Equal(a, b) -> (of_bvexpr ctx a) <=> (of_bvexpr ctx b) 
      | Bv_ule(a, b) -> BV.mk_ule (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_ult(a, b) -> BV.mk_ult (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_uge(a, b) -> BV.mk_uge (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_ugt(a, b) -> BV.mk_ugt (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_sle(a, b) -> BV.mk_sle (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_slt(a, b) -> BV.mk_slt (of_bvexpr ctx b) (of_bvexpr ctx a)
      | Bv_sge(a, b) -> BV.mk_sge (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_sgt(a, b) -> BV.mk_sgt (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Pred(n, es) -> of_bexpr ctx (expand_pred n es)
    and of_bvexpr ctx = function
      | Var(v, bits) -> BV.mk_var ctx (Sig.get_var_name v) bits
      | HexConst(c, bits) -> BV.mk_num ctx (Prelude.hex2bin c) bits
      | Bv_and(a, b) -> BV.mk_and (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_or(a, b) -> BV.mk_or (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_xor(a, b) -> BV.mk_xor (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_not(a) -> BV.mk_not (of_bvexpr ctx a)
      | Bv_add(a, b) -> BV.mk_add (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_sub(a, b) -> BV.mk_sub (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_neg(a) -> BV.mk_neg (of_bvexpr ctx a)
      | Bv_mult(a, b) -> BV.mk_mul (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_udiv(a, b) -> BV.mk_udiv (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_sdiv(a, b) -> BV.mk_sdiv (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_shl(a, b) -> BV.mk_shl (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Bv_ashr(a, b) -> BV.mk_ashr (of_bvexpr ctx a) (of_bvexpr ctx b) 
      | Bv_lshr(a, b) -> BV.mk_lshr (of_bvexpr ctx a) (of_bvexpr ctx b)
      | Fun(n, b, es) -> of_bvexpr ctx (expand_fun n b es)
    in
    (*Format.printf "2logic %a\n%!" print e;*)
    let r = of_bexpr ctx e in
    (*L.show r;*)
    r
  ;;
  
  let is_sat ctx e = 
    L.push ctx;
    L.require e;
    let sat = L.check ctx in
    L.pop ctx;
    sat
  ;;
  
  let is_valid ctx e = 
    L.push ctx;
    L.require (L.(!!) e);
    let unsat = not (L.check ctx) in
    L.pop ctx;
    unsat
  ;;

  let implies ctx a b = is_valid ctx (to_logic ctx (Or(Not a, b)))
end

module Equality = struct
  type t = Rule.t * Expr.boolean

  let print_with sep ppf ((l, r), c) =
    F.fprintf ppf "%a %s %a [%a]" Term.print l sep Term.print r Expr.print c
  ;;

  let print = print_with "="
end

module Literal = struct

  open Equality

  type t = {
    terms: Rule.t;
    constr: Expr.boolean;
    log_constr: L.t
  }

  let make rl c lc = { terms = rl; constr = c; log_constr = lc}

  let of_equation ctx (rl, e) = make rl e (Expr.to_logic ctx e)

  let constr l = l.constr

  let log_constr l = l.log_constr

  let terms l = l.terms

  let print f l = Equality.print f (l.terms, l.constr)

  let print_list = Formatx.print_list (fun f n -> print f n) "\n "

  let equal l l' = (l.terms = l'.terms && l.constr = l'.constr)

  let flip l = {l with terms = Rule.flip l.terms}

  let rename rho l = 
    let c' = Expr.rename rho l.constr in
    let lc' = Expr.to_logic (L.ctx l.log_constr) c' in
    make (Rule.substitute rho l.terms) c' lc'
  ;;

  (* check whether overlap candidate really produces overlap *)
  let overlap2cp (l1, p, l2, sigma) =
    try
      let c1s, c2s = Expr.rename sigma l1.constr, Expr.rename sigma l2.constr in
      let ctx = L.ctx l1.log_constr in
      let lc = Expr.to_logic ctx (And(c1s, c2s)) in
      if not (Expr.is_sat ctx lc) then (
        (*Format.printf "No overlap (unsat): %a and %a\n%!" print l1 print l2;*)
        None)
      else
        let s, t = Overlap.cp_of_overlap (l1.terms, p, l2.terms, sigma) in
        if s = t then None else Some (make (s, t) (And(c1s, c2s)) lc)
    with Expr.Invalid_subst -> 
      (*Format.printf "No overlap (invalid unifier): %a and %a\n%!"
          print l1 print l2;*)
      None
  ;;
  
  let overlaps_between l1 l2 =
    let overlap_at lt1 lt2 p =
      let (l1,_), (l2, _) = lt1.terms, lt2.terms in
      try Some (lt1, p, lt2, Subst.mgu (Term.subterm_at p l2) l1) with _ -> None
    in
      let rho = Rule.renaming_for (terms l2) in
      let l2r = rename rho l2 in
      let add acc p = match overlap_at l1 l2r p with
       | None -> acc
       | Some o -> o :: acc
      in
      let fpos = Term.function_positions (fst l2r.terms) in
      let fpos' = if equal l1 l2 then Listx.remove [] fpos else fpos in
      List.fold_left add [] fpos'
  ;;

  let overlaps_on l1 l2 =
    let ols = overlaps_between l1 l2 in
    let add os o = match overlap2cp o with Some e -> e :: os | _ -> os in
    List.fold_left add [] ols
  ;;

  let overlaps_on_below_root l l' = []

  let rewrite ctx l rs = (* one attempt with each rule on each side *)
    let rew_with_at (t, c) p rl =
      try
        let tau = Subst.pattern_match (fst (terms rl)) (Term.subterm_at p t) in
        let crls = Expr.rename tau rl.constr in
        let c1 = Expr.And(crls, c) in
        let c2 = Expr.And(Expr.Not crls, c) in
        if not (Expr.is_sat ctx (Expr.to_logic ctx c1)) then []
        else
          let u = Term.replace t (Term.substitute tau (snd (terms rl))) p in
          if Expr.implies ctx c crls then [u,c]
          else [t,c2; u, c1]
      with _ -> []
    in
    let rec rew l =
      let (s, t), c = l.terms, l.constr in
      let fpos = Term.function_positions t in
      let ts = List.flatten [ rew_with_at (t, c) p rl | p <- fpos; rl <- rs] in
      [ of_equation ctx ((s, u), c) | u, c <- ts; u <> s]
    and rewrite_all ls = List.flatten [ rew l | l <- ls] in
    match rew l with
    | [] -> rewrite_all [flip l]
    | rs ->
      let rs' = rewrite_all (List.map flip rs) in
      if rs' = [] then rs else (List.map flip rs')
  ;;

  let rec nf ctx l rs =
    match rewrite ctx l rs with
    | [] -> [l]
    | ls ->
      Format.printf "reducts of %a:\n%a%!" print l print_list ls;
      List.flatten [ nf ctx l rs | l <- ls]
  ;;
end

module Literals = struct
  type t = Literal.t list

  let symmetric ls = [ Literal.flip l | l <- ls] @ ls
end