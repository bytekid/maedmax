(*** MODULES *****************************************************************)
module L = List
module C = Cache
module F = Format
module Sig = Signature
module Logic = Settings.Logic
module Expr = Constrained.Expr

(*** OPENS *******************************************************************)
open Term
open Logic

(*** TYPES *******************************************************************)
type flags = {
 af : bool ref 
}

(*** GLOBALS *****************************************************************)
(* settings for LPO *)
let flags = { af = ref false }
(* signature *)
let funs = ref []
(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Sig.sym, Logic.t) Hashtbl.t = Hashtbl.create 32
(* map function symbol and strategy stage to variable expressing whether
   argument filtering for symbol is list *)

(* cache results of comparison *)
let gt_encodings : (int * Rule.t, Logic.t) Hashtbl.t = Hashtbl.create 512
let ge_encodings : (int * Rule.t, Logic.t) Hashtbl.t = Hashtbl.create 512
let eq_encodings : (int * Rule.t, Logic.t) Hashtbl.t = Hashtbl.create 512

(*** FUNCTIONS ***************************************************************)
let (<>>) = Int.(<>>)

let (<>=>) = Int.(<>=>)

let name = Sig.get_fun_name

let set_af _ = flags.af := true

let (<.>) f g x = f (g x)

let cache ht f k =
 try Hashtbl.find ht k with Not_found -> 
 let v = f k in Hashtbl.add ht k v; v
;;

let rec emb_geq s t = 
  match s, t with 
  | V x, V y when x = y -> true
  | F (f, ss), (F (g, ts) as t) when f = g ->
      L.exists (fun si -> emb_geq si t) ss || 
      L.for_all2 (fun si ti -> emb_geq si ti) ss ts
  | F (f, ss), t -> 
      L.exists (fun si -> emb_geq si t) ss
  | _ -> false
;;

let emb_gt s t = s <> t && emb_geq s t

(* lpo for yices *)

let prec i f = 
  try Hashtbl.find precedence (i,f) with
  Not_found ->
    failwith ("Lpo.prec: unknown symbol " ^ (name f) ^ ", " ^ (string_of_int i))
;;

let rec gt (ctx,i) s t phi =
  (*Format.printf "cmp %a %a %a\n" Term.print s Term.print t Expr.print phi;*)
  let vs = Expr.variables phi in
  let p = prec i in
  let rec ylpo_gt s t =
    let helper (i,(s,t)) =
      if emb_gt s t then mk_true ctx
      else if emb_geq t s then mk_false ctx
      else match s, t with
	      | F(f,ss), F(g,ts) ->
          let sub = big_or ctx [ ylpo_ge si t | si <- ss ] in
          if f = g then
            big_and1 (ylex ss ts :: [ ylpo_gt s ti | ti <- ts ]) <|> sub
          else
            big_and1 ((p f <>> (p g)) :: [ ylpo_gt s ti | ti <- ts ]) <|> sub
        | F _, V x when List.mem_assoc x vs -> mk_true ctx
        | _ -> mk_false ctx (* variable case already covered *)
    in cache gt_encodings helper (i,(s,t))
  and ylpo_ge s t = if s = t then mk_true ctx else ylpo_gt s t
  and ylex l1 l2 = match l1, l2 with
    | s :: ss, t :: ts when s = t -> ylex ss ts
    | s :: ss, t :: ts -> ylpo_gt s t
    | [], [] -> mk_false ctx
    | _ -> mk_true ctx
  in ylpo_gt s t

 and ge (ctx,i) s t phi =
  let rec ge (s,t) =
  if s = t then mk_true ctx else
  match s,t with
  | V x, V y ->
    let b =
      try List.assoc x (Expr.variables phi)
      with _ -> failwith "Crpo.ge: no such var"
    in
    let dec = Expr.implies ctx phi (Expr.Bv_uge(Var(x, b), Var(y, b))) in
    if dec then mk_true ctx else mk_false ctx
  | F(f,ss), F(g,ts) when f = g -> big_and ctx [ge p | p <-  Listx.zip ss ts]
  | _ -> gt (ctx,i) s t phi
  in ge (s,t)
;;

(* * OVERALL ENCODING * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

let make_fun_vars ctx k fs =
 let add f =
   let ki = string_of_int k in
   Hashtbl.add precedence (k,f) (Int.mk_var ctx ("lpo" ^ (name f) ^ "-" ^ ki))
 in L.iter add fs
;;

let init (ctx,k) fs =
  funs := fs;
  Hashtbl.clear precedence;
  let fs' = L.map fst fs in
  make_fun_vars ctx k fs';
  let bnd_0 = Int.mk_zero ctx in
  let bnd_n = Int.mk_num ctx (L.length fs') in
  let bounds f = let p = prec k f in (p <>=> bnd_0) <&> (bnd_n <>=> p) in
  (* total: causes stack overflow with too large signatures *)
  let total_prec =
    if List.length fs > 400 then mk_true ctx
    else
      let ps = [ f,g | f <- fs'; g <- fs'; f <> g ] in
      let p = prec k in
      big_and ctx [ !! (p f <=> (p g)) | f, g <- ps ]
  in
  big_and1 (total_prec :: [ bounds f | f <- fs' ])
;;

let decode_prec_aux k m =
 let add (k',f) x p =
   if k <> k' then p
   else (
     try
       let v = Int.eval m x in
       Hashtbl.add p f v; p
     with _ -> p)
 in Hashtbl.fold add precedence (Hashtbl.create 16)
;;

let eval_prec k m =
 let prec = Hashtbl.find (decode_prec_aux k m) in
 List.sort (fun (_, p) (_,q) -> p - q) [ (f,a), prec f | f,a <- !funs ]
;;

let prec_to_string = function
    [] -> ""
  | ((f,_),p) :: fp ->
    let s = "LPO \n " ^ (name f) in
    List.fold_left (fun s ((f,_),_) -> s ^ " < " ^ (name f)) s fp;
;;

let print_prec p = Format.printf "%s\n%!" (prec_to_string p)

let decode_print k m = print_prec (eval_prec k m)

let decode_term_gt k m =
 let prec = Hashtbl.find (decode_prec_aux k m) in
 let rec gt s t =
  if Term.is_subterm s t then false
  else if Term.is_subterm t s then true
  else
   match s,t with
    | V _, _
    | _, V _  -> false (* no subterm *)
    | F(f,ss), F(g,ts) ->
      let sub_gt = L.exists (fun si -> (gt si t) || (si = t)) ss in
      if f <> g then
       sub_gt || (prec f > prec g && L.for_all (gt s) ts)
      else (
       let lex (gt_lex,ge) (si,ti) = gt_lex || (ge && gt si ti), ge && si=ti in
       let lex_gt = fst (L.fold_left lex (false, true) (List.combine ss ts)) in
       sub_gt || (lex_gt && L.for_all (gt s) ts))
  in gt
;;

let decode_xml prec =
  let status_prec ((f,a),p) =
    let name = Xml.Element("name", [], [Xml.PCData (name f)]) in
    let arity = Xml.Element("arity", [], [Xml.PCData (string_of_int a)]) in
    let prec = Xml.Element("precedence", [], [Xml.PCData (string_of_int p)]) in
    let lex = Xml.Element("lex", [], []) in
    Xml.Element("statusPrecedenceEntry", [], [ name; arity; prec; lex] )
  in
  let w0 = Xml.Element("w0", [], [Xml.PCData "1"]) in
  let pw = Xml.Element("statusPrecedence", [], [ status_prec f | f <- prec ]) in
  Xml.Element("pathOrder", [], [ w0; pw ] )
;;

let print_params = function
    [] -> ()
  | ((f,_),p) :: fp ->
    Format.printf "-t LPO ";
    if fp <> [] then (
      Format.printf "--precedence=\"%s" (name f);
      List.iter (fun ((f,_),_) -> Format.printf "<%s" (name f)) fp;
      Format.printf "\"\n%!"
      )
  ;;

let encode i preclist ctx =
 let add ((f,_), p) = (prec i f <=> (Int.mk_num ctx p)) in
 Logic.big_and ctx (List.map add preclist)
;;

let decode k m =
  let gt = decode_term_gt k m in
  let cmp c d = if gt (Term.F(c,[])) (Term.F(d,[])) then d else c in
  let bot =  match [ c | c,a <- !funs; a = 0] with
      [] -> None
    | c :: cs -> Some (List.fold_left cmp c cs)
  in
  let prec = eval_prec k m in
  object
    method bot = bot
    method gt = gt
    method smt_encode = encode k prec
    method to_string = prec_to_string prec
    method print = fun _ -> print_prec prec
    method to_xml = decode_xml prec
    method print_params = fun _ -> print_params prec
  end
;;

let cond_gt i ctx conds s t =
  let p = prec i in
  let rec gt s t =
    if L.mem (s,t) conds || (emb_gt s t) then mk_true ctx
    else if emb_geq t s then mk_false ctx
    else match s, t with
	    | F(f,ss), F(g,ts) ->
        let sub = big_or ctx [ ylpo_ge si t | si <- ss ] in
        if f = g then
          big_and1 (ylex ss ts :: [ gt s ti | ti <- ts ]) <|> sub
        else
          big_and1 ((p f <>> (p g)) :: [ gt s ti | ti <- ts ]) <|> sub
      | _, F(g,ts) -> big_and ctx ([p f <>> (p g) | f,_ <- !funs; f <> g ] @
                                   (L.map (gt s) ts)) (* special hack *)
        | _ -> mk_false ctx (* variable case already covered *)
  and ylpo_ge s t = if s = t then mk_true ctx else gt s t
  and ylex l1 l2 = match l1, l2 with
    | s :: ss, t :: ts when s = t -> ylex ss ts
    | s :: ss, t :: ts -> gt s t
    | [], [] -> mk_false ctx
    | _ -> mk_true ctx
  in gt s t
;;

let clear () =
 Hashtbl.clear precedence;
 Hashtbl.clear gt_encodings; 
 Hashtbl.clear ge_encodings; 
 Hashtbl.clear eq_encodings
;;

