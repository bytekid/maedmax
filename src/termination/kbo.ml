(*** MODULES *****************************************************************)
module L = List
module T = Term
module C = Cache
module Sig = Signature
module Logic = Settings.Logic

(*** OPENS *******************************************************************)
open Term
open Logic
open Settings

(*** GLOBALS *****************************************************************)
(* signature *)
let funs = ref []

(* map function symbol and strategy stage to variable for weight *)
let weights : (int * Sig.sym, Logic.t) Hashtbl.t = Hashtbl.create 32

(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Sig.sym, Logic.t) Hashtbl.t = Hashtbl.create 32

(* map function symbol and strategy stage to variable expressing whether
   argument filtering for symbol is list *)
let af_is_list : (int * Sig.sym, Logic.t) Hashtbl.t = Hashtbl.create 32
(* variable whether argument position for symbol is contained in filtering *)
let af_arg : ((int * Sig.sym) * int, Logic.t) Hashtbl.t = Hashtbl.create 64

(*** FUNCTIONS ***************************************************************)
let (<>>) = Int.(<>>)

let (<>=>) = Int.(<>=>)

let name = Sig.get_fun_name

let w k f = Hashtbl.find weights (k,f)

let prec i f = 
try Hashtbl.find precedence (i,f)
with Not_found ->
  failwith ("Kbo.prec: unknown symbol " ^ (name f) ^ ", " ^ (string_of_int i))

let adm_smt (ctx,k) =
  let p = prec k in
  let zero, one = Int.mk_zero ctx, Int.mk_one ctx in
  let nat_f f = (w k f <>=> zero) <&> (p f <>=> zero) in
  let ensure_nat = big_and ctx [ nat_f f | f,_ <- !funs] in
  (* constants *)
  let cs = [ c | c,a <- !funs; a=0 ] in
  let cadm = big_and ctx [ w k c <>=> one | c <- cs ] in (* w0 = 1 *)
  (* unary symbols *)
  let f0 f = w k f <=> zero in
  let max f = big_and ctx [ p f <>> (p g) | g,_<- !funs; g <> f ] in
  let uadm = big_and ctx [ f0 f <=>> (max f) | f,a <- !funs; a = 1 ] in
  (* total *)
  let ps = [ f,g | f,_ <- !funs; g,_ <- !funs; f <> g ] in
  let total_prec = big_and ctx [ !! (p f <=> (p g)) | f, g <- ps ] in
  let cw0 = big_or ctx [ w k c <=> one | c <- cs ] in
  (* CeTA expects 0 *)
  let cw0' = if !(Settings.do_proof) = Some CPF then cw0 else mk_true ctx in
  big_and1 [ensure_nat; cadm; uadm; total_prec; cw0']
;;
    
let weight (ctx,k) t =
  let rec weight = function
    | V _ -> Int.mk_one ctx (* w0 = 1 *)
    | F(f,ss) -> Int.sum1 ((w k f) :: [weight si | si <- ss ])
  in weight t
;;

let rec remove_equals ss tt =
  match ss,tt with
    | [], [] -> [],[]
    | s::sss, t::ttt ->
      if s <> t then ss,tt else remove_equals sss ttt
    | _ -> failwith "Kbo.remove_equals: different lengths"
;;

let rec gt (ctx,k) s t =
  if (s = t || not (Rule.is_non_duplicating (s,t))) then mk_false ctx
  else
    let ws, wt = weight (ctx,k) s, weight (ctx,k) t in
    let cmp = match s,t with
     | V _,_ -> mk_false ctx
     | F(f,ss), V _ -> mk_true ctx (* var condition already checked *)
     | F(f,ss), F(g,ts) when f = g -> ( match remove_equals ss ts with
       | si :: _, ti :: _ -> gt (ctx,k) si ti
       | _ -> failwith "Kbo.gt different lengths")
     | F(f,ss), F(g,ts) -> (prec k f) <>> (prec k g)
    in
    ws <>> wt <|> ((ws <=> wt) <&> cmp)
;;

let ge (ctx,k) s t = if s = t then mk_true ctx else gt (ctx,k) s t

let init s ctx k =
  let fs = Rules.signature (s.gs @ [ r.terms | r <- s.norm @ s.axioms]) in
  Hashtbl.clear precedence;
  Hashtbl.clear weights;
  let add (f,_) =
    let s = "kbo" ^ (name f) ^ (string_of_int k) in
    Hashtbl.add precedence (k,f) (Int.mk_var ctx (s^"p"));
    Hashtbl.add weights (k,f) (Int.mk_var ctx s)
  in List.iter add fs;
  funs := fs;
  let constr = adm_smt (ctx,k) in
  let rec gt = function
    | f :: g :: fs -> (prec k f <>> prec k g) <&> gt (g :: fs)
    | _ -> mk_true ctx
  in
  match s.order_params with
  | Some ps ->
    let c = List.fold_left (fun c prec -> gt prec <&> c) constr ps.precedence in
    List.fold_left (fun c (f, a) -> w k f <=> Int.mk_num ctx a <&> c) c ps.weights
  | _ -> constr
;;

let cond_gt k ctx conds s t =
  let rec gt s t =
    if List.mem (s,t) conds then mk_true ctx
    else if (s = t || not (Rule.is_non_duplicating (s,t))) then mk_false ctx
    else
      let ws, wt = weight (ctx,k) s, weight (ctx,k) t in
      let cmp =
        match s,t with
          | V _,_ -> mk_false ctx
          | F(f,ss), V _ -> mk_true ctx (* var condition already checked *)
          | F(f,ss), F(g,ts) when f = g -> (match remove_equals ss ts with
            | si :: _, ti :: _ -> gt si ti
            | _ -> failwith "Kbo.cond_gt: different lengths")
          | F(f,ss), F(g,ts) -> (prec k f) <>> (prec k g)
     in ws <>> wt <|> ((ws <=> wt) <&> cmp)
  in big_or1 (gt s t :: [ gt u t | (s',u) <- conds; s' = s ])
;;

let eval_table_with eval k m h =
  let add (k',f) x p =
    if k <> k' then p
    else (
      try
        let v = eval m x in
        Hashtbl.add p f v; p
      with _ -> p)
  in Hashtbl.fold add h (Hashtbl.create 16)
;;

let eval_bool_table k m h = eval_table_with Logic.eval k m h

let eval_table k = eval_table_with Int.eval k

let decode_term_gt' tw tp add_syms =
  List.iter (fun f -> Hashtbl.add tw f 1) add_syms;
  let w = Hashtbl.find tw in
  let rec weight = function
    | T.V _ -> 1 (* w0 = 1 *)
    | T.F (f, ts) -> List.fold_left (fun s ti -> s + (weight ti)) (w f) ts
  in
  let sz_sig = Hashtbl.length tp in
  List.iter (fun (p,f) -> Hashtbl.add tp f p) (Listx.ix ~i:sz_sig add_syms);
  let prec = Hashtbl.find tp in
  let rec gt s t =
    if Term.is_subterm s t || not (Rule.is_non_duplicating (s,t)) then false
    else if Term.is_subterm t s then true
    else (
      let ws, wt = weight s, weight t in
      let cmp = match s,t with
        | T.V _, _
        | _, T.V _  -> false (* no subterm *)
        | T.F(f,ss), T.F(g,ts) ->
          let lex (gt_lex,ge) (u,v) = gt_lex || (ge && gt u v), ge && u = v in
          if f <> g then prec f > prec g
          else fst (L.fold_left lex (false, true) (List.combine ss ts))
      in
      ws > wt || (ws = wt && cmp))
  in gt
;;

let decode_term_gt k m = 
  decode_term_gt' (eval_table k m weights) (eval_table k m precedence)

let eval k m =
  let prec f = try Hashtbl.find (eval_table k m precedence) f with _ -> 0 in
  let w f = try Hashtbl.find (eval_table k m weights) f with _ -> 0 in
  List.sort (fun (_,p,_) (_,q,_) -> p - q) [ (f,a), prec f, w f | f,a <- !funs ]
;;

let to_string = function
    [] -> ""
  | ((f,_),p,w) :: fpw ->
    let s = "KBO \n " ^ (name f) in
    let name = Signature.get_fun_name in
    let s = List.fold_left (fun s ((f,_),i,_) -> s ^" < " ^ (name f)) s fpw in
    let s = s ^ "\n w0 = 1, w(" ^ (name f) ^ ") = " ^ (string_of_int w) in
    let addw s ((f,_),_,w) = s ^ ", w(" ^ (name f) ^ ") = "^(string_of_int w) in
    List.fold_left addw s fpw
;;

let print fpw = Format.printf "%s\n%!" (to_string fpw)

let print_params = function
    [] -> ()
  | ((f,_),p,w) :: fpw ->
    Format.printf "-t KBO6 ";
    let name = Signature.get_fun_name in
    if fpw <> [] then (
      Format.printf "--precedence=\"%s" (name f);
      List.iter (fun ((f,_),i,_) -> Format.printf "<%s" (name f)) fpw;
      Format.printf "\" %!"
    );
    Format.printf "--order-weights=\"%s:%d" (name f) w;
    List.iter (fun ((f,_),_,w) -> Format.printf ",%s:%d" (name f) w) fpw;
    Format.printf "\"\n%!"
;;

let decode_print k m = print (eval k m)

let decode_xml fpws =
  let prec_weight ((f,a),p,w) =
    let name = Xml.Element("name", [], [Xml.PCData (name f)]) in
    let arity = Xml.Element("arity", [], [Xml.PCData (string_of_int a)]) in
    let prec = Xml.Element("precedence", [], [Xml.PCData (string_of_int p)]) in
    let weight = Xml.Element("weight", [], [Xml.PCData (string_of_int w)]) in
    Xml.Element("precedenceWeightEntry", [], [ name; arity; prec; weight] )
  in
  let w0 = Xml.Element("w0", [], [Xml.PCData "1"]) in
  let pw = Xml.Element("precedenceWeight", [], [ prec_weight f | f <- fpws ]) in
  Xml.Element("knuthBendixOrder", [], [ w0; pw ] )
;;

let encode k fpw ctx =
  let num = Int.mk_num ctx in
  let add ((f,_),p,wf) = prec k f <=> (num p) <&> w k f <=> (num wf) in
  Logic.big_and ctx (List.map add fpw)
;;

let decode k m =
  let gt = decode_term_gt k m in
  let cmp c d = if gt [] (Term.F(c,[])) (Term.F(d,[])) then d else c in
  let bot =  match [ c | c,a <- !funs; a = 0] with
      [] -> None
    | c :: cs -> Some (List.fold_left cmp c cs)
  in
  let fpw = eval k m in
  object
    method bot = bot
    method gt = gt []
    method gt_extend_sig = gt
    method smt_encode ctx = encode k fpw ctx
    method to_string = to_string fpw
    method print = fun _ -> print fpw
    method to_xml = decode_xml fpw
    method print_params = fun _ -> print_params fpw
  end
;;
