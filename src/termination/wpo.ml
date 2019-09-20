(*** MODULES *****************************************************************)
module L = List
module T = Term
module H = Hashtbl
module Sig = Signature
module Logic = Settings.Logic

(*** OPENS *******************************************************************)
open Term
open Logic
open Settings

(*** GLOBALS *****************************************************************)
(* signature *)
let funs = ref []

(* map function symbol and argument position to boolean expression:
   if true, argument is in max expression  *)
let arg_max_status : (int * (Sig.sym * int), Logic.t) H.t =
  H.create 32

(* map function symbol and strategy stage to constant for weight *)
let weights : (int * Sig.sym, Logic.t) H.t = H.create 32

(* map function symbol and strategy stage to variable for precedence *)
let precedence : (int * Sig.sym, Logic.t) H.t = H.create 32

let w0_table : (int, Logic.t) H.t = H.create 32

(*** FUNCTIONS ***************************************************************)
let (<>>) = Int.(<>>)

let (<+>) = Int.(<+>)

let (<>=>) = Int.(<>=>)

let (!!) = Logic.(!!)

let name = Sig.get_fun_name

let arg_max k f i = H.find arg_max_status (k, (f, i))

let w_fun k f =
  try H.find weights (k,f)
  with Not_found ->
    failwith ("Wpo.w: unknown symbol " ^ (name f) ^ ", " ^ (string_of_int k))
;;

let prec i f = 
  try H.find precedence (i,f)
  with Not_found ->
    failwith ("Wpo.prec: unknown symbol " ^ (name f) ^ ", " ^ (string_of_int i))
;;

let w0 i = 
  try H.find w0_table i
  with Not_found -> failwith ("Wpo.w0: unknown for " ^ (string_of_int i))
;; 

let adm_smt (ctx, k) funs =
  let p = prec k in
  let zero, one = Int.mk_zero ctx, Int.mk_one ctx in
  let nat_f f = (w_fun k f <>=> zero) <&> (p f <>=> zero) in
  let ensure_nat = big_and ctx [ nat_f f | f,_ <- funs] in
  (* TODO other constraints? *)
  (* total *)
  let ps = [ f,g | f,_ <- funs; g,_ <- funs; f <> g ] in
  let total_prec = big_and ctx [ !! (p f <=> (p g)) | f, g <- ps ] in
  (* constants >= w0, w0 >= 0 *)
  let w0 = w0 k in
  let cs = [f | f, a <- funs; a = 0] in
  let w0c = w0 <>=> zero in
  let consts = List.fold_left (fun c f -> (w_fun k f <>=> w0) <&> c) w0c cs in
  (* combine *)
  big_and1 [ensure_nat; total_prec; consts]
;;

let init s ctx k =
  let fs = Rules.signature (s.gs @ [ r.terms | r <- s.norm @ s.axioms]) in
  let add (f, a) =
    let s = "wpo" ^ (name f) ^ (string_of_int k) in
    H.add precedence (k, f) (Int.mk_var ctx (s^"p"));
    H.add weights (k, f) (Int.mk_var ctx (s^"w"));
    let var i = mk_fresh_bool_var ctx in
    let add_arg_status i = H.add arg_max_status (k, (f, i)) (var i) in
    List.iter add_arg_status (Listx.range 0 (a - 1))
  in List.iter add fs;
  H.add w0_table k (Int.mk_var ctx ("w0" ^ (string_of_int k)));
  funs := fs;
  let constr = adm_smt (ctx, k) fs in
  let rec gt = function
    | f :: g :: fs -> (prec k f <>> prec k g) <&> gt (g :: fs)
    | _ -> mk_true ctx
  in
  match s.order_params with
  | Some ps ->
    let c = L.fold_left (fun c prec -> gt prec <&> c) constr ps.precedence in
    let fix_weight f a = w_fun k f <=> Int.mk_num ctx a in
    L.fold_left (fun c (f, a) -> fix_weight f a <&> c) c ps.weights
  | _ -> constr
;;

let vop_if ctx op b vs vsi =
  let zero = Int.mk_zero ctx in
  let add_cnt cx x = try op cx (List.assoc x vsi) with Not_found -> cx in
  let vsx = [x, ite b (add_cnt cx x) cx | x, cx <- vs] in
  [x, ite b c zero | x, c <- vsi; not (L.mem_assoc x vs)] @ vsx
;;

let vop op xs ys =
  let add_cnt cx x = try op cx (List.assoc x xs) with Not_found -> cx in
  let ysx = [x, add_cnt cx x | x, cx <- ys] in
  [x, c | x, c <- xs; not (L.mem_assoc x ys)] @ ysx
;;

(* MSum setting: f(x, y, z) = x + max(y, z) + c *)
let weight (ctx, k) t =
  let zero = Int.mk_zero ctx in
  let rec weight = function
  | V x -> w0 k, [x, Int.mk_one ctx]
  | F(f, ss) ->
    let args = Listx.ix [weight si | si <- ss ] in
    let vars_op op p =
      L.fold_left (fun vs (i,(_,vsi)) -> vop_if ctx op (p i) vs vsi) [] args
    in
    let args_sum = [ ite (arg_max k f i) zero ai | i, (ai, _) <- args ] in
    let vs_sum = vars_op (<+>) (fun i -> !! (arg_max k f i)) in
    let args_max = [ ite (arg_max k f i) ai zero | i, (ai, _) <- args ] in
    let vs_max = vars_op (fun a b -> ite (a <>> b) a b) (arg_max k f) in
    let max = List.fold_left (fun m a -> ite (a <>> m) a m) zero args_max in
    Int.sum1 ((w_fun k f) :: max :: args_sum), vop (<+>) vs_sum vs_max
  in weight t
;;

let rec remove_equals ss tt =
  match ss,tt with
    | [], [] -> [],[]
    | s :: sss, t :: ttt ->
      if s <> t then ss,tt else remove_equals sss ttt
    | _ -> failwith "Wpo.remove_equals: different lengths"
;;

let weight_cmp (ctx, k) s t =
  let ws, vss = weight (ctx, k) s in
  let wt, vst = weight (ctx, k) t in
  let cmp b (x, c) = try b <&> (L.assoc x vss <>=> c) with _ -> mk_false ctx in
  let var_cond = List.fold_left cmp (mk_true ctx) vst in
  var_cond <&> (ws <>> wt), var_cond <&> (ws <>=> wt)
;;

(* taking = as >= *)
let gt_lex ctx gt ss ts =
  let rec lex = function
  | s :: ss, t :: ts when s = t -> lex (ss, ts)
  | s :: _, t :: _ -> gt s t
  | [], [] -> mk_false ctx
  | _ -> failwith "Wpo.gt_lex: different lengths"
  in
  lex (ss, ts)
;;

let rec gt (ctx, k) s t =
  let top, bot = mk_true ctx, mk_false ctx in
  if T.is_subterm s t then bot
  else if T.is_subterm t s then top
  else
    let w_gt, w_ge = weight_cmp (ctx, k) s t in
    let cmp_rec = match s, t with
    | T.V _, _ -> bot
    | T.F(_, _), T.V x -> if L.mem x (T.variables s) then top else bot
    (* in lexicographic case assume same roots (precedence total) *)
    | T.F(f, ss), T.F(g, ts) ->
      if f <> g then prec k f <>> (prec k g) else gt_lex ctx (gt (ctx, k)) ss ts
    in
    let cmp_subt = match s, t with
    | T.F(_, ss), _ -> Logic.big_or ctx [gt (ctx, k) s' t | s' <- ss]
    | _ -> bot
    in
    w_gt <|> (w_ge <&> (cmp_subt <|> cmp_rec))
    and ge (ctx, k) s t = if s = t then mk_true ctx else gt (ctx, k) s t
;;

let cond_gt k ctx conds =
  let top, bot = mk_true ctx, mk_false ctx in
  let rec cgt s t =
    if List.mem (s,t) conds || T.is_subterm t s then top
    else if T.is_subterm s t then bot
    else
      let w_gt, w_ge = weight_cmp (ctx, k) s t in
      let cmp_rec = match s, t with
      | T.V _, _ -> bot
      | T.F(_, _), T.V x -> if L.mem x (T.variables s) then top else bot
      (* in lexicographic case assume same roots (precedence total) *)
      | T.F(f, ss), T.F(g, ts) ->
        if f <> g then prec k f <>> (prec k g) else gt_lex ctx cgt ss ts
      in
      let cmp_subt = match s, t with
      | T.F(_, ss), _ -> Logic.big_or ctx [cgt s' t | s' <- ss]
      | _ -> bot
      in
      w_gt <|> (w_ge <&> (cmp_subt <|> cmp_rec))
  in cgt
;;

let last_rule  = ref None

let gt (ctx, k) s t = last_rule := Some (s, t); gt (ctx, k) s t

let eval_table = Kbo.eval_table

(* mind that when running the returned function gt no evaluation may happen
   since the model pointer is likely already invalid *)
let decode_term_gt k m =
  let w = H.find (eval_table k m weights) in
  let w0 = Int.eval m (H.find w0_table k) in
  let arg_max = H.find (Kbo.eval_bool_table k m arg_max_status) in
  let args f a = L.partition (fun i -> arg_max (f,i)) (Listx.range 0 (a - 1)) in
  let rec weight = function
    | T.V _ -> w0
    | T.F (f, ts) ->
      let margs, sargs = args f (List.length ts) in
      let sts = [ weight (L.nth ts i) | i <- sargs] in
      let mts = List.fold_left max 0 [ weight (L.nth ts i) | i <- margs] in
      L.fold_left (fun s wti -> s + wti) (w f + mts) sts
  in
  let prec = H.find (eval_table k m precedence) in
  let rec lex gt = function
  | s :: ss, t :: ts -> gt s t || (s = t && lex gt (ss, ts))
  | [], [] -> false
  | _ -> failwith "Wpo.lex: different lengths"
  in
  let rec gt s t =
    if T.is_subterm s t || (weight s < weight t) then false
    else if not (Rule.is_rule (s,t)) then false
    else if T.is_subterm t s || (weight s > weight t) then true
    else (
      let cmp_rec = match s,t with
        | T.V _, _
        | _, T.V _  -> false (* no subterm *)
        | T.F(f, ss), T.F(g, ts) ->
          if f <> g then prec f > prec g else lex gt (ss, ts)
      in
      let cmp_subt = match s, t with
      | T.F(_, ss), _ -> L.exists (fun s' -> gt s' t) ss
      | _ -> false
      in
      cmp_subt || cmp_rec
    )
  in 
  gt
;;

let eval k m =
  let prec f = try H.find (eval_table k m precedence) f with _ -> 0 in
  let w f = try H.find (eval_table k m weights) f with _ -> 0 in
  let maxarg f i =
    try Logic.eval m (arg_max k f i) with _ -> failwith "WPO: maxarg not found"
  in
  let args f a = L.partition (fun i -> maxarg f i) (Listx.range 0 (a - 1)) in
  let fpws = [ (f,a), prec f, w f, args f a | f, a <- !funs ] in
  let w0 = Int.eval m (H.find w0_table k) in
  List.sort (fun (_, p, _, _) (_, q, _, _) -> p - q) fpws, w0
;;

let to_string (fpw, w0) =
  let name = Signature.get_fun_name in
  let interp ((f, a), p, w, (margs, sargs)) =
    let xs l = [ "x" ^  (string_of_int i) | i <- l] in
    let app sep = function
    | [] -> ""
    | a :: ars -> (L.fold_left (fun s a -> s ^ sep ^ a) a ars)
    in
    let argstr = "(" ^ (app "," (xs (Listx.range 0 (a - 1)))) ^ ")" in
    let sstr = app " + " (xs sargs) in
    let mstr = if margs=[] then "" else "max(" ^ (app "," (xs margs)) ^ ",0)" in
    let inter =
      (if sargs = [] then "" else sstr ^ " + ") ^
      (if margs = [] then "" else mstr ^ " + ") ^
      (string_of_int w)
    in
    (name f) ^ (if a = 0 then "" else argstr) ^ " = " ^ inter
  in
  let fs = [f | (f, _), _, _, _ <- fpw] in
  let prec =
    match fs with
    | f :: fs -> L.fold_left (fun s f -> s ^ " < " ^ (name f)) (name f) fs
    | _ -> ""
  in
  let w0 = "WPO\nw0 = " ^ (string_of_int w0) ^ "\n" ^ prec ^ "\n" in
  List.fold_left (fun s f -> s ^ (interp f) ^ "\n") w0 fpw
;;

let print fpw = Format.printf "%s%!" (to_string fpw)

let decode_print k m = print (eval k m)

let decode k m =
  let decoded_gt = decode_term_gt k m in
  let cmp c d = if decoded_gt (T.F(c,[])) (T.F(d,[])) then d else c in
  let bot =  match [ c | c,a <- !funs; a = 0] with
      [] -> None
    | c :: cs -> Some (List.fold_left cmp c cs)
  in
  let fpw = eval k m in
  object
    method bot = bot
    method gt = decoded_gt
    method smt_encode = (fun _ -> failwith "WPO encode not implemented")
    method to_string = to_string fpw
    method print = fun _ -> print fpw
    method to_xml = Xml.Element("weightedPathOrder", [], [] )
    method print_params = (fun _ -> failwith "WPO params not implemented")
  end
;;

let clear _ =
  H.clear precedence;
  H.clear arg_max_status;
  H.clear weights;
  H.clear w0_table
;;