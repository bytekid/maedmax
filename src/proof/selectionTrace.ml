(*** OPENS *******************************************************************)
open Format
open Yojson.Basic
open Settings

(*** MODULES *****************************************************************)
module L = List
module T = Term
module H = Hashtbl
module Sig = Signature

(*** GLOBALS ********************* *******************************************)
let selections : selection_features list ref = ref []

(*** FUNCTIONS ***************************************************************)
(* * * * * * PQ-GRAMS * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
let dummy = -1

(* extend with dummies and replace function names by arities *)
let extend p q t =
  let dummies = Listx.copy (q - 1) (T.F (dummy, [])) in
  let rec ext_q = function
    | (T.V _ as t) -> t
    | T.F (_, []) -> T.F (0, [])
    | T.F (_, ts) -> T.F(L.length ts, dummies @ [ext_q ti | ti <- ts] @ dummies)
  in
  let rec ext_p i t = if i = 0 then t else T.F(dummy, [ext_p (i - 1) t]) in
  ext_p (p - 1) (ext_q t)
;;

type node = Fun of int | Var | Dummy

type node_named = FunN of string | VarN | DummyN

type pq_gram = node list

let pq_count_table : (Term.t, int list) Hashtbl.t = Hashtbl.create 256

(* fixed for now *)
let pq = ref (1, 2)

let all =
  let cs = [ Fun 0 ] in
  let ncs = [Fun 1; Fun 2; Fun 3] in
  let all = Var :: Dummy :: cs @ ncs in
  (*[[n1; n2; n3; n4] | n1 <- Dummy :: ncs; n2 <- ncs; n3 <- all; n4 <- all;
    not (n3 = Dummy && n4 = Dummy) ]*)
  let no_dummies n3 n4 = not (n3 = Dummy && n4 = Dummy) in
  let gs = [[n2; n3; n4] | n2 <- ncs; n3 <- all; n4 <- all; no_dummies n3 n4] in
  List.sort compare gs
;;

let print_pq_gram =
  let nstr = function Dummy -> "*" | Fun i -> string_of_int i | _ -> "X" in
  let pnode f n = Format.fprintf f "%s" (nstr n) in
  Formatx.print_list pnode "."
;;

let print_pq_grams = Formatx.print_list print_pq_gram "\n"

let pq_grams p q t =
  let tx = extend p q t in
  let complete g = List.length g = (p + q) in
  let rec takeq ts =
    if List.length ts < q then []
    else Listx.take q ts :: (takeq (List.tl ts))
  in
  let node = function
    | T.V _ -> Var
    | T.F (d, _) when d = dummy -> Dummy
    | T.F (f, _) -> Fun f (* after extend: gets abstracted to arity *)
  in
  let rec pqs = function
    | T.V _ -> []
    | T.F (d, []) when d = dummy -> []
    | T.F (f, ts) as t ->
      let gs = List.concat [pqs ti | ti <- ts] in
      let gs_c, gs_i = List.partition complete gs in
      [ node t :: g | g <- takeq [node ti | ti <- ts]] @
      [ node t :: g | g <- gs_i ] @ gs_c
  in
  [g | g <- pqs tx; complete g]
;;

let extend_named p q t =
  let dummies = Listx.copy (q - 1) (T.F (dummy, [])) in
  let rec ext_q = function
    | (T.V _ as t) -> t
    | T.F (f, []) -> T.F (f, [])
    | T.F (f, ts) -> T.F(f, dummies @ [ext_q ti | ti <- ts] @ dummies)
  in
  let rec ext_p i t = if i = 0 then t else T.F(dummy, [ext_p (i - 1) t]) in
  ext_p (p - 1) (ext_q t)
;;

let pq_grams_named p q t =
  let tx = extend_named p q t in
  let complete g = List.length g = (p + q) in
  let rec takeq ts =
    if List.length ts < q then []
    else Listx.take q ts :: (takeq (List.tl ts))
  in
  let node = function
    | T.V _ -> VarN
    | T.F (d, _) when d = dummy -> DummyN
    | T.F (f, _) -> FunN (Signature.get_fun_name f)
  in
  let rec pqs = function
    | T.V _ -> []
    | T.F (d, []) when d = dummy -> []
    | T.F (f, ts) as t ->
      let gs = List.concat [pqs ti | ti <- ts] in
      let gs_c, gs_i = List.partition complete gs in
      [ node t :: g | g <- takeq [node ti | ti <- ts]] @
      [ node t :: g | g <- gs_i ] @ gs_c
  in
  [g | g <- pqs tx; complete g]
;;

let print_named_pq_gram =
  let nstr = function Dummy -> "*" | Fun i -> string_of_int i | _ -> "X" in
  let pnode f n = Format.fprintf f "%s" (nstr n) in
  Formatx.print_list pnode "."
;;

let count_vector t =
  let p,q = fst !pq, snd !pq in
  let gs = List.sort compare (pq_grams p q t) in
  let ggs = Listx.group_by (fun x -> x) gs in
  let rec count = function
    | (_, []) -> []
    | ((g, os) :: gs, a :: all') when g = a -> L.length os :: (count (gs, all'))
    | (gs, a :: all') -> 0 :: (count (gs, all'))
  in
  try Hashtbl.find pq_count_table t with
  Not_found -> let v = count (ggs, all) in Hashtbl.add pq_count_table t v; v
;;

let print_vector =
  let pval f n = Format.fprintf f "%d" n in
  Formatx.print_list pval " "
;;

let pq_gram_features (s, t) = count_vector s, count_vector t

let test_pq_gram_term t = 
  Format.printf "%a has pq-grams:\n%a\n" Term.print t print_pq_grams
    (pq_grams 1 2 t)
;;

let test_pq_grams es =
  let p,q = fst !pq, snd !pq in
  Format.printf "all pq-grams:\n%a\n" print_pq_grams all;
  let pq_gram_features (s, t) =
    let vs, vt = count_vector s, count_vector t in
    Format.printf "%a has pq-grams:\n%a\n%a\n"
      Term.print s print_pq_grams (pq_grams p q s) print_vector vs;
    Format.printf "%a has pq-grams:\n%a\n%a\n"
      Term.print t print_pq_grams (pq_grams p q t) print_vector vt
  in
  List.iter (fun e -> pq_gram_features e) es
;;

(* * * * * * STATE FEATURES * * * * * * * * * * * * * * * * * * * * * * * * * *)
let state_features _ =
  let ee = !Analytics.equalities in
  let gg = !Analytics.goals in
  let i = !Analytics.iterations in
  { equations = ee; goals = gg; iterations = i}
;;

let state_feature_string fs =
  Printf.sprintf "%d %d %d" fs.equations fs.goals fs.iterations
;;

(*
let count_subterms_where pred cc n =
  let s, t = Literal.terms n in
  let is_rule (l,r) = Rule.is_rule (l,r) && not (T.is_embedded l r) in
  let matched_by n' =
    let s',t' = Literal.terms n' in
    let matching u =
      (is_rule (s,t) && pred u s) || (is_rule (t,s) && pred u t)
    in
    List.exists matching (T.subterms s' @ (T.subterms t'))
  in
  let r = List.length (List.filter matched_by cc) in
  r
;;

let matches = count_subterms_where Subst.is_instance_of

let unifiables = count_subterms_where Subst.unifiable
*)
let count_term_cond retrieve cc =
  let cc = [Literal.terms n | n <- cc] in
  let is_rule (l,r) = Rule.is_rule (l,r) && not (Term.is_embedded l r) in
  let subts r = [ u, u | u <- T.subterms (fst r); not (T.is_variable u)] in
  let ts = List.concat [subts (l,r) @ subts (r,l) | l,r <- cc] in
  let ps = [[]; [0]; [1]; [0;0]; [0;1]; [1;0]; [1;1]] in
  let idx = FingerprintIndex.create ~poss:ps ts in
  let insts u = [ v | v <- retrieve u idx] in
  let count_node n =
    let s, t = Literal.terms n in
    let insts (l, r) = if is_rule (l,r) then L.length (insts l) else 0 in 
    insts (s,t) + insts (t,s)
  in
  let len = float_of_int (List.length cc + 1) in
  let norm i = (float_of_int i) /. len in
  (fun n -> norm (count_node n))
;;

let count_instances = count_term_cond FingerprintIndex.get_instances

let count_unifiables = count_term_cond FingerprintIndex.get_unifiables

let node_features n cc =
  let is_rule (l,r) = Rule.is_rule (l,r) && not (T.is_subterm l r) in
  let s, t = Literal.terms n in
  let a  = Nodes.age n in
  let max_age = float_of_int (Nodes.max_age ()) in
  let age = (max_age -. float_of_int a) /. max_age in
  {
    is_goal_selection = Literal.is_inequality n;
    size = Rule.size (s, t);
    size_diff = abs (T.size s - T.size t);
    linear = Rule.linear (s, t);
    age = age;
    orientable = (is_rule (s, t), is_rule (t, s));
    duplicating = (Rule.is_duplicating (s, t), Rule.is_duplicating (t, s));
    matches = count_instances cc n;
    cps = count_unifiables cc n
  }
;;

let node_feature_string fs =
  let i b = if b then 1 else 0 in
  let s b = if b then "1" else "0" in
  let s2 (b1,b2) = s b1 ^ " " ^ (s b2) in 
  Printf.sprintf "%d %d %d %d %.2f %s %s %.3f %.3f"
    (i fs.is_goal_selection) fs.size fs.size_diff (i fs.linear) fs.age
    (s2 fs.orientable) (s2 fs.duplicating) fs.matches fs.cps
;;

let log selected all =
  let state_data = state_features () in
  let add e =
    (* exclude trivial literals that may appear just before success *)
    if fst (Literal.terms e) <> snd (Literal.terms e) then
      let e_data = node_features e all in
      selections := (e, e_data, state_data) :: !selections
  in
  List.iter add selected
;;

let report ancs =
  let used rl = List.mem rl ancs in
  let show (n, n_fs, st_fs) =
    let rl = Literal.terms n in
    let sn_fs = node_feature_string n_fs in
    let sst_fs = state_feature_string st_fs in
    let u = if used rl then 1 else 0 in
    let vs, vt = pq_gram_features rl in
    Format.printf "-- %a\n%s %s %a %a %d\n"
      Rule.print rl sn_fs sst_fs print_vector vs print_vector vt u; 
  in
  List.iter show !selections
;;

let report ancs =
  let ht = Hashtbl.create 256 in
  let collect (n, _, _) =
    let (s, t) = Literal.terms n in
    let pqgs = pq_grams_named 1 2 s @ (pq_grams_named 1 2 t) in
    let add g = 
      try Hashtbl.replace ht g (Hashtbl.find ht g + 1)
      with Not_found -> Hashtbl.add ht g 1
    in
    List.iter add pqgs
  in
  let repl s =
    if s = "b" || s = "c" || s = "d" || s = "aa" || s = "sk1" || s = "sk2" ||
       s = "sk3" then "a" else s
    in
  let print =
    let nstr = function DummyN -> "*" | FunN i -> repl i | _ -> "X" in
    let pnode f n = Format.fprintf f "%s" (nstr n) in
    Formatx.print_list pnode "."
  in
  List.iter collect !selections;
  let l = Hashtbl.fold (fun g n l -> if n > 9 then (g, n) :: l else l) ht [] in
  let l = List.sort (fun (_,a) (_,b) -> compare b a) l in
  List.iter (fun (g, n) -> Format.printf "%a  %d\n%!" print g n) l
;;

let for_goal_disproof (rr, ee) (rs, rt) =
  let tfst = (fun (rl,_,_,_) -> rl) in
  let rrs,rrt = List.map tfst rs, List.map tfst rt in
  let ancs = Trace.ancestors (ee @ rr @ rrs @ rrt) in
  report (List.map fst ancs)
;;

let for_goal_proof es0 g_orig ((s, t), (rs, rt), sigma) =
  let g = Variant.normalize_rule g_orig in
  let ancs = Trace.goal_proof g (s, t) (rs, rt) sigma in
  report (List.map fst ancs)
;;

let for_ground_completion ee0 (rr, ee) =
  let ancs = Trace.ancestors (ee @ rr) in
  report (List.map fst ancs)
;;
