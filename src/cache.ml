(*** MODULES *****************************************************************)
module A = Analytics
module H = Hashtbl
module L = Settings.Logic

(*** OPENS *******************************************************************)
open Prelude
open Rewriting

(*** GLOBALS *****************************************************************)
(* count number of TRSs considered so far *)
let trscount = ref 0

(* associate index with TRS and vice versa *)
let ht_itrss : (int, Rules.t) H.t = H.create 128;;
let ht_iredtrss : (int, Rules.t) H.t = H.create 128;;
let ht_trssi : (Rules.t,int) H.t = H.create 128;;

(* tuples ((n,m),b) to remember whether TRS n contains TRS m *)
let ht_contains : (int * int, bool) H.t = H.create 200;;

(* Yices variable for each TRS *)
let ht_trsvars : (int, L.t) H.t = H.create 128;;

(* bool and int Yices variable for each equation (only for comp setting) *)
let eq_vars : (Rule.t * (L.t * L.t)) list ref = ref [];;
(* Yices variable for each rule *)
let ht_rl_vars : (Rule.t, L.t) H.t = H.create 128

(* variables for strategy stage and strict rules *)
let strict_vars : (int * Rule.t, L.t) H.t = H.create 128

(* variables for strategy stage and weak rules *)
let weak_vars : (int * Rule.t, L.t) H.t = H.create 128

(* variables for reducibility of equation *)
let ht_rdcbl_vars : (Rule.t, L.t) H.t = H.create 128
let ht_rdcbl_constr : (Rule.t, L.t) H.t = H.create 128

(* remember whether termination constraint was already added to context *)
let ht_rlycs : (Rule.t, bool) H.t = H.create 128;;

let ht_rewriters : (int, Rewriter.rewriter) H.t = H.create 128

let ht_considered_overlaps : (Rule.t * Rule.t * Term.pos, bool) H.t = H.create 128

let equation_count = ref 0

(*** FUNCTIONS ***************************************************************)
let (<=>>) = L.(<=>>)
let (!!) = L.(!!)

let clear _ =
  H.clear ht_itrss;
  H.clear ht_iredtrss;
  H.clear ht_trssi;
  H.clear ht_contains;
  H.clear ht_trsvars;
  eq_vars := [];
  H.clear strict_vars;
  H.clear weak_vars;
  H.clear ht_rlycs;
  H.clear ht_rdcbl_constr;
  H.clear ht_rdcbl_vars;
  H.clear ht_rl_vars;
  H.clear ht_rewriters;
  H.clear ht_considered_overlaps;
  trscount := 0
;;

let trs_of_index n =
  try H.find ht_itrss n
  with Not_found -> failwith ("trs_of_index failed")
;;

let redtrs_of_index n =
  try H.find ht_iredtrss n
  with Not_found -> failwith ("redtrs_of_index " ^ (string_of_int n) ^ " failed")
;;

let trs_of_index = A.take_time A.t_cache trs_of_index

let contains n m =
  try H.find ht_contains (n,m)
  with Not_found ->
    let rn = redtrs_of_index n in
    let rm = redtrs_of_index m in
    let c = Listset.subset rm rn in
    H.add ht_contains (n,m) c;
    c
;;

let contains n = A.take_time A.t_cache (contains n)

let rlvar_cmp st rl = Rule.variant st rl

let find_rule rl = H.find ht_rl_vars rl

let store_rule_var ?(assert_rule=true) ctx lr =
  try find_rule lr with _ -> (
    let v = L.mk_fresh_bool_var ctx in
    if assert_rule && not (Rule.is_rule lr) then L.require (!! v);
    H.add ht_rl_vars lr v;
    v)
;;

let store_rule_vars ctx rls = List.iter (ignore <.> store_rule_var ctx) rls

let store_eq_var ctx lr =
  let v = L.mk_fresh_bool_var ctx in
  let vi = L.Int.mk_var ctx ("eqw"^(string_of_int !equation_count)) in
  equation_count := !equation_count + 1;
  eq_vars := (lr, (v, vi)) :: !eq_vars;
  (v, vi) 
;;

let store_eq_vars ctx rls = List.iter (ignore <.> store_eq_var ctx) rls

let rule_var ctx rl = try find_rule rl with Not_found -> store_rule_var ctx rl

let eq_variant (l,r) st = Rule.variant st (l,r) || Rule.variant st (r,l)

let find_eq rl =
  try fst (snd (List.find (fun (st,_) -> eq_variant st rl) !eq_vars))
  with Not_found -> failwith ("no equation variable for " ^ (Rule.to_string rl))
;;

let find_eq_weight rl =
  try snd (snd (List.find (fun (st,_) -> eq_variant st rl) !eq_vars))
  with Not_found -> failwith ("no equation weight for " ^ (Rule.to_string rl))
;;

let eq_var ctx rl =
  try fst (snd (List.find (fun (st,_) -> eq_variant st rl) !eq_vars))
  with Not_found -> fst (store_eq_var ctx rl)
;;

let eq_weight_var ctx rl =
  try snd (snd (List.find (fun (st,_) -> eq_variant st rl) !eq_vars))
  with Not_found -> snd (store_eq_var ctx rl)
;;

let find_strict_var = H.find strict_vars

let find_weak_var = H.find weak_vars

let get_var h ctx (i,r) = 
  if H.mem h (i,r) then H.find h (i,r)
  else let v = L.mk_fresh_bool_var ctx in H.add h (i,r) v; v
;;

let get_strict_var = get_var strict_vars

let get_weak_var = get_var weak_vars

let get_rdcbl_var = get_var ht_rdcbl_vars

let get_all_strict k =
  H.fold (fun (i,r) v l -> if i=k then (r,v)::l else l) strict_vars []
;;

let find_trs_var n =
  try H.find ht_trsvars n
  with Not_found -> failwith ("trsvar "^(string_of_int n)^" not found")
;;

let find_trs_var = A.take_time A.t_cache find_trs_var

let store_trs trs =
  trscount := !trscount+1;
  let n = !trscount in
  H.add ht_itrss n trs;
  H.add ht_trssi trs n;
  n
;;

let store_redtrs trs n = H.add ht_iredtrss n trs

let store_trs = A.take_time A.t_cache store_trs

let assert_rule k f =
  if not (H.mem ht_rlycs k) then (f k; H.add ht_rlycs k true)
;;

let assert_with ctx f ce =
  let assert_constr (l,r) =
    let c (s,t) = (find_rule (s,t)) <=>> (f ctx s t) in
    L.require (c (l,r));
    L.require (c (r,l))
  in
  let consider (lr,_) = assert_rule lr assert_constr in
  List.iter consider ce
;;

let decode_print m i =
  let s =
    H.fold (fun (j,rl) v l -> if i=j then (rl,v)::l else l) strict_vars []
  in
  let s' = [ rl | (rl,v) <- s; L.eval m v ] in
  let w =
    H.fold (fun (j,rl) v l -> if i=j then (rl,v)::l else l) weak_vars []
  in
  let w' = [ rl | (rl,v) <- w; L.eval m v ] in
  Format.printf "Strict %i: \n@[ %a@]\n" i Rules.print s';
  Format.printf "Weak %i: \n@[ %a@]\n" i Rules.print w'
;;

let consider_overlap rl1 rl2 p = H.replace ht_considered_overlaps (rl1,rl2,p) true

let overlap_was_considered rl1 rl2 p = H.mem ht_considered_overlaps (rl1,rl2,p)