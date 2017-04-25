(*** MODULES *****************************************************************)
module St = Statistics

(*** OPENS *******************************************************************)
open Prelude
open Yicesx
open Rewriting

(*** GLOBALS *****************************************************************)
(* count number of TRSs considered so far *)
let trscount = ref 0
(* associate index with TRS and vice versa *)
let ht_itrss : (int, Rules.t) Hashtbl.t = Hashtbl.create 128;;
let ht_iredtrss : (int, Rules.t) Hashtbl.t = Hashtbl.create 128;;
let ht_trssi : (Rules.t,int) Hashtbl.t = Hashtbl.create 128;;

(* tuples ((n,m),b) to remember whether TRS n contains TRS m *)
let ht_contains : (int * int, bool) Hashtbl.t = Hashtbl.create 200;;

let ht_was_oriented : (Rule.t,bool) Hashtbl.t = Hashtbl.create 128;;

(* Yices variable for each TRS *)
let ht_trsvars : (int, Yicesx.t) Hashtbl.t = Hashtbl.create 128;;

(* bool and int Yices variable for each equation (only for comp setting) *)
let eq_vars : (Rule.t * (Yicesx.t * Yicesx.t)) list ref = ref [];;
(* Yices variable for each rule *)
let rule_vars : (Rule.t * Yicesx.t) list ref = ref [];;
(* variables for strategy stage and strict rules *)
let strict_vars : (int * Rule.t, Yicesx.t) Hashtbl.t = Hashtbl.create 128
(* variables for strategy stage and weak rules *)
let weak_vars : (int * Rule.t, Yicesx.t) Hashtbl.t = Hashtbl.create 128

(* remember whether termination constraint was already added to context *)
let ht_rlycs : (Rule.t, bool) Hashtbl.t = Hashtbl.create 100;;

let wc = ref 0

(*** FUNCTIONS ***************************************************************)
let clear _ =
  Hashtbl.clear ht_itrss;
  Hashtbl.clear ht_iredtrss;
  Hashtbl.clear ht_trssi;
  Hashtbl.clear ht_contains;
  Hashtbl.clear ht_trsvars;
  eq_vars := [];
  rule_vars := [];
  Hashtbl.clear strict_vars;
  Hashtbl.clear weak_vars;
  Hashtbl.clear ht_rlycs
;;

let trs_of_index n =
  try Hashtbl.find ht_itrss n
  with Not_found -> failwith ("trs_of_index failed")
;;

let redtrs_of_index n =
 try Hashtbl.find ht_iredtrss n
 with Not_found -> failwith ("redtrs_of_index failed")
;;

let trs_of_index = St.take_time St.t_cache trs_of_index

let contains n m =
 try Hashtbl.find ht_contains (n,m)
 with Not_found ->
  let rn = trs_of_index n in
  let rm = trs_of_index m in
  let c = Listset.subset rm rn in
  Hashtbl.add ht_contains (n,m) c;
  c
;;

let contains n = St.take_time St.t_cache (contains n)

let store_rule_var ctx lr =
  let v = mk_fresh_bool_var ctx in
  if not (Rule.is_rule lr) then require (!! v);
  rule_vars :=  (lr, v) :: !rule_vars;
  v 
;;

let store_rule_vars ctx rls = List.iter (ignore <.> store_rule_var ctx) rls

let store_eq_var ctx lr =
  let v = mk_fresh_bool_var ctx in
  let vi = mk_int_var ctx ("eqw"^(string_of_int !wc)) in
  wc := !wc + 1;
  eq_vars := (lr, (v, vi)) :: !eq_vars;
  (v, vi) 
;;

let store_eq_vars ctx rls = List.iter (ignore <.> store_eq_var ctx) rls

let find_rule rl =
 try snd (List.find (fun (st,_) -> Rule.variant st rl) !rule_vars)
 with Not_found -> failwith ("no rule variable for " ^ (Rule.to_string rl))
;;

let rule_var ctx rl =
  try snd (List.find (fun (st,_) -> Rule.variant st rl) !rule_vars)
  with Not_found -> store_rule_var ctx rl
;;

let eq_variant (l,r) st = Rule.variant st (l,r) || Rule.variant st (r,l)

let find_eq rl =
 try
 fst (snd (List.find (fun (st,_) -> eq_variant st rl) !eq_vars))
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

let find_strict_var = Hashtbl.find strict_vars

let find_weak_var = Hashtbl.find weak_vars

let get_var h ctx (i,r) = 
 if Hashtbl.mem h (i,r) then Hashtbl.find h (i,r)
 else let v = mk_fresh_bool_var ctx in Hashtbl.add h (i,r) v; v
;;

let get_strict_var = get_var strict_vars

let get_weak_var = get_var weak_vars

let get_all_strict k =
 Hashtbl.fold (fun (i,r) v l -> if i=k then (r,v)::l else l) strict_vars []

let find_trs_var n =
 try Hashtbl.find ht_trsvars n
 with Not_found -> failwith ("trsvar "^(string_of_int n)^" not found")
;;

let find_trs_var = St.take_time St.t_cache find_trs_var

let store_trs trs =
 trscount := !trscount+1;
 let n = !trscount in
 Hashtbl.add ht_itrss n trs;
 Hashtbl.add ht_trssi trs n;
 List.iter (fun rl -> Hashtbl.add ht_was_oriented rl true) trs;
 n
;;

let was_oriented rule = Hashtbl.mem ht_was_oriented rule

let store_redtrs trs n = Hashtbl.add ht_iredtrss n trs

let store_trs = St.take_time St.t_cache store_trs

let assert_rule k f =
 if not (Hashtbl.mem ht_rlycs k) then (f k; Hashtbl.add ht_rlycs k true)
;;

let assert_with ctx f ce =
 let assert_constr (l,r) =
  let c (s,t) = (find_rule (s,t)) <=>> (f ctx s t) in
  require (c (l,r));
  require (c (r,l))
 in
 let consider (lr,_) = assert_rule lr assert_constr in
 List.iter consider ce
;;

let decode_print m i =
 let s = Hashtbl.fold (fun (j,rl) v l -> if i=j then (rl,v)::l else l) strict_vars [] in
 let s' = [ rl | (rl,v) <- s; eval m v ] in
 let w = Hashtbl.fold (fun (j,rl) v l -> if i=j then (rl,v)::l else l) weak_vars [] in
 let w' = [ rl | (rl,v) <- w; eval m v ] in
 Format.printf "Strict %i: \n@[ %a@]\n" i Rules.print s';
 Format.printf "Weak %i: \n@[ %a@]\n" i Rules.print w'
;;
