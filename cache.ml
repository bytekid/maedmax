(*** MODULES *****************************************************************)
module St = Statistics

(*** OPENS *******************************************************************)
open Yices
open Yicesx
open Rewriting
open Constraint

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
let ht_trsvars : (int, Yices.expr) Hashtbl.t = Hashtbl.create 128;;

(* bool and int Yices variable for each equation (only for comp setting) *)
let eq_vars : (Rule.t * (Yices.expr * Yices.expr)) list ref = ref [];;
(* Yices variable for each rule *)
let rule_vars : (Rule.t * Yices.expr) list ref = ref [];;
(* variables for strategy stage and strict rules *)
let strict_vars : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 128
(* variables for strategy stage and weak rules *)
let weak_vars : (int * Rule.t, Yices.expr) Hashtbl.t = Hashtbl.create 128

(* Yices variable for each constraint encountered at some point *)
let ht_cvars : (Constraint.c, Yices.expr) Hashtbl.t = Hashtbl.create 100;;

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
 Hashtbl.clear ht_cvars;
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

let find_rule lr =
 try
 snd (List.find (fun (st,_) -> Rule.variant st lr) !rule_vars)
 with Not_found -> (Format.printf "%a" Rule.print lr; failwith "no rule var for")
;;

let eq_variant (l,r) st = Rule.variant st (l,r) || Rule.variant st (r,l)

let find_eq lr =
 try
 fst (snd (List.find (fun (st,_) -> eq_variant st lr) !eq_vars))
 with Not_found -> (Format.printf "%a" Rule.print lr; failwith "no eq var for")
;;

let find_eq_weight lr =
 try
 snd (snd (List.find (fun (st,_) -> eq_variant st lr) !eq_vars))
 with Not_found -> (Format.printf "%a" Rule.print lr; failwith "no eq var for")
;;

let rec store_rule_vars ctx rls =
 let add lr =
   if not (List.exists (fun (st,_) -> Rule.variant st lr) !rule_vars) then
    let v = mk_fresh_bool_var ctx in
    if not (Rule.is_rule lr) then assert_simple ctx (ynot ctx v);
    rule_vars :=  (lr, v) :: !rule_vars
 in List.iter add rls
;;

let rec store_eq_vars ctx rls =
 let add lr =
   if not (List.exists (fun (st,_) -> eq_variant st lr) !eq_vars) then
    let v = mk_fresh_bool_var ctx in
    let ty  = mk_type ctx int_type_name in
    let n = "eqw"^(string_of_int !wc) in
    let d = mk_var_decl ctx n ty in
    let vi = mk_var_from_decl ctx d in
    wc := !wc + 1;
    eq_vars :=  (lr, (v,vi)) :: !eq_vars
 in List.iter add rls
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
  let c (s,t) = yimp ctx (find_rule (s,t)) (f ctx s t) in
  assert_simple ctx (c (l,r));
  assert_simple ctx (c (r,l))
 in
 let consider (lr,_) = assert_rule lr assert_constr in
(* let consider (lr,_) =assert_constr lr in *)
 List.iter consider ce
;;

let decode m i =
 let s = Hashtbl.fold (fun (j,rl) v l -> if i=j then (rl,v)::l else l) strict_vars [] in
 let s' = [ rl | (rl,v) <- s; yeval m v ] in
 let w = Hashtbl.fold (fun (j,rl) v l -> if i=j then (rl,v)::l else l) weak_vars [] in
 let w' = [ rl | (rl,v) <- w; yeval m v ] in
 Format.printf "Strict %i: \n@[ %a@]\n" i Rules.print s';
 Format.printf "Weak %i: \n@[ %a@]\n" i Rules.print w'
;;
