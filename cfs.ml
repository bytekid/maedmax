
(*** MODULES *****************************************************************)
module St = Statistics
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yices
open Yicesx

(*** GLOBALS *****************************************************************)
(* signature *)
let funs = ref []
(* map function symbol and strategy stage to bool whether its counted *)
let decreasing : (int * Signature.sym, Yices.expr) Hashtbl.t
 = Hashtbl.create 32
let all_weak : Yices.expr option ref = ref None  

(*** FUNCTIONS ***************************************************************)
let passthru () = 
 match !all_weak with Some x -> x | None -> failwith "Cfs.passthru: all_weak not initialized"

let decrease is_strict (l,r) f =
 let rec count = function
  | V _ -> 0
  | F (f', ts) ->
   List.fold_left (fun s ti -> s + count ti) (if f=f' then 1 else 0) ts
 in (Rule.is_non_duplicating (l,r)) && 
  (if is_strict then count l > (count r) else count l >= (count r))
;;

let strict_decrease = decrease true

let weak_decrease = decrease false

let dec (ctx,k) f = 
 try Hashtbl.find decreasing (k,f)
 with Not_found ->
  let x = mk_fresh_bool_var ctx in Hashtbl.add decreasing (k,f) x; x
;;

let gt (ctx,k) s t =
 let np = ynot ctx (passthru ()) in
 yand ctx np (ybig_or ctx [ dec (ctx,k) f | f <- !funs; strict_decrease (s,t) f ])
;;

let ge (ctx,k) s t =
 yor ctx (passthru ()) (ybig_or ctx [ dec (ctx,k) f | f <- !funs; weak_decrease (s,t) f ])
;;

let init (ctx,k) fs = 
 all_weak := Some (mk_fresh_bool_var ctx); (* passthru, eg if R duplicating *)
 funs := List.map fst fs; 
 let zero, one = mk_num ctx 0, mk_num ctx 1 in
 (* only one function symbol may decrease *)
 mk_ge ctx one (ysum ctx [mk_ite ctx (dec (ctx,k) f) one zero | f <- !funs ])
;;

let decode k m = 
 let dps = [ rl | rl,v <- C.get_all_strict 1; evaluate_in_model m v == True ] in
 let rls = [ rl | rl,v <- C.get_all_strict 0; evaluate_in_model m v == True] in
 let fs = Rules.functions (dps @ rls) in
 let is_decreasing f = 
  try evaluate_in_model m (Hashtbl.find decreasing (k,f)) = True
  with Not_found -> false
 in
 if evaluate_in_model m (passthru ()) = True then
  Format.printf "(no symbol count decrease)\n "
 else (
  Format.printf "symbol count decrease: @\n ";
  try 
   let f = List.find is_decreasing fs in
   Format.printf "%s\n%!" (Signature.get_fun_name f)
  with Not_found ->
   Format.printf "none\n%!"
  )
;;
