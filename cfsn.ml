
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

(* map function symbol and strategy stage to variable for weight *)
let weights : (int * Signature.sym, Yices.var_decl * Yices.expr) Hashtbl.t
 = Hashtbl.create 32

(* map function symbol and strategy stage to bool whether its counted *)
let decreasing : (int * Signature.sym, Yices.expr) Hashtbl.t
 = Hashtbl.create 32
let all_weak : Yices.expr option ref = ref None  

(*** FUNCTIONS ***************************************************************)
let w k f = snd (Hashtbl.find weights (k,f))

let weight (ctx,k) t =
 let rec weight = function
  | V _ -> mk_num ctx 0 (* w0 = 1 *)
  | F(f,ss) -> ysum ctx ((w k f) :: [weight si | si <- ss ])
 in weight t
;;

let passthru () = 
 match !all_weak with Some x -> x | None -> failwith "Cfs.passthru: all_weak not initialized"

let decrease is_strict (ctx,k) (l,r) =
 if Rule.is_non_duplicating (l,r) then
   (if is_strict then ygt else yge) ctx (weight (ctx,k) l) (weight (ctx,k) r)
 else yfalse ctx
;;

let strict_decrease = decrease true

let weak_decrease = decrease false

let gt (ctx,k) s t = yand ctx (ynot ctx (passthru ())) (strict_decrease (ctx,k) (s,t))

let ge (ctx,k) s t = yor ctx (passthru ()) (weak_decrease (ctx,k) (s,t))

let init (ctx,k) fs = 
  let add (f,_) =
   let s = (Signature.get_fun_name f) ^ "-"^(string_of_int k) in
   let ty  = mk_type ctx "int" in
   let dw = mk_var_decl ctx s ty in
   let xw = mk_var_from_decl ctx dw in
   Hashtbl.add weights (k,f) (dw,xw);
   (yge ctx xw (mk_num ctx 0))
  in 
 all_weak := Some (mk_fresh_bool_var ctx); (* passthru, eg if R duplicating *)
 funs := fs;
 ybig_and ctx (List.map add fs)
;;

let decode k m = 
 let dec (f, a) =
  let (v,_) = Hashtbl.find weights (k,f) in
  let w = Int32.to_int (get_int_value m v) in
  let fn = Signature.get_fun_name f in
  Format.printf " w(%s) = %i\n%!" fn w
 in 
 if evaluate_in_model m (passthru ()) = True then
  Format.printf "(no symbol count decrease)\n "
 else (
  Format.printf "symbol count decrease: @\n ";
  List.iter dec !funs 
  )
;;

let clear () = 
 Hashtbl.clear weights;
 Hashtbl.clear decreasing;
 all_weak := None
;;
