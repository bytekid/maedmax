
(*** MODULES *****************************************************************)
module St = Statistics
module Sig = Signature
module C = Cache

(*** OPENS *******************************************************************)
open Term
open Yices
open Yicesx

(*** GLOBALS *****************************************************************)
(* signature *)
let funs = ref []

(* map function symbol and strategy stage to variable for weight *)
let weights : (int * Signature.sym, Yicesx.t) Hashtbl.t
 = Hashtbl.create 32
let w0 : Yicesx.t option ref = ref None

(* map function symbol and strategy stage to bool whether its counted *)
let decreasing : (int * Signature.sym, Yicesx.t) Hashtbl.t
 = Hashtbl.create 32
let all_weak : Yicesx.t option ref = ref None  

(*** FUNCTIONS ***************************************************************)
let w k f = Hashtbl.find weights (k,f)

let the = function Some x -> x | _ -> failwith "Cfs.the: no value"

let weight k t =
 let rec weight = function
  | V _ -> the !w0 (* w0 = 1 *)
  | F(f,ss) -> sum1 ((w k f) :: [weight si | si <- ss ])
 in weight t
;;

let decrease is_strict (ctx,k) (l,r) =
 if Rule.is_non_duplicating (l,r) then
   (if is_strict then (<>>) else (<>=>)) (weight k l) (weight k r)
 else mk_false ctx
;;

let strict_decrease = decrease true

let weak_decrease = decrease false

let gt (ctx,k) s t = (!! (the !all_weak)) <&> (strict_decrease (ctx,k) (s,t))

let ge (ctx,k) s t = (the !all_weak) <|> (weak_decrease (ctx,k) (s,t))

let init (ctx,k) fs = 
  let add (f,_) =
   let xw = mk_int_var ctx ((Sig.get_fun_name f) ^ "-"^(string_of_int k)) in
   Hashtbl.add weights (k,f) xw;
   (xw <>=> (mk_zero ctx))
  in 
 all_weak := Some (mk_fresh_bool_var ctx); (* passthru, eg if R duplicating *)
 w0 := Some (mk_one ctx);
 funs := fs;
 big_and ctx (List.map add fs)
;;

let decode_print k m = 
 let dec (f, a) =
  let v = Hashtbl.find weights (k,f) in
  let fn = Signature.get_fun_name f in
  Format.printf " w(%s) = %i\n%!" fn (eval_int_var m v)
 in 
 if eval m (the !all_weak) then
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
