
(*** MODULES *****************************************************************)
module C = Cache
module Logic = Settings.Logic

(*** OPENS *******************************************************************)
open Term
open Logic

(*** GLOBALS *****************************************************************)
(* signature *)
let funs : (Signature.sym * int) list ref = ref []
(* map function symbol and strategy stage to bool whether its counted *)
let decreasing : (int * Signature.sym, Logic.t) Hashtbl.t = Hashtbl.create 32
let all_weak : Logic.t option ref = ref None  

(*** FUNCTIONS ***************************************************************)
let (<>=>) = Logic.Int.(<>=>)
let passthru () = match !all_weak with
    Some x -> x 
  | None -> failwith "Cfs.passthru: all_weak not initialized"

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
  let np = !! (passthru ()) in
  np <&> (big_or ctx [ dec (ctx,k) f | f,_ <- !funs; strict_decrease (s,t) f ])
;;

let ge (ctx,k) s t =
  let pass = !! (passthru ()) in
  pass <|> (big_or ctx [ dec (ctx,k) f | f,_ <- !funs; weak_decrease (s,t) f ])
;;

let init (ctx,k) fs = 
 all_weak := Some (mk_fresh_bool_var ctx); (* passthru, eg if R duplicating *)
 funs := fs; 
 let zero, one = Int.mk_num ctx 0, Int.mk_num ctx 1 in
 (* only one function symbol may decrease *)
 one <>=> (Int.sum ctx [ite (dec (ctx,k) f) one zero | f,_ <- !funs ])
;;

let decode_string k m = 
 let dps = [ rl | rl,v <- C.get_all_strict 1; eval m v ] in
 let rls = [ rl | rl,v <- C.get_all_strict 0; eval m v ] in
 let fs = Rules.functions (dps @ rls) in
 let is_decreasing f = 
  try eval m (Hashtbl.find decreasing (k,f))
  with Not_found -> false
 in
 if eval m (passthru ()) then
  "(no symbol count decrease)\n "
 else (
  "symbol count decrease: @\n " ^
  try let f = List.find is_decreasing fs in (Signature.get_fun_name f)
  with Not_found -> "none"
  )
;;

let decode_print k m = Format.printf "%s\n%!" (decode_string k m)

let decode k m =
  let is_decreasing (f,_) = 
   try eval m (Hashtbl.find decreasing (k,f))
   with Not_found -> false
  in
  let gt s t =
    try strict_decrease (s,t) (fst (List.find is_decreasing !funs))
    with Not_found -> false
  in
  let bot =  match [ c | c,a <- !funs; a = 0] with
      [] -> None
    | c :: cs -> Some c
  in
  object
    method bot = bot
    method gt = gt
    method smt_encode ctx = Logic.mk_false ctx
    method to_string = decode_string k m
    method print = fun _ -> decode_print k m
    method to_xml = Xml.Element("cfs", [], [])
    method print_params = Order.default#print_params
  end
;;
