(*** TYPES *******************************************************************)
type f =
    True
  | False
  | Not of f
  | And of f list
  | Or of f list
  | Xor of f * f
  | Implies of f * f
  | Iff of f * f
  | Lt of t * t
  | Leq of t * t
  | Eq of t * t
  | BoolVar of string
and t =
    Num of int
  | IntVar of string
  | Plus of t list
  | Ite of f * t * t

(*** GLOBALS *****************************************************************)
let var_count = ref 0

let hard_asserts : f list list ref = ref [[]]

let soft_asserts : (f * int) list list ref = ref [[]]

(*** FUNCTIONS ***************************************************************)
let is_true f = (f == True)

let is_false f = (f == False)

let is_zero x = (x == Num 0)

let mk_fresh_bool_var _ =
  let x = "_b" ^ (string_of_int !var_count) in
  var_count := !var_count + 1;
  BoolVar x
;;

let to_string f =
  let rec strt = function
    | Num n -> string_of_int n
    | IntVar name -> name
    | Plus ts ->
      "(+ " ^ (List.fold_left (fun s t -> s ^ (strt t) ^ " ")) "" ts ^ ")"
    | Ite(b, t1, t2) ->
      "(ite " ^ (str b) ^ " "^ (strt t1) ^ " " ^ (strt t2) ^  ")"
  and str = function
    | True -> "true"
    | False -> "false"
    | Not f -> "(not " ^ (str f) ^ ")"
    | And fs ->
      "(and " ^ (List.fold_left (fun s t -> s ^ (str t) ^ " ")) "" fs ^ ")"
    | Or fs ->
      "(or " ^ (List.fold_left (fun s t -> s ^ (str t) ^ " ")) "" fs ^ ")"
    | Xor(f1,f2) -> "(xor " ^ (str f1) ^ " " ^ (str f2) ^ ")"
    | Implies(f1,f2) -> "(implies " ^ (str f1) ^ " " ^ (str f2) ^ ")"
    | Iff(f1,f2) -> "(= " ^ (str f1) ^ " " ^ (str f2) ^ ")"
    | Lt(t1,t2) -> "(< " ^ (strt t1) ^ " " ^ (strt t2) ^ ")"
    | Leq(t1,t2) -> "(<= " ^ (strt t1) ^ " " ^ (strt t2) ^ ")"
    | Eq(t1,t2) -> "(= " ^ (strt t1) ^ " " ^ (strt t2) ^ ")"
    | BoolVar name -> name
  in str f
;; 

let visit visit_f visit_t f =
  let rec vis_t = function
    | Plus ts -> List.fold_left (fun acc t -> vis_t t @ acc) [] ts
    | Ite(b, t1, t2) -> vis_f b @ (vis_t t1) @ (vis_t t2)
    | t -> visit_t t
  and vis_f = function
    | Not f -> vis_f f
    | And fs -> List.fold_left (fun acc f -> vis_f f @ acc) [] fs
    | Or fs -> List.fold_left (fun acc f -> vis_f f @ acc) [] fs
    | Xor(f1,f2) -> vis_f f1 @ (vis_f f2)
    | Implies(f1,f2) -> vis_f f1 @ (vis_f f2)
    | Iff(f1,f2) -> vis_f f1 @ (vis_f f2)
    | Lt(t1,t2) -> vis_t t1 @ (vis_t t2)
    | Leq(t1,t2) -> vis_t t1 @ (vis_t t2)
    | Eq(t1,t2) -> vis_t t1 @ (vis_t t2)
    | f -> visit_f f
  in vis_f f
;;

let visit_all vf vt = List.fold_left (fun acc f -> visit vf vt f @ acc) []

let bool_vars fs =
  let vs = visit_all (function BoolVar s -> [s] | _ -> []) (fun _ -> []) fs in
  Listx.unique vs
;;

let int_vars fs =
  let vs = visit_all (fun _ -> []) (function IntVar s -> [s] | _ -> []) fs in
  Listx.unique vs
;;

let (!!) = function
  | True -> False
  | False -> True
  | Not f -> f
  | f -> Not f
;;

let (<|>) x y =
  match x,y with
  | True, _
  | _, True -> True
  | False, _ -> y
  | _, False -> x
  | _ -> Or [x;y]
;;

let (<&>) x y =
  match x,y with
  | False, _
  | _, False -> False
  | True, _ -> y
  | _, True -> x
  | _ -> And [x;y]
;;

let (<=>>) x y =
match x,y with
| False, _ -> True
| _ -> Implies(x,y)

let (<+>) x y =
  match x,y with
  | Num 0, _ -> y
  | _, Num 0 -> x
  | _ -> Plus [x;y]

let iff x y = Iff(x,y)

let big_binop p_ann ann p_neut neut op xs =
  if List.exists p_ann xs then ann
  else match List.filter (fun x -> not (p_neut x)) xs with
      []  -> neut
    | [x] -> x
    | xs  -> (op xs)
;;

let big_binop1 big_binop = function
  | [] -> failwith "Smtlib.big_binop1: empty argument list"
  | x :: xs -> big_binop (x :: xs)
;;

let big_and = big_binop is_false False is_true True (fun fs -> And fs)

let big_and1 = big_binop1 big_and

let big_or = big_binop is_true True is_false False (fun fs -> Or fs)

let big_or1 = big_binop1 big_or

let sum = big_binop (fun _ -> false) (Num 0) is_zero (Num 0) (fun fs -> Plus fs)

let sum1 = big_binop1 sum

let (<>>) x y = Lt(y,x)

let (<>=>) x y = Leq(y,x)

let (<=>) x y = Eq(x,y)

let (<!=>) x y = Not(Eq(x,y))

let ite c t f = Ite(c,t,f)

let require f =
  match !hard_asserts with
  | [] -> failwith "Smtlib.require: no context"
  | fs :: hard_asserts' -> hard_asserts := (f :: fs) :: hard_asserts'
;;

let assert_weighted f n =
    match !soft_asserts with
    | [] -> failwith "Smtlib.assert_weighted: no context"
    | fs :: soft_asserts' -> soft_asserts := ((f,n) :: fs) :: soft_asserts'
  ;;

let push _ =
  soft_asserts := [] :: !soft_asserts;
  hard_asserts := [] :: !hard_asserts
;;

let pop _ =
  match !hard_asserts, !soft_asserts with
  | _ :: hard_asserts', _ :: soft_asserts' -> (
    soft_asserts := soft_asserts';
    hard_asserts := hard_asserts')
  | _ -> failwith "Smtlib.pop: invalid context"
;;

let state_to_string _ =
  let s = "" in
  let hard = List.concat !hard_asserts in
  let soft = List.concat !soft_asserts in
  let all = List.map fst soft @ hard in
  let declare typstr s n = s ^ "(declare-const " ^ n ^ " " ^ typstr ^ ")\n" in
  let s = List.fold_left (declare "Bool") s (bool_vars all) in
  let s = List.fold_left (declare "Int") s (int_vars all) in
  let assert_hard s f = s ^ "(assert " ^ (to_string f) ^ ")\n" in
  let s = List.fold_left assert_hard s hard in
  let assert_soft s (f,n) =
    let sn = string_of_int n in
    s ^ "(assert-soft " ^ (to_string f) ^ " :weight " ^ sn ^ ")\n"
  in
  let s = List.fold_left assert_soft s soft in
  let s = s ^ "(check-sat)\n" in
  s
;;

let benchmark suffix =
  if !hard_asserts = [[]] && !soft_asserts = [[]] then ()
  else (
    (*let bfile = Filename.temp_file "maedmax_benchmarks/" ".smt2" in*)
    let bname = (!Settings.input_file) ^ "_" ^ suffix in
    let bfile = "/tmp/maedmax_benchmarks/" ^ bname ^ ".smt2" in
    let out_channel = open_out bfile in
    Printf.fprintf out_channel "%s\n" (state_to_string ());
    close_out out_channel;
    Format.printf "Benchmark written to %s\n%!" bfile)
;;

let clear _ = soft_asserts := [[]]; hard_asserts := [[]];
(*
let check ctx = 
let max_sat ctx = 
let get_model =
let eval m x =
let eval_int_var m x =
let get_cost m =
*)
