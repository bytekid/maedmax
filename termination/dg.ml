(*** OPENS *******************************************************************)
open Yices
open Yicesx
open Rewriting
(*open TerminationStrategy*)

(*** MODULES *****************************************************************)
module C = Cache
module T = Term

(*** TYPES *******************************************************************)
(*** GLOBALS *****************************************************************)
let t_edge : (int * Rule.t * Rule.t, Yicesx.t) Hashtbl.t = Hashtbl.create 128
let cycle_id :  (int * Signature.sym, Yicesx.t) Hashtbl.t = Hashtbl.create 128

let varcount = ref 0

let t_scc : (int * Signature.sym, Yicesx.t) Hashtbl.t = Hashtbl.create 128

(*** FUNCTIONS ***************************************************************)

let x_edge ctx j p1 p2 =
 try Hashtbl.find t_edge (j,p1,p2) with Not_found ->
  let x = mk_fresh_bool_var ctx in 
  Hashtbl.add t_edge (j,p1,p2) x;
  x
;;

let x_scc ctx j f =
 try Hashtbl.find t_scc (j,f) with Not_found ->
  let fresh_name () = incr varcount; "scc"^(string_of_int !varcount) in
  let x = mk_int_var ctx (fresh_name ()) in
  Hashtbl.add t_scc (j,f) x;
  x
;;

let init_without_sccs ctx = ()

let init_with_sccs ctx fs j k =
 let xfs = [x_scc ctx j f | f,_ <- fs] in
 let n0, nk = mk_num ctx 0, mk_num ctx k in
 big_and1 [nk <>> xf <&> (xf <>=> n0) | xf <- xfs]
;;


let add f = List.map (fun fs -> f :: fs) 
let subst (x,t) = List.map (Rule.substitute [x,t]) 

let rec uf = function
  | [] -> [[]]
  | (Term.V _ , _) :: es -> uf es
  | (Term.F(f,_) as t, Term.V x) :: es -> add f (uf es) @ (uf (subst (x,t) es))
  | (Term.F(f, ts), Term.F(g,us)) :: es when f = g ->
   add f (uf es) @ (uf ((List.map2 (fun t u -> (t,u)) ts us) @ es))
  | (Term.F(f, _), Term.F(_,_)) :: es -> add f (uf es)
;;

let has_edge ctx (_,r1) (l2,_) =
 try if  Term.root r1 = Term.root l2 then mk_true ctx else mk_false ctx with
 _ -> failwith "edge_exists: variable found"
;;

let has_edge_bool (_,r1) (l2,_) = Term.root r1 = Term.root l2

let has_edge' ctx (_,t) (u,_) =
 try
  match t,u with
  | Term.F (f,ts), Term.F (g,us) when f = g ->
   let fss = uf (List.map2 (fun t u -> (t,u)) ts us) in
   big_or1 [ big_and1 [Dp.x_def f | f <- fs] | fs <- fss ]
  | _ -> mk_false ctx 
 with _ -> failwith "edge_exists: variable found"
;;




let x_w ctx j f =
 try Hashtbl.find cycle_id (j,f) with Not_found ->
  let fresh_name () = incr varcount; "wgt"^(string_of_int !varcount) in
  let x = mk_int_var ctx (fresh_name ()) in
  Hashtbl.add cycle_id (j,f) x;
  x
;;

let decode j m =  ()
