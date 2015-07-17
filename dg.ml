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
let t_edge : (int * Rule.t * Rule.t,Yices.expr) Hashtbl.t = Hashtbl.create 128
let cycle_id :  (int * Signature.sym,Yices.expr * Yices.var_decl) Hashtbl.t = 
 Hashtbl.create 128

let varcount = ref 0

let t_scc : (int * Signature.sym,Yices.expr * Yices.var_decl) Hashtbl.t 
 = Hashtbl.create 128

(*** FUNCTIONS ***************************************************************)

let x_edge ctx j p1 p2 =
 try Hashtbl.find t_edge (j,p1,p2) with Not_found ->
  let x = mk_fresh_bool_var ctx in 
  Hashtbl.add t_edge (j,p1,p2) x;
  x
;;

let x_scc ctx j f =
 try fst (Hashtbl.find t_scc (j,f)) with Not_found ->
  let fresh_name () = incr varcount; "scc"^(string_of_int !varcount) in
  let ty  = mk_type ctx "int" in
  let n = fresh_name () in
  let d = mk_var_decl ctx n ty in
  let x = mk_var_from_decl ctx d in
  Hashtbl.add t_scc (j,f) (x,d);
  x
;;

let init_without_sccs ctx = ()

let init_with_sccs ctx fs j k =
 let fs = [f | f,_ <- fs] in
 let xf f = x_scc ctx j f in
 let n0, nk = mk_num ctx 0, mk_num ctx k in
 let cs = [yand ctx (ygt ctx nk (xf f)) (yge ctx (xf f) n0) | f <- fs] in
 ybig_and ctx cs
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
 try if  Term.root r1 = Term.root l2 then ytrue ctx else yfalse ctx with
 _ -> failwith "edge_exists: variable found"
;;

let has_edge_bool (_,r1) (l2,_) = Term.root r1 = Term.root l2

let has_edge' ctx (_,t) (u,_) =
 try
  match t,u with
  | Term.F (f,ts), Term.F (g,us) when f = g ->
   let fss = uf (List.map2 (fun t u -> (t,u)) ts us) in
   ybig_or ctx [ ybig_and ctx [Dp.x_def f | f <- fs] | fs <- fss ]
  | _ -> yfalse ctx 
 with _ -> failwith "edge_exists: variable found"
;;



let fresh_name () = incr varcount; "wgt"^(string_of_int !varcount)

let x_w ctx j f =
 try fst (Hashtbl.find cycle_id (j,f)) with Not_found ->
  let ty  = mk_type ctx "int" in
  let n = fresh_name () in
  let d = mk_var_decl ctx n ty in
  let x = mk_var_from_decl ctx d in
  Hashtbl.add cycle_id (j,f) (x,d);
  x
;;

let decode j m =
 let w = Hashtbl.fold (fun k (_,v) l -> (Yices.get_int_value m v,k)::l) cycle_id [] in
(* let is_strict rl = yeval m (C.find_strict_var (j, rl)) in
 let w' = [(c,st) | (c,(j',st)) <- w; j' = j; is_strict st] in
 let print_cycle (w,ps) =
  Format.printf "cycle %i:\n @.%a@.\n" (Int32.to_int w) Rules.print ps
 in
 List.iter print_cycle (Listx.group w');*) ()
;;

let decode_scc j k m =
 let w = Hashtbl.fold (fun k (_,v) l -> (Yices.get_int_value m v,k)::l) t_scc [] in
 let is_strict rl = yeval m (C.find_strict_var (j, rl)) in
(* let w' = [(c,st) | (c,(j',st)) <- w; j' = j; is_strict st] in
 let print_scc (w,ps) =
  Format.printf "SCC %i: @\n @[%a@]@\n" (Int32.to_int w) Rules.print ps;
  List.iter (fun r -> Format.printf "Rule %a, w: %i\n" 
   Rule.print r (Int32.to_int (Yices.get_int_value m (snd (Hashtbl.find cycle_id (j,r)))))) ps (*;
  ignore [ Format.printf "edge from %a to %a: %i\n" Rule.print p1 Rule.print p2 (if has_edge_aux p1 p2 then 1 else 0) | p1 <- ps; p2 <- ps ]*)
 in
 List.iter print_scc (Listx.group w');*) ()
;;
