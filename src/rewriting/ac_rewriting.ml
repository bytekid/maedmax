open Term
open Subst

(*** GLOBALS *****************************************************************)
let ht_match : (Term.t * Term.t, Term.subst list) Hashtbl.t = 
 Hashtbl.create 40

let lookup f ht x =
 try Hashtbl.find ht x
 with Not_found -> 
  let y = f x in
  Hashtbl.add ht x y;
  y
;;

(*** FUNCTIONS ***************************************************************)
(* extended rewriting with A-matching *)
let rec rewrite_root ac t = function
  | [] -> false, t
  | (l, r) :: rules ->
      (* let matcher = Ac_subst.matcher ac (l,t) in *)
      (* let _ = Format.printf "computing ac-matcher@." in *)
      let matcher = lookup (Ac_subst.matcher ac) ht_match (l,t) in 
      (* let _ = Format.printf "ac-matcher found@." in *)
      begin
	match matcher with
	| [] -> rewrite_root ac t rules
	| m :: _ ->
	    true, substitute m r
      end

let rec remove_first elem = function
  | [] -> []
  | h :: t -> if elem = h then t else h :: (remove_first elem t)

let rec remove_arg ls = function
  | [] -> ls
  | h :: t ->
      let ls1 = remove_first h ls in
      remove_arg ls1 t

let rec find_redex ac f args rules = function
  | [] -> false, V (Signature.fun_called "false")
  | ls :: lss ->
      let b,u = rewrite_root ac (Term.flatten ac (F(f, ls))) rules in
      if b then b, Term.flatten ac (F(f, u :: (remove_arg args ls)))
      else
       find_redex ac f args rules lss

let rec rewrite_aux ac rules = function
  | V _ as t -> false, t
  | F (f, ts) ->
      let l = [ rewrite_aux ac rules ti | ti <- ts ] in
      let ls = List.map snd l in 
      let b, u = rewrite_root ac (Term.flatten ac (F (f, [ t | _, t <- l ]))) rules in
      if b || List.exists (fun (b, _) -> b) l then true, u
      else 
       if not (List.mem f ac) then false, u
       else 
        (* f is ac. Try to find a redex by taking all possible args *) 
        (* assumes ac-symbols are always binary *)
        let pow_ls = [ arg_ls | arg_ls <- Listx.power ls; List.length arg_ls >= 2 ] in
        let b,t = find_redex ac f ls rules pow_ls in 
        if b then b, Term.flatten ac t else b, Term.flatten ac (F(f,ls))
	

let rec nf ac rules t =
  let t_flat = Term.flatten ac t in 
  (* let _ = Format.printf "Rewriting term %a@." Term.print t in *)
  let b, u = rewrite_aux ac rules t_flat in
  if b then nf ac rules (Term.flatten ac u) else t_flat

(* check if s ==_AC t *)

let rec remove_first eq elem = function
  | [] -> []
  | h :: t -> if eq elem h then t else h :: (remove_first eq elem t)

let rec exists_eq eq elem = function
  | [] -> false
  | h :: tt ->
      if eq elem h 
      then true else exists_eq eq elem tt

let remove_common_args eq l1 l2 =
  let rec rca1 ll acc = function
    | [] -> ll, List.rev acc
    | h :: t ->
        if exists_eq eq h ll then
          let lln = remove_first eq h ll in rca1 lln acc t
        else rca1 ll (h::acc) t
  in
  rca1 l1 [] l2

let rec equal ac s t =
  let s_f = Term.flatten ac s in
  let t_f = Term.flatten ac t in 
  match s_f,t_f with 
  | V x, V y -> if x = y then true else false
  | F(f,ff),F(g,gg) when f = g ->
      let aa,bb = remove_common_args (equal ac) ff gg in
      if aa = [] && bb = [] then true else false
  | _, _ -> false

(* 

let t1 = Tplparser.parse_t "f(x,a(),g(f(f(z,b(),z))),e(),x)"
let t2 = Tplparser.parse_t "f(f(a(),g(f(b(),z,z))),e(),x,x)"
equal_ac ["f";"g"] t1 t2

*)


(* 

input trs, get (trs \setminus ac, ac_sym, ac rules)

*)

let make_assoc1 f x y z = 
 (F(f,[F(f,[V x; V y]);V z]),F(f,[V x; F(f,[V y; V z])]))

let make_assoc2 f x y z = 
   (F(f,[V x; F(f,[V y; V z])])),F(f,[F(f,[V x; V y]);V z])

let make_comm f x y = 
 F(f,[V y;V x]),F(f,[V x;V y])

let is_ac f rr =
  let x,y,z = Signature.fresh_var (), Signature.fresh_var (), Signature.fresh_var () in
  let fc = make_comm f x y in
  let fa1 = make_assoc1 f x y z in
  let fa2 = make_assoc2 f x y z in 
 List.exists (fun rl -> Rule.variant rl fc) rr &&
 List.exists (fun rl -> Rule.variant rl fa1 || Rule.variant rl fa2) rr

let find_ac rr = 
 let fs = Rules.signature rr in 
 let x,y,z = Signature.fresh_var (), Signature.fresh_var (), Signature.fresh_var () in

 let ac_sym = [ f | f,n <- fs; n=2; is_ac f rr ] in
 if ac_sym = [] then None
 else 
  let ac_rules_all = List.flatten 
     [ [ make_comm f x y; make_assoc1 f x y z; make_assoc2 f x y z] | f <- ac_sym ] 
  in 
  let ac_rules_1 = List.flatten 
   [ [ make_comm f x y; make_assoc1 f x y z] | f <- ac_sym ] 
  in
  Some (Rules.remove rr ac_rules_all, ac_sym, ac_rules_1, ac_rules_all)
  
