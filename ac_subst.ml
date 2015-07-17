open Term

(*
let rec flatten_aux f_ac = function
  | V x as t -> [t]
  | F(f,ls) -> 
      let args_flat = List.flatten (List.map (flatten_aux f_ac) ls) in
      if List.mem f f_ac then args_flat else [F(f,args_flat)]

let flatten f_ac = function
  | V x as t -> t
  | F(f,ls) -> F(f,List.flatten (List.map (flatten_aux f_ac) ls))
*)

(*
let t = Tplparser.parse_t "f(f(a,a),a,f(g(u),y,x))";;
let t1 = Tplparser.parse_t "f(a,f(b,g(c)),f(y,y),z)";;
let t2 = Tplparser.parse_t "f(a,f(b,g(d)),f(z,z),x)";;

let h1 = Tplparser.parse_t "f(x,x,a(),a())"
let h2 = Tplparser.parse_t "f(g(y),g(a()),z,z)"
*)

let rec remove_first elem = function
  | [] -> []
  | h :: t -> if elem = h then t else h :: (remove_first elem t)

let remove_common_args l1 l2 =
  let rec rca1 ll acc = function
    | [] -> ll, List.rev acc
    | h :: t -> 
	if List.mem h ll then
          let lln = remove_first h ll in rca1 lln acc t
        else rca1 ll (h::acc) t
  in
  rca1 l1 [] l2
    
let group s t =
 match s,t with
 | F(f,ss), F(g,tt) when f = g ->
     let ss1,tt1 = remove_common_args ss tt in
     f, Listx.count ss1, Listx.count tt1
 | _ -> failwith "invalid arg in Ac.normalize"

(*
let f,ss,tt = group h1 h2
*)

let basic_sol ac h1 h2 = 
  let f, ss, tt = group (flatten ac h1) (flatten ac h2) in
  let bb1,bb2 = (List.map snd ss), (List.map snd tt) in
  let aa = List.map fst (ss @ tt) in 
  let bs = List.map (fun (x,y) -> x @ y) (Dio.basis bb1 bb2) in 
  (f, aa, bs)

(*
let f,aa,bs = basic_sol h1 h2
*)


let filterPreCond4 basic_sols aa = 
  let i1n = Listx.interval 0 ((List.length aa)-1) in
  let violates4 b i = (List.nth b i >= 2) && (not (is_variable (List.nth aa i))) in
  [ b | b <- basic_sols; not (List.exists (violates4 b) i1n) ]

(*
let bs1 = filterPreCond4 b aa
*)

let condition3 base aa =
 let base_ar = Array.of_list (List.map Array.of_list base) in
 let b = ref true in 
 for i=0 to (List.length aa) - 1 do
  let column_i = [ base_ar.(j).(i) | j <- Listx.interval 0 ((Array.length base_ar) - 1) ] in
  begin
  if List.for_all (fun x -> x=0) column_i 
  then b := false  
  end;
 done; !b

(*
let bss3 = [ bs | bs <- Listx.power bs2; bs <> [] ]
let bss4 = [ bs | bs <- bss3; condition3 bs aa ]
*)


let condition4 base aa =
  let base_ar = Array.of_list (List.map Array.of_list base) in
  let b = ref true in 
  for i=0 to (List.length aa) - 1 do
    if not (is_variable (List.nth aa i)) then
      let column_i = [ base_ar.(j).(i) | j <- Listx.interval 0 ((Array.length base_ar) - 1) ] in
      let sum = List.fold_left (+) 0 column_i in
      begin
	if not (sum = 1) then b := false
      end;
  done; !b

(*
let bss5 = [ bs | bs <- bss4; condition4 bs aa ]
*)

let apply phi (s,t) = Term.substitute phi s, Term.substitute phi t

let combine phi2 phi1 = 
  [ v, (Term.substitute phi2) t | v,t <- phi1 ]
@ [ v,t | v,t <- phi2; not (List.mem v (List.map fst phi1)) ]

let lookup i basis_var =
 [ List.nth b i, var | b,var <- basis_var; List.nth b i >= 1 ]

let rec make_term f acc = function
  | [] -> F(f,acc)
  | (n,s) :: tt ->
      let ls = [ s | i <- Listx.interval 1 n ] in
      make_term f (acc @ ls) tt
      
let make_term_or_sing f ls = 
  match ls with
  | [(n,t)] when n = 1 -> t
  | _ -> make_term f [] ls
  
let make_eqs f basis_var aa = 
 let n = (List.length aa) - 1 in 
 [ List.nth aa i, make_term_or_sing f n_var_ls | i <- Listx.interval 0 n; 
   n_var_ls <- [lookup i basis_var]; not (is_variable (List.nth aa i)) ]  

let s_of_v = function
  | V x -> x
  | _ -> failwith "invalid arg in Ac.s_of_v"

let make_sigma f basis_var aa =
 let n = (List.length aa) - 1 in 
 [ s_of_v (List.nth aa i), make_term_or_sing f n_var_ls | i <- Listx.interval 0 n; 
   n_var_ls <- [lookup i basis_var]; (is_variable (List.nth aa i)) ]  
  


let rec unify_set f i k sigma eqs =
  if i > k then sigma else
  let si,ti = List.nth eqs i in 
  let next_sigma = [ combine phi1 phi2 | phi2 <- sigma; 
		     phi1 <- f (Term.substitute phi2 si,Term.substitute phi2 ti) ] in
  unify_set f (i+1) k next_sigma eqs


let rec simplify_vt subst =
  let appears v sub1 =
    try 
      let _ = List.find (fun (x,y) -> List.mem v (Term.variables y)) sub1 in true 
    with Not_found -> false
  in
  let v,t = List.find (fun (x,y) -> appears x (Listset.remove (x,y) subst)) subst in 
  let subst1 = Listset.remove (v,t) subst in 
  [ w, Term.substitute [v,t] s | w,s <- subst1 ]


let rec simplify subst = 
 try 
  let subst1 = simplify_vt subst in
  simplify subst1
 with Not_found -> subst

let remove_vars vars subst =
 [ v,t | v,t <- subst; List.mem v vars ]

let filter_invalid subs =
 [ sub | sub <- subs; List.for_all (fun (x,y) -> not (List.mem x (Term.variables y))) sub ]

let rec powerset = function
 | [] -> [[]]
 | h::t -> List.fold_left (fun xs t -> (h::t)::t::xs) [] (powerset t);;

let rec unify ac = function
  | t1,t2 when t1 = t2 -> [[]]
  | (V x, t) 
  | (t, V x) when not (List.mem x (Term.variables t)) -> [[x,t]]
  | F(f,ss),F(g,tt) when f=g && not (List.mem f ac) ->
      let k = (List.length ss) - 1 in
      let ss_tt = List.combine ss tt in 
      unify_set (unify ac) 0 k [[]] ss_tt 
  | F(f,ss),F(g,tt) when f=g && (List.mem f ac) ->
      let f,aa,bs = basic_sol [f] (F(f,ss)) (F(g,tt)) in
      let bs1 = filterPreCond4 bs aa in  
      let bss2 = [ b | b <- powerset bs1; b <> [] ] in
      let bss3 = [ b | b <- bss2; condition3 b aa ] in
      let bss4 = [ b | b  <- bss3; condition4 b aa ] in  
      let fresh () = Signature.fresh_var () in
      let basis_var_ls = [ [ bj, V (fresh ()) | bj <- bsi ] | bsi <- bss4 ] in 
      let subs =
      List.flatten
      [ unify_set (unify ac) 0 ((List.length eqs)-1)  [(make_sigma f basis_var aa)] eqs | basis_var <- 
	basis_var_ls; eqs <- [ make_eqs f basis_var aa ] ] 
      in subs (*
      let subs1 = List.map simplify subs in 
      List.map (remove_vars (Rule.variables (F(f,ss),F(g,tt)))) subs1 *)
  | _ -> []
	

let unify ac (s,t) =
 (*Format.printf "unify %a %a\n%!" Term.print s Term.print t;*)
  let ss = unify ac (s,t) in
 (*Format.printf "%i subs\n%!" (List.length ss);*)
 ss

(* problem: 
let l5 = Tplparser.parse_t "p(p(x,m(x)),y)";;

let t2c = Tplparser.parse_t "p(y(),m(y()),m(w()),z(),w(),x())";;

Ac_subst.unify ["p"] (l5,t2c)

let ls = 
 [[1; 0; 0; 1; 0; 0; 0; 0; 0]; [1; 0; 0; 0; 1; 0; 0; 0; 0];
   [1; 0; 0; 0; 0; 1; 0; 0; 0]; [1; 0; 0; 0; 0; 0; 1; 0; 0];
   [1; 0; 0; 0; 0; 0; 0; 1; 0]; [1; 0; 0; 0; 0; 0; 0; 0; 1];
   [0; 1; 0; 1; 0; 0; 0; 0; 0]; [0; 1; 0; 0; 1; 0; 0; 0; 0];
   [0; 1; 0; 0; 0; 1; 0; 0; 0]; [0; 1; 0; 0; 0; 0; 1; 0; 0];
   [0; 1; 0; 0; 0; 0; 0; 1; 0]; [0; 1; 0; 0; 0; 0; 0; 0; 1];
   [0; 0; 1; 1; 0; 0; 0; 0; 0]; [0; 0; 1; 0; 1; 0; 0; 0; 0];
   [0; 0; 1; 0; 0; 1; 0; 0; 0]; [0; 0; 1; 0; 0; 0; 1; 0; 0];
   [0; 0; 1; 0; 0; 0; 0; 1; 0]; [0; 0; 1; 0; 0; 0; 0; 0; 1]];;
*)

let rec powerset = function
 | [] -> [[]]
 | h::t -> List.fold_left (fun xs t -> (h::t)::t::xs) [] (powerset t);;


(*
  Tests: from Stickel's paper 


assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,x,y,a(),b(),c())", Tplparser.parse_t "f(b(),b(),b(),c(),z)"))) = 4

(*
  Test: from Fortenbacher's paper (he uses a different algorith, so output may vary)
*)
  
assert (List.length (unify ["f"] (Tplparser.parse_t "f(a(),x)", Tplparser.parse_t "f(b(),y)"))) = 2;;

assert (List.length (unify ["p"] (Tplparser.parse_t "p(x,x)", Tplparser.parse_t "p(y,z)"))) = 5;;

assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,x,y,a(),c())", Tplparser.parse_t "f(b(),b(),z,c())"))) = 4;;

assert (List.length (unify ["f";"p"] (Tplparser.parse_t "f(p(x,a()),p(y,a()),c(),c()) ", Tplparser.parse_t "f(p(z,z,z),w)")))=4;;

assert (List.length (unify ["f";"p"] (Tplparser.parse_t "f(x,a(),x,a())", Tplparser.parse_t "f(g(a()),g(y),z,z)"))) = 2;;

assert (List.length (unify ["f";"p"] (Tplparser.parse_t "p(w,p(x,g(x)))", Tplparser.parse_t "p(y,p(z,g(z)))")))=35;;

from paper of Christian and Lincoln

assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,x,a())", Tplparser.parse_t "f(u,u,v,w)")))=12;;

assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,a(),a())", Tplparser.parse_t "f(u,y,v,c())")))=18;;

assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,a(),a())", Tplparser.parse_t "f(u,y,z,v)")))=32;;

assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,y,z)", Tplparser.parse_t "f(u,v,w,t())")))=870;;

assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,y,z)", Tplparser.parse_t "f(u,v,w,t)")))=2161;;

assert (List.length (unify ["f"] (Tplparser.parse_t "f(x,y,a())", Tplparser.parse_t "f(u,v,w,t)")))=416;;
 
 *)

let replace_var_by_consts t = 
 let vars = Term.variables t in
 let name x = "skolem"^(string_of_int x) in
 let sigma = [ v, F(Signature.fun_called (name v),[]) | v <- vars ] in
  sigma, Term.substitute sigma t

let rec replace_consts_by_var sigma = function
  | V x as t -> t
  | F(f,[]) as t ->
      begin
	try
	  let v,_ = List.find (fun (w,u) -> u = t) sigma in V v
	with Not_found -> t
      end
  | F(f,ss) ->  F(f,[ replace_consts_by_var sigma si | si <- ss ])

(*
let sigma, t2c = replace_var_by_consts (Tplparser.parse_t "f(x,y,g(z,x,y),a(),c())");;
Tplparser.parse_t "f(x,y,g(z,x,y),a(),c())" = replace_consts_by_var sigma t2c;;
*)

let matcher ac (t1,t2) = 
 let var_const,t2c = replace_var_by_consts t2 in
 let subs = unify ac (t1,t2c) in
  List.map (fun sub -> [ v, replace_consts_by_var var_const t | v,t <- sub ]) subs

(*
 matcher ["f"] (Tplparser.parse_t "f(a(),x)", Tplparser.parse_t "f(b(),a())");;
 matcher ["f"] (Tplparser.parse_t "f(x,y,z,a(),w)", Tplparser.parse_t "f(x,y,g(z,x,y),a(),c())");;
*)
