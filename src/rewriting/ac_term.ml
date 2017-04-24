open Term

type t = int list * int list

let rec pos p ac = function
 | V _ as x -> if p x then [[],[]] else []
 | F (f,ts) as t ->
   let ps = [i::p,s | i,ti <- Listx.index ts; p,s <- pos p ac ti] in
   let is = Listx.interval 0 (List.length ts) in
   if not (List.mem f ac) then
    if p t then ([],is)::ps else ps
   else
    let ss = [s | s <- Listx.power is; List.length s > 2] in
    if p t then [[],s | s <- ss] @ ps else ps
;;

let funs_pos = pos (fun t -> not (Term.is_variable t))

let rec subterm_at u (p,s) =
  match u, p with
  | V _, [] -> u
  | F (f, ss), [] ->
   F (f, [ si | i,si <- Listx.index ss; List.mem i s])
  | F (f, ss), i :: q -> subterm_at (List.nth ss i) (q,s)
  | _ -> invalid_arg "Ac_term.subterm_at"

let rec replace u t (p,s) =
  match u, p, s with
  | _, [], [] -> t
  | F (f, ss), [], _ ->
   let ss' = [ si | i,si <- Listx.index ss; not (List.mem i s)] in
   if ss' = [] then t else F (f, t::ss') 
  | F (f, ss), i :: q, _ ->
      F (f, [ if i = j then replace sj t (q,s) else sj | j, sj <- Listx.ix ss ])
  | _ -> invalid_arg "Ac_term.replace" 
