(*** MODULES *****************************************************************)
module L = List
module T = Term
module R = Rule

(*** GLOBALS *****************************************************************)
let settings = Settings.default

(*** FUNCTIONS ***************************************************************)
let debug _ = !(settings.d) >= 1

let pstr = function
[] -> "e"
| p -> L.fold_left (fun s i -> s ^ (string_of_int i)) "" p
;;

let narrow_forward_at_with ((s,t),(ps,pt)) p (l,r) =
let s_p = T.subterm_at p s in
try
let subst = T.substitute (Subst.mgu s_p l) in
if debug () then
  Format.printf "forward narrow %a with %a at %s\n%!" T.print s
    R.print (l,r) (pstr p);
let s' = T.replace (subst s) (subst r) p in
let ps' = L.filter (fun q -> not (Listx.is_prefix p q)) ps in 
let ps' = ps' @ [ p @ q | q <- T.function_positions r ] in
[((s',subst t),(Listx.unique ps',pt))]
with _ -> []
;;

let narrow_backward_at_with ((s,t),(ps,pt)) p (l,r) =
let s_p = T.subterm_at p s in
try
if debug () then
Format.printf "backward narrow %a with %a at %s?\n%!" T.print s
  R.print (l,r) (pstr p);
let subst = T.substitute (Subst.mgu s_p r) in
if debug () then
  Format.printf "backward narrow %a with %a at %s\n%!" T.print s
    R.print (l,r) (pstr p);
let s' = T.replace (subst s) (subst l) p in
let ps' = L.filter (fun q -> not (Listx.is_prefix p q)) ps in 
let ps' = ps' @ [ p @ q | q <- T.function_positions l ] in
[((s',subst t),(Listx.unique ps',pt))]
with _ -> []
;;

let narrow_at rr st p =
  L.concat (L.map (fun rl -> narrow_forward_at_with st p (R.rename rl)) rr)
;;

let merge ((s,t),(ps,pt)) ((s',t'),(ps',pt')) =
  if R.variant (s,t) (s',t') then
    (s,t),(Listx.unique (ps@ps'), Listx.unique (pt@pt'))
  else if R.variant (t,s) (s',t') then
    (s',t'),(Listx.unique (pt@ps'), Listx.unique (ps@pt'))
  else ((s',t'),(ps',pt'))
;;

let sym_variant ((s,t),_) (st',_) = R.variant (t,s) st' || R.variant (s,t) st'

let rec add st = function
    [] -> [st]
  | st' :: gs when sym_variant st st' -> (merge st st') :: gs  
  | st' :: gs -> st' :: (add st gs)
;;

let unique = L.fold_left (fun all g -> add g all) []

let narrow rr ((s,t),(ps,pt)) =
  L.concat ((L.map (narrow_at rr ((s,t),(ps,pt))) ps) @
  (L.map (narrow_at rr ((t,s),(pt,ps))) pt))
;;

let decide rr ee ord (s,t) =
  let bot = match ord#bot with Some b -> b | _ -> 100 in
  let patch (l,r) = 
    let vs = Listset.diff (T.variables r) (T.variables l) in
    R.substitute [ v, T.F (bot,[]) | v <- vs ] (l,r)
  in 
  let ee' = L.map patch ee in  
  let rr' = rr @ ee' in

  let rec decide_by_narrowing all gs =
  if debug () then (
    Format.printf "start decide_by_narrowing iteration\n%!";
    let psstr ps =
      "{" ^ (L.fold_left (fun s p -> s ^ ", " ^ (pstr p)) "" ps) ^ "}"
    in
    L.iter (fun ((s,t),(ps,pt)) ->
      Format.printf "  (%a,%a) (%s,%s)\n%!" T.print s T.print t
        (psstr ps) (psstr pt)) gs;
    Format.printf "all:\n";
    L.iter (fun ((s,t),(ps,pt)) ->
      Format.printf "  (%a,%a) (%s,%s)\n%!" T.print s T.print t
        (psstr ps) (psstr pt)) all);
  let unifiable ((s,t),_) = Subst.unifiable s t in
  if L.exists unifiable gs then (
    if debug () then
      Format.printf "UNSAT, found unifiable equation\n%!";
    Some (Settings.Proof (fst (L.find unifiable gs),([],[]),[])))
  else if L.for_all (fun (_,(ps,pt)) -> ps @ pt = []) gs then (
    Some (Settings.GroundCompletion (rr,ee,ord)))
  else
    let remove_gs ((st,(ps,pt)) as np) =
      try
        let _,(ps',pt') = L.find (fun (st',_) -> R.variant st' st) all in
        (st,(Listset.diff ps ps', Listset.diff pt pt'))
      with Not_found -> np
    in
    let gs' = unique (L.concat (L.map (narrow rr') gs)) in
    let gs' = L.map remove_gs gs' in
    let all' = unique (all @ gs') in
    decide_by_narrowing all' (Listx.unique gs')
  in
  let ps_pt = T.function_positions s,T.function_positions t in
  decide_by_narrowing [(s,t),ps_pt] [(s,t),ps_pt]
;;
