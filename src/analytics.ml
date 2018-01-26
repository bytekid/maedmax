(*** OPENS *******************************************************************)
open Format
open Yojson.Basic
open Settings

(*** MODULES *****************************************************************)
module L = List

(*** GLOBALS *****************************************************************)
let t_ccomp = ref 0.0
let t_ccpred = ref 0.0
let t_cred = ref 0.0
let t_gjoin_check = ref 0.0
let t_maxk = ref 0.0
let t_orient_constr = ref 0.0
let t_overlap = ref 0.0
let t_process = ref 0.0
let t_rewrite = ref 0.0
let t_sat = ref 0.0
let t_success_check = ref 0.0
let t_select = ref 0.0
let t_cache = ref 0.0
let t_tmp1 = ref 0.0
let t_tmp2 = ref 0.0

let iterations = ref 0;;
let ces = ref 0;;
let goals = ref 0;;
let restarts = ref 0
let time_diffs = ref []
let mem_diffs = ref []
let eq_counts = ref []
let shape = ref NoShape

(*** FUNCTIONS ***************************************************************)
let take_time t f x =
 let s = Unix.gettimeofday () in
 let res = f x in
 t := !t +. (Unix.gettimeofday () -. s);
 res

let memory _ =
  let s = Gc.quick_stat () in
  s.Gc.heap_words * (Sys.word_size / 8 ) / (1024 * 1024)
;;

let eq_count_str _ =
 List.fold_left (fun s d -> s^" "^(string_of_int d)) "" (List.rev !eq_counts)
;;

let memory_diff_str _ =
 List.fold_left (fun s d -> s^" "^(string_of_int d)) "" (List.rev !mem_diffs)
;;

let time_diff_str _ =
 let str s d = s ^ " " ^ (string_of_int (int_of_float (d *. 100.))) in
 List.fold_left str "" (List.rev !time_diffs)
;;

let print () =
  printf "\niterations          %i@." !iterations;
  printf "equalities          %i@." !ces;
  if !goals > 0 then
    printf "goals               %i@." !goals;
  printf "restarts            %i@." !restarts;
  printf "memory (MB)         %d@." (memory ());
  printf "time diffs         %s@." (time_diff_str ());
  printf "memory diffs       %s@." (memory_diff_str ());
  printf "equation counts    %s@." (eq_count_str ());
  printf "problem shape      %s@."(Settings.shape_to_string !shape);
  printf "times@.";
  printf " ground join checks %.3f@." !t_gjoin_check;
  printf " maxk               %.3f@." !t_maxk;
  printf " sat                %.3f@." !t_sat;
  printf " overlaps           %.3f@." !t_overlap;
  printf " process            %.3f@." !t_process;
  printf " success checks     %.3f@." !t_success_check;
  printf " constraints CPred  %.3f@." !t_ccpred;
  printf "             Comp   %.3f@." !t_ccomp;
  printf "             red    %.3f@." !t_cred;
  printf " rewriting          %.3f@." !t_rewrite;
  printf " encode termination %.3f@." !t_orient_constr;
  printf " selection          %.3f@." !t_select;
  printf " caching            %.3f@." !t_cache;
  printf " tmp1               %.3f@." !t_tmp1;
  printf " tmp2               %.3f@." !t_tmp2;
  printf " normalization      %.3f@." !Variant.t_normalize
;;

let is_applicative es =
 let bs, rest = List.partition (fun (_,a) -> a = 2) (Rules.signature es) in
 List.length bs = 1 && List.for_all (fun (_,a) -> a = 0) rest
;;

let really_duplicating_rule (l,r) = Rule.is_duplicating (l,r)

let duplicating_rule (l,r) =
  Rule.is_rule (l,r) && Rule.is_duplicating (l,r) && not (Term.is_subterm l r)

let is_duplicating es =
  List.exists duplicating_rule (es @ [Rule.flip e | e <- es ])
;;

let find_duplicating es =
  List.find duplicating_rule (es @ [Rule.flip e | e <- es ])
;;

let problem_shape es =
  let rmax (l,r) = Pervasives.max (Term.size l) (Term.size r) in
  let max_term_size = L.fold_left Pervasives.max 0 [ rmax e | e <- es] in
  let rmax (l,r) = Pervasives.max (Term.depth l) (Term.depth r) in
  let max_term_depth = L.fold_left Pervasives.max 0 [ rmax e | e <- es] in
  let max_term_arity = L.fold_left max 0 [ a | _,a <- Rules.signature es ] in
  let es_size = L.fold_left (+) 0 [Rule.size e | e <- es] in 
  let es_count = List.length es in
  let app = is_applicative es in
  let dup = is_duplicating es in
  let mon = Theory.Monoid.count es > 0 in
  let group = Theory.Group.count es > 0 in
  let lat = Theory.Lattice.count es > 0 in
  let acs = Theory.Ac.count es in
  let cs = Theory.Commutativity.count es - acs in
  let distrib = Theory.Ring.has_distrib es in
  if (max_term_size > 65 && max_term_depth > 10) then
    Piombo (* large terms like in lattices, LAT084-1, LAT392-1, ... *)
  else if (acs > 0 && dup && distrib && group && lat) then
    Ossigeno (* GRP166-1, GRP185-3, GRP193-2, GRP184-4 *)
  else if (acs > 0 && dup && distrib && mon && not app) then
    Xeno (* relation problems like REL011-2 *)
  else if (app && not dup && not distrib && acs = 0) then
    Zolfo (* some groups like GRP119-1 - GRP122-1 *)
  else if (app && dup && not distrib && acs = 0) then
    Carbonio (* COL003-* *)
  else if (not app && not distrib && acs > 1 && lat && not mon) then
    Silicio (* lattice *)
  else if (not app && not dup && not distrib && acs = 0 && cs=0 && not mon) then
    Elio (* no structure detected *)
  else if (dup && not app && acs = 0 && cs > 1 && not mon) then
    Boro (* commutative symbols, duplication *)
  else if (dup && max_term_arity > 4 && es_count > 25 && es_size > 200) then
    Calcio (* large problems *)
  else
    NoShape
;;

let theory_equations es =
  let theory_relevant l =
    let eq = Literal.terms l in
    Theory.Commutativity.is_axiom eq || Theory.Ac.is_axiom eq ||
    Theory.Monoid.is_axiom eq || Theory.Group.is_axiom eq ||
    Theory.Lattice.is_axiom eq || Theory.Ring.is_distributivity eq
  in
  let ths = List.filter theory_relevant es in
  let esl = [ Literal.terms e | e <- es] in
  if not (is_duplicating esl) then ths
  else Literal.make_axiom (find_duplicating esl) :: ths
;;

let analyze es gs =
  let es, ies = List.partition Literal.is_equality es in
  let all = List.map Literal.terms (es @ ies) in
  let fs = Rules.signature all in
  (* some counting *)
  let eqc = "equality count", `Int (L.length es) in
  let ieqc = "inequality count", `Int (L.length ies) in
  let eqs = "equality size", `Int (L.fold_left (+) 0 [Rule.size e | e <-all]) in
  let mar = "max arity", `Int (L.fold_left max 0 [ a | _,a <- fs ]) in
  let rmax (l,r) = max (Term.size l) (Term.size r) in
  let mts = "max term size", `Int (L.fold_left max 0 [ rmax e | e <-all]) in
  let rmax (l,r) = max (Term.depth l) (Term.depth r) in
  let mtd = "max term depth", `Int (L.fold_left max 0 [ rmax e | e <-all]) in
  let symcount = "symbol count", `Int (L.length fs) in
  let gc = "goal count", `Int (L.length gs) in
  let app = "is applicative", `Bool (is_applicative all) in
  let es = List.map Literal.terms es in
  let dup = "is duplicating", `Bool (is_duplicating es) in
  (* some theory characteristics *)
  let cs = "commutative syms", `Int (Theory.Commutativity.count es) in
  let ac = "acs", `Int (Theory.Ac.count es) in
  let mon = "monoids", `Int (Theory.Monoid.count es) in
  let group = "groups", `Int (Theory.Group.count es) in
  let agroup = "abelian groups", `Int (Theory.AbelianGroup.count es) in
  let ring = "ring", `Int (Theory.Ring.count es) in
  let distrib = "has distribution", `Bool (Theory.Ring.has_distrib es) in
  let lattice = "lattice", `Int (Theory.Lattice.count es) in
  let shp = "shape", `String (Settings.shape_to_string (problem_shape es)) in
  `Assoc [eqc; ieqc; eqs; mar; symcount; mts; mtd; gc; app; dup;
          cs; ac; mon; group; agroup; ring; lattice; distrib; shp ]
;;

let json () =
 let trunc f = `Float ((float_of_int (truncate (f *. 1000.))) /. 1000.) in
 let it = "iterations", `Int !iterations in
 let ea = "equalities", `Int !ces in
 let mem = "memory", `Int (memory ()) in
 let t_ccpred = "time/ccpred", trunc !t_ccpred in
 let t_ccomp = "time/ccomp", trunc !t_ccomp in
 let t_cred = "time/cred", trunc !t_cred in
 let t_gjoin = "time/ground join checks", trunc !t_gjoin_check in
 let t_maxk = "time/maxk", trunc !t_maxk in
 let t_process = "time/process", trunc !t_process in
 let t_rewrite = "time/rewrite", trunc !t_rewrite in
 let t_select = "time/select", trunc !t_select in
 let t_ovl = "time/overlaps", trunc !t_overlap in
 let t_orient = "time/orientation constraints", trunc !t_orient_constr in
 let t_proj = "time/success checks", trunc !t_success_check in
 let t_sat = "time/sat", trunc !t_sat in
 let t_cache = "time/cache", trunc !t_cache in
 let res = "restarts", `Int !restarts in
 let shp = "shape", `String (Settings.shape_to_string !shape) in
 let t = `Assoc [it; ea; res; mem; shp; t_ccpred; t_ccomp; t_cred; t_select;
  t_gjoin; t_maxk; t_rewrite; t_ovl; t_orient; t_proj; t_process; t_sat;
  t_cache]
 in t
;;
