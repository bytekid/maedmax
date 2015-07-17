open Format
open Yojson.Basic

let t_cache = ref 0.0
let t_gc = ref 0.0
let t_insert = ref 0.0
let t_maxk = ref 0.0
let t_norm = ref 0.0
let t_orient_constr = ref 0.0
let t_overlap = ref 0.0
let t_project = ref 0.0
let t_sat = ref 0.0
let t_translate = ref 0.0
let t_upd = ref 0.0
let t_tmp1 = ref 0.0
let t_tmp2 = ref 0.0

let iterations = ref 0;;
let ces = ref 0;;
let restarts = ref 0

let take_time t f x =
 let s = Unix.gettimeofday () in
 let res = f x in
 t := !t +. (Unix.gettimeofday () -. s);
 res

let print () =
 printf "\nequalities         %i@." !ces;
 printf "overlaps2 time       %.3f@." !t_cache;
 printf "gc time            %.3f@." !t_gc;
 printf "insert time        %.3f@." !t_insert;
 printf "iterations         %i@." !iterations;
 printf "maxk time          %.3f@." !t_maxk;
 printf "normalization time %.3f@." !t_norm;
 printf "orientation time   %.3f@." !t_orient_constr;
 printf "overlap time       %.3f@." !t_overlap;
 printf "join check time    %.3f@." !t_project;
 printf "sat time           %.3f@." !t_sat;
 printf "translate time     %.3f@." !t_translate;
 printf "update context     %.3f@." !t_upd;
 printf "tmp1               %.3f@." !t_tmp1;
 printf "tmp2               %.3f@." !t_tmp2;
 printf "restarts           %i@."   !restarts
;;

let json s k n =
 let trunc f = `Float ((float_of_int (truncate (f *. 1000.))) /. 1000.) in
 let s = "strategy", `String s in
 let k = "k", `String (if k  < 0 then "if i < 3 then 6 else 2" else string_of_int k) in
 let n = "n", `Int n in
 let it = "iterations", `Int !iterations in
 let ea = "equalities", `Int !ces in
 let t_cache = "time/cache", trunc !t_cache in
 let t_ins = "time/set ops", trunc !t_insert in
 let t_maxk = "time/maxk", trunc !t_maxk in
 let t_norm = "time/normalization", trunc !t_norm in
 let t_ovl = "time/overlaps", trunc !t_overlap in
 let t_orient = "time/orientation constraints", trunc !t_orient_constr in
 let t_proj = "time/project", trunc !t_project in
 let t_sat = "time/sat", trunc !t_sat in
 let t_context = "time/update context", trunc !t_upd in
 let res = "restarts", `Int !restarts in
 let t = `Assoc [s; k; n; it; ea; res; t_cache; t_ins; t_maxk; t_norm; 
  t_ovl; t_orient; t_proj; t_sat; t_context] in
 t
;;

