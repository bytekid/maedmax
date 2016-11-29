open Format
open Yojson.Basic

let t_ccomp = ref 0.0
let t_ccpred = ref 0.0
let t_cred = ref 0.0
let t_maxk = ref 0.0
let t_orient_constr = ref 0.0
let t_overlap = ref 0.0
let t_rewrite = ref 0.0
let t_sat = ref 0.0
let t_success_check = ref 0.0
let t_select = ref 0.0
let t_cache = ref 0.0
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
 printf "\niterations          %i@." !iterations;
 printf "equalities          %i@." !ces;
 printf "restarts            %i@." !restarts;
 printf "times@.";
 printf " maxk               %.3f@." !t_maxk;
 printf " sat                %.3f@." !t_sat;
 printf " overlaps           %.3f@." !t_overlap;
 printf " success checks     %.3f@." !t_success_check;
 printf " constraints CPred  %.3f@." !t_ccpred;
 printf "             Comp   %.3f@." !t_ccomp;
 printf "             red    %.3f@." !t_cred;
 printf " rewriting          %.3f@." !t_rewrite;
 printf " encode termination %.3f@." !t_orient_constr;
 printf " selection          %.3f@." !t_select;
 printf " caching            %.3f@." !t_cache;
 printf " tmp1               %.3f@." !t_tmp1;
 printf " tmp2               %.3f@." !t_tmp2
;;

let json s k n =
 let trunc f = `Float ((float_of_int (truncate (f *. 1000.))) /. 1000.) in
 let s = "strategy", `String s in
 let k = "k", `String (if k  < 0 then "if i < 3 then 6 else 2" else string_of_int k) in
 let n = "n", `Int n in
 let it = "iterations", `Int !iterations in
 let ea = "equalities", `Int !ces in
 let t_ccpred = "time/ccpred", trunc !t_ccpred in
 let t_ccomp = "time/ccomp", trunc !t_ccomp in
 let t_cred = "time/cred", trunc !t_cred in
 let t_maxk = "time/maxk", trunc !t_maxk in
 let t_rewrite = "time/rewrite", trunc !t_rewrite in
 let t_select = "time/select", trunc !t_select in
 let t_ovl = "time/overlaps", trunc !t_overlap in
 let t_orient = "time/orientation constraints", trunc !t_orient_constr in
 let t_proj = "time/success checks", trunc !t_success_check in
 let t_sat = "time/sat", trunc !t_sat in
 let t_cache = "time/cache", trunc !t_cache in
 let res = "restarts", `Int !restarts in
 let t = `Assoc [s; k; n; it; ea; res; t_ccpred; t_ccomp; t_cred; t_select;
  t_maxk; t_rewrite; t_ovl; t_orient; t_proj; t_sat; t_cache] in
 t
;;

