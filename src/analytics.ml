(*** OPENS *******************************************************************)
open Format
open Yojson.Basic
open Settings

(*** MODULES *****************************************************************)
module L = List

(*** TYPES *******************************************************************)
type equation_state = Active of int | Passive of int | Unseen

type track_footprint = {
  active: int;
  passive: int;
  unseen: int;
  ratio: float
}

type state = {
  restarts: int;
  iterations: int;
  equalities: int;
  goals: int;
  time: float;
  memory: int;
  reducible: int;
  cps: int;
  trs_size: int;
  cost : int;
  smt_checks: int;
  track : track_footprint option
}

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
let t_subsumption = ref 0.0
let t_cache = ref 0.0
let t_tmp1 = ref 0.0
let t_tmp2 = ref 0.0
let t_tmp3 = ref 0.0
let t_rewrite_goals = ref 0.0

let iterations = ref 0;;
let equalities = ref 0;;
let goals = ref 0;;
let restarts = ref 0
let time_diffs = ref []
let mem_diffs = ref []
let eq_counts = ref []
let goal_counts = ref []
let red_counts = ref []
let cp_counts = ref []
let trs_sizes = ref []
let costs = ref []
let shape = ref NoShape
let smt_checks = ref 0

let acount = ref 0
let pcount = ref 0
let ucount = ref 0

let ac_syms = ref []
let only_c_syms = ref []

let start_time = ref 0.0
let last_time = ref 0.0

let track_equations_state : (Literal.t * equation_state) list ref = ref []

let states : state list ref = ref []

let progress : bool list ref = ref []

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

let runtime _ = Unix.gettimeofday () -. !start_time

let set_time_mem _ =
  if !iterations > 0 then (
    let mem_diff = memory () - (try (List.hd !states).memory with _ -> 0) in
    let time_diff = Unix.gettimeofday () -. !last_time in
    time_diffs := time_diff :: !time_diffs;
    mem_diffs := mem_diff :: !mem_diffs;
    last_time := Unix.gettimeofday ())
;;

let int_count_str l =
  let append s d = s ^ " " ^ (string_of_int d) in
  List.fold_left append "" (List.rev !l)
;;

let bool_str l =
  let append s d = s ^ " " ^ (if d then "1" else "0") in
  List.fold_left append "" (List.rev !l)
;;

let float_count_str l =
  let str f = string_of_float ((floor (100. *.f)) /. 100.) in
  let append s d = s ^ " " ^ (str d) in
  List.fold_left append "" (List.rev !l)
;;

let print () =
  printf "\niterations          %i@." !iterations;
  printf "equalities          %i@." !equalities;
  if !goals > 0 then
    printf "goals               %i@." !goals;
  printf "restarts            %i@." !restarts;
  printf "memory (MB)         %d@." (memory ());
  printf "time diffs         %s@." (float_count_str time_diffs);
  printf "memory diffs       %s@." (int_count_str mem_diffs);
  printf "equation counts    %s@." (int_count_str eq_counts);
  printf "goal counts        %s@." (int_count_str goal_counts);
  printf "reduction counts   %s@." (int_count_str red_counts);
  printf "CP counts          %s@." (int_count_str cp_counts);
  printf "TRS sizes          %s@." (int_count_str trs_sizes);
  printf "costs              %s@." (int_count_str costs);
  printf "oracle counts       %i/%i/%i@." !acount !pcount !ucount;
  printf "progress estimates  %s@." (bool_str progress);
  printf "SMT checks          %i@." !smt_checks;
  printf "problem shape       %s@."(Settings.shape_to_string !shape);
  printf "times@.";
  printf " ground join checks %.3f@." !t_gjoin_check;
  printf " maxk               %.3f@." !t_maxk;
  printf " sat                %.3f@." !t_sat;
  printf " overlaps           %.3f@." !t_overlap;
  printf " process            %.3f@." !t_process;
  printf " subsumption check  %.3f@." !t_subsumption;
  printf " success checks     %.3f@." !t_success_check;
  printf " constraints CPred  %.3f@." !t_ccpred;
  printf "             Comp   %.3f@." !t_ccomp;
  printf "             red    %.3f@." !t_cred;
  printf " rewriting          %.3f@." !t_rewrite;
  printf "   on goals         %.3f@." !t_rewrite_goals;
  printf " encode termination %.3f@." !t_orient_constr;
  printf " selection          %.3f@." !t_select;
  printf " caching            %.3f@." !t_cache;
  printf " tmp1               %.3f@." !t_tmp1;
  printf " tmp2               %.3f@." !t_tmp2;
  printf " tmp3               %.3f@." !t_tmp3;
  printf " normalization      %.3f@." !Variant.t_normalize

let is_applicative es =
  let bs, rest = List.partition (fun (_ ,a) -> a = 2) (Rules.signature es) in
  List.length bs = 1 && List.for_all (fun (_, a) -> a = 0) rest

let duplicating_rule (l,r) =
  Rule.is_rule (l,r) && Rule.is_duplicating (l,r) && not (Term.is_subterm l r)

let is_duplicating es =
  List.exists duplicating_rule (es @ [Rule.flip e | e <- es])

let find_duplicating es =
  List.find duplicating_rule (es @ [Rule.flip e | e <- es])

let problem_shape es =
  let s = !Settings.fixed_shape in
  if s = "boro" then Boro
  else if s = "calcio" then Calcio
  else if s = "carbonio" then Carbonio
  else if s = "elio" then Elio
  else if s = "magnesio" then Magnesio
  else if s = "ossigeno" then Ossigeno
  else if s = "piombo" then Piombo
  else if s = "silicio" then Silicio
  else if s = "xeno" then Xeno
  else if s = "zolfo" then Zolfo
  else (
  let rmax (l, r) = max (Term.size l) (Term.size r) in
  let max_term_size = L.fold_left max 0 [rmax e | e <- es] in
  let rmax (l, r) = max (Term.depth l) (Term.depth r) in
  let max_term_depth = L.fold_left max 0 [rmax e | e <- es] in
  let max_arity = L.fold_left max 0 [ a | _, a <- Rules.signature es ] in
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
  let no_prop = not app && not dup && not distrib && acs + cs = 0 && not mon in
  let large = max_arity > 4 && es_count > 25 && es_size > 200 in
  (* Piombo: heavy terms like in lattices, LAT084-1, LAT392-1, ... *)
  if (max_term_size > 65 && max_term_depth > 10) then Piombo
  (* Ossigeno: GRP166-1, GRP185-3, GRP193-2, GRP184-4 *)
  else if (acs > 0 && dup && distrib && group && lat) then Ossigeno
  (* Xeno: relation problems like REL011-2 *)
  else if (acs > 0 && dup && distrib && mon && not app) then Xeno
  (* Zolfo: some groups like GRP119-1 - GRP122-1 *)
  else if (app && not dup && not distrib && acs = 0) then Zolfo
  (* Carbonio: COL003-* *)
  else if (app && dup && not distrib && acs = 0) then Carbonio
  (* Silicio: lattice problems *)
  else if (not app && not distrib && acs > 1 && lat && not mon) then Silicio
  (* Elio: no structure detected *)
  else if no_prop then if max_arity = 2 then Elio else Magnesio
  (* Boro: commutative symbols, duplication *)
  else if (dup && not app && acs = 0 && cs > 1 && not mon) then Boro
  (* Magnesio: commutative symbols, monoid *)
  else if (not app && acs > 0 && cs > 0 && mon && max_arity = 2) then Magnesio
  (* Calcio: large problems *)
  else if (dup && large) then Calcio
  else if dup && max_arity > 2 then Zolfo else NoShape)
;;

let theory_equations es =
  let theory_relevant l =
    let eq = Literal.terms l in
    Theory.Commutativity.is_axiom eq || Theory.Ac.is_axiom eq ||
    Theory.Monoid.is_axiom eq || Theory.Group.is_axiom eq ||
    Theory.Lattice.is_axiom eq || Theory.Ring.is_distributivity eq
  in
  let ths = List.filter theory_relevant es in
  let esl = [Literal.terms e | e <- es] in
  if not (is_duplicating esl) then ths
  else Literal.make_axiom (find_duplicating esl) :: ths

let analyze es gs =
  let es, ies = List.partition Literal.is_equality es in
  let all = List.map Literal.terms (es @ ies) in
  let fs = Rules.signature all in
  (* some counting *)
  let eqc = "equality count", `Int (L.length es) in
  let ieqc = "inequality count", `Int (L.length ies) in
  let eqs = "equality size", `Int (L.fold_left (+) 0 [Rule.size e | e <-all]) in
  let mar = "max arity", `Int (L.fold_left max 0 [ a | _, a <- fs ]) in
  let rmax (l,r) = max (Term.size l) (Term.size r) in
  let mts = "max term size", `Int (L.fold_left max 0 [rmax e | e <- all]) in
  let rmax (l,r) = max (Term.depth l) (Term.depth r) in
  let mtd = "max term depth", `Int (L.fold_left max 0 [rmax e | e <- all]) in
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
  let assoc =
    [eqc; ieqc; eqs; mar; symcount; mts; mtd; gc; app; dup;
    cs; ac; mon; group; agroup; ring; lattice; distrib; shp]
  in
  `Assoc assoc

let json () =
  let trunc f = `Float ((float_of_int (truncate (f *. 1000.))) /. 1000.) in
  let it = "iterations", `Int !iterations in
  let ea = "equalities", `Int !goals in
  let gs = "goals", `Int !equalities in
  let mem = "memory", `Int (memory ()) in
  let smtc = "SMT checks", `Int !smt_checks in
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
  let t_sub = "time/subsumption checks", trunc !t_subsumption in
  let t_proj = "time/success checks", trunc !t_success_check in
  let t_sat = "time/sat", trunc !t_sat in
  let t_cache = "time/cache", trunc !t_cache in
  let res = "restarts", `Int !restarts in
  let shp = "shape", `String (Settings.shape_to_string !shape) in
  let assoc =
    [it; ea; gs; res; mem; smtc; shp; t_ccpred; t_ccomp; t_cred;
    t_select; t_gjoin; t_maxk; t_rewrite; t_ovl; t_orient; t_proj; t_process;
    t_sat; t_sub; t_cache]
  in
  `Assoc assoc

(* compare current state with respect to other proof *)
let init_proof_track ls =
  track_equations_state := [Literal.normalize l, Unseen | l <- ls]
;;

(* aa are active, pp passive equations *)
let reset_proof_track _ =
  acount := 0;
  pcount := 0;
  ucount := 0;
  track_equations_state := []

let update_proof_track aa pp i =
  let (>) s1 s2 =
    match s1,s2 with
    | _, Unseen -> true
    | Active _, Passive _ -> true
    | _ -> false
  in
  let current l =
    if List.mem l aa then Active i
    else if List.mem l pp then Passive i
    else Unseen
  in
  let update (l,s) = let s' = current l in l, if s' > s then s' else s in
  track_equations_state := List.map update !track_equations_state;
  (* update counts *)
  acount := 0;
  pcount := 0;
  ucount := 0;
  let check = function
    | Unseen -> ucount := !ucount + 1
    | Active i -> acount := !acount + 1
    | Passive i -> pcount := !pcount + 1
  in
  List.iter check (List.map snd !track_equations_state)
;;

let goal_similarity settings n =
  let sim = Term.similarity settings.ac_syms settings.only_c_syms in
  let rsim (s,t) (s',t') = sim s s' +. sim t t' in
  let msim r = List.fold_left (fun m q -> m +. (rsim r q)) 0. settings.gs in
  msim (Literal.terms n)
;;

let show_proof_track settings all_nodes =
  let rec pos l i = function
    | [] -> "none"
    | (n,_) :: _ when n = l -> string_of_int i
    | _ :: ns -> pos l (i + 1) ns
  in
  let pos l = pos l 0 !all_nodes in
  if !(Settings.track_equations) <> [] then (
    let ststr l = function
      | Unseen -> "unseen"
      | Active i -> "active"
      | Passive i -> "passive (" ^ (pos l) ^ ")"
    in
    printf "Proof track:\n";
    let show (l,s) =
      (*let sz, age = Literal.size l, Nodes.age l in*)
      printf "  %s (%s)\n%!" (Literal.to_string l) (ststr l s)
    in
    List.iter show !track_equations_state;
    printf "%i active, " !acount;
    printf "%i passive, " !pcount;
    printf "%i unseen" !ucount;
    let cnt = float_of_int (List.length !track_equations_state) in
    let rat = (float_of_int !acount +. (float_of_int !pcount) *. 0.5) /. cnt in
    printf " (%.3f)\n%!" rat ;
  )
;;

let prefix_equal n xs =
  let all_equal = function
    | x :: xs -> List.fold_left (fun b y -> b && x = y) true xs
    | _ -> false
  in
  try all_equal (Listx.take n xs) with _ -> false
;;

let little_progress i =
  try
    let progress = Listx.take i !progress in
    List.fold_left (fun b y -> b && not y) (!iterations > i) progress
  with _ -> false
;;

let print_state s =
  printf "%i, %i, %i, %i, " s.restarts s.iterations s.equalities s.goals;
  printf "%.2f, %i, %i, " s.time s.memory s.smt_checks;
  printf "%i, %i, %i, %i" s.reducible s.cps s.trs_size s.cost;
  (
    match s.track with
    | Some t -> printf ", %.2f" t.ratio;
    | None -> ()
  );
  printf "\n%!"
;;

let add_progress s' s =
  let dtime = (s.time -. s'.time) *. 100. in
  let deqs = s.equalities - s'.equalities in
  let dgls = s.goals - s'.goals in
  let dcost = s.cost - s'.cost in
  let dcps = s.cps - s'.cps in
  let dsz = s.trs_size - s'.trs_size in
  let dred = s.reducible - s'.reducible in
  let prog1 =
    (dtime < 53.5 && deqs <= 6 && dgls <= 1) ||
    (dtime < 53.5 && deqs > 6 && dcost > 1)
  in
  let prog2 =
    (deqs <= 10 && (
      (dred <= 3 && (dgls <=1 || dred >=0)) ||
      dsz > 3 ||
      deqs <= 6)
    ) ||
    (deqs > 10 && (
      (dgls <= 1 && deqs <= 15) || (dgls <= 1 && deqs = 20 && dcost <= 33) ||
      (dgls <= 1 && deqs > 20 && dsz > 17 && dcps <= 326) ||
      (dgls > 1 && dcost <= 0 && deqs <= 13 && dgls <= 6)||
      (dgls > 1 && dcost > 0 && dgls <= 3 && dcps <= 500))
    )
  in
  progress := (prog1 && prog2) :: !progress
;;

let record_state red_count trs_size cost cp_count =
  let t =
    if !acount + !pcount + !ucount = 0 then None
    else
      let cnt = float_of_int (List.length !track_equations_state) in
      let r = (float_of_int !acount +. (float_of_int !pcount) *. 0.5) /. cnt in
      Some {active = !acount; passive = !pcount; unseen = !ucount; ratio = r}
  in
  let s = {
    restarts = !restarts;
    iterations = !iterations;
    equalities = !equalities;
    goals = !goals;
    time = runtime ();
    memory = memory ();
    reducible = red_count;
    cps = cp_count;
    trs_size = trs_size;
    cost = cost;
    smt_checks = !smt_checks;
    track = t
  }
  in
  (match !states with
  | s' :: _ -> add_progress s' s;
  | _ -> ());
  states := s :: !states;
  if !Settings.benchmark then print_state s
;;

let add_state red_count trs_size cost cp_count =
  red_counts := red_count :: !red_counts;
  trs_sizes := trs_size :: !trs_sizes;
  costs := cost :: !costs;
  cp_counts := cp_count :: !cp_counts;
  record_state red_count trs_size cost cp_count
;;

let restart _ =
  start_time := Unix.gettimeofday ();
  last_time := Unix.gettimeofday ()
;;
