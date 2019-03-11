(*** OPENS *******************************************************************)
open Term

(*** MODULES ******************************************************************)
module Commutativity = struct
  (*** FUNCTIONS **************************************************************)
  let x = V (-1)
  let y = V (-2)

  let commutativity f = (F(f, [x; y]), F(f, [y; x]))

  let symbols es =
    let is_c f (l,r) = Variant.eq_variant (l,r) (commutativity f)  in
    let binary_root = function F(_, [_;_]) -> true | _ -> false in
    let fs = [ root l | l,_ <- es@[ r,l | l,r <- es ]; binary_root l ] in
    let f = [f | f <- fs; List.exists (is_c f) es] in
    Listx.unique f

  let is_for es f = List.mem f (symbols es)

  let eqs fs = [ commutativity f | f <- fs ]

  let count es = List.length (symbols es)

  let equivalent cs (s, t) = Term.args_sort cs s = Term.args_sort cs t

  let is_axiom = function
      F(f, [V x; V y]), F(f', [V y'; V x']) -> f=f' && x=x' && y=y' && x <> y
    | _ -> false
  ;;

end

module Ac = struct
  (*** FUNCTIONS **************************************************************)
  let x = V (-1)
  let y = V (-2)
  let z = V (-3)

  let associativity f =
    let lhs = F(f, [F(f, [x; y]); z]) in
    let rhs = F(f, [x; F(f, [y; z])]) in
    (lhs, rhs)
  ;;

  let commutativity f = (F(f, [x; y]), F(f, [y; x]))

  let cassociativity f =
    let lhs = F(f, [x; F(f, [y; z])]) in
    let rhs = F(f, [y; F(f, [x; z])]) in
    (lhs, rhs)
  ;;

  let symbols es =
    let is_a f (l,r) = Variant.eq_variant (l,r) (associativity f) in
    let is_c f (l,r) = Variant.eq_variant (l,r) (commutativity f)  in
    let binary_root = function F(_, [_;_]) -> true | _ -> false in
    let fs = [ root l | l,_ <- es@[ r,l | l,r <- es ]; binary_root l ] in
    let f = [f | f <- fs; List.exists (is_a f) es && List.exists (is_c f) es] in
    Listx.unique f

  let is_for es f = List.mem f (symbols es)

  let eqs fs =
    let cs = [ commutativity f | f <- fs ] in
    let ass = [ associativity f | f <- fs ] in
    let cas = [ cassociativity f | f <- fs ] in
    cs @ ass @ cas

  let add es acs =
    let cs = [ Variant.normalize_rule (commutativity f) | f <- acs ] in
    let cs' = [ Variant.normalize_rule (cassociativity f) | f <- acs ] in
    Listx.unique (cs @ cs' @ es)

  let count es = List.length (symbols es)

  let equivalent acs (s, t) = Term.flatten acs s = Term.flatten acs t

  let is_assoc_axiom = function
      F(f0, [F(f1, [V x; V y]); V z]), F(f2, [V x'; F(f3, [V y'; V z'])]) ->
      f0=f1 && f1=f2 && f2=f3 &&
      x=x' && y=y' && z=z' && x<>y && x<>z && y<>z
    | _ -> false
  ;;

  let is_axiom st = Commutativity.is_axiom st || is_assoc_axiom st

  let axioms acs = [associativity acs; commutativity acs]
end

module Monoid = struct
  (*** FUNCTIONS **************************************************************)
  let x = V (-1)
  let y = V (-2)
  let z = V (-3)

  let associativity f = F(f, [F(f, [x; y]); z]), F(f, [x; F(f, [y; z])])

  let left_ident f id = F(f, [F(id, []); x]), x

  let right_ident f id = F(f, [x; F(id, [])]), x

  let is_right_for es (f, id) =
    let var = Variant.eq_variant in
    let ex = List.exists in
    ex (var (associativity f)) es && ex (var (right_ident f id)) es

  let is_left_for es (f, id) =
    let var = Variant.eq_variant in
    let ex = List.exists in
    ex (var (associativity f)) es && ex (var (left_ident f id)) es

  let is_for es (f, id) = is_right_for es (f, id) || is_left_for es (f, id)

  let symbols es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    List.filter (is_for es) [ f,id | f <- bs; id <- cs ]

  let count es = List.length (symbols es)

  let is_contained es = count es > 0

  let is_left_ident_axiom = function
      F(f,[F(n,[]);V x]), V x' -> x=x'
    | _ -> false
  ;;

  let is_right_ident_axiom = function
      F(f,[V x;F(n,[])]), V x' -> x=x'
    | _ -> false
  ;;

  let is_axiom st =
    Ac.is_assoc_axiom st || is_left_ident_axiom st || is_right_ident_axiom st

end

module Group = struct
  (*** FUNCTIONS **************************************************************)
  let x = V (-1)

  let left_inv f i id = F(f, [F(i, [x]); x]), F(id, [])

  let right_inv f i id = F(f, [x; F(i, [x])]), F(id, [])

  let is_right_for es (f, i, id) =
    let var = Variant.eq_variant in
    Monoid.is_right_for es (f,id) && List.exists (var (right_inv f i id)) es

  let is_left_for es (f, i, id) =
    let var = Variant.eq_variant in
    Monoid.is_left_for es (f,id) && List.exists (var (left_inv f i id)) es

  let is_for es fs = is_right_for es fs || is_left_for es fs

  let symbols es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let us = [ f | f,a <- fs; a = 1 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    List.filter (is_for es) [ f,i,id | f <- bs; i <- us; id <- cs ]

  let count es = List.length (symbols es)

  let is_contained es = count es > 0

  let is_left_inv_axiom = function
      F(f, [F(i, [V x']); V x]), F(n, []) -> x=x'
    | _ -> false
  ;;

  let is_right_inv_axiom = function
      F(f, [V x; F(i, [V x'])]), F(n, []) -> x=x'
    | _ -> false
  ;;

  let is_axiom st =
    Monoid.is_axiom st || is_left_inv_axiom st || is_right_inv_axiom st
end

module AbelianGroup = struct
  (*** FUNCTIONS **************************************************************)
  let is_for es (f,i,id) = Group.is_for es (f,i,id) && Ac.is_for es f

  let symbols es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let us = [ f | f,a <- fs; a = 1 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    List.filter (is_for es) [ f,i,id | f <- bs; i <- us; id <- cs ]

  let count es = List.length (symbols es)

  let is_axiom st =
    Group.is_axiom st || Commutativity.is_axiom st

end

module Ring = struct
  (*** FUNCTIONS **************************************************************)
  let x = V (-1)
  let y = V (-2)
  let z = V (-3)

  let associativity f = F(f, [F(f, [x; y]); z]), F(f, [x; F(f, [y; z])])

  let left_distrib m a =
    F(m, [x; F(a, [y; z]);]), F(a, [F(m, [x; y]); F(m, [x; z])])

  let right_distrib m a =
    F(m, [F(a, [y; z]); x]), F(a, [F(m, [y; x]); F(m, [z; x])])

  let has_distrib es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let has_d (m,a) = 
      let var = Variant.eq_variant in
      let ex = List.exists in
      ex (var (right_distrib m a)) es || ex (var (left_distrib m a)) es
    in List.exists has_d [ m,a | m <- bs; a <- bs ]
  ;;

  let is_for es (m,a,i,z) =
    let var = Variant.eq_variant in
    let ex = List.exists in
    ex (var (right_distrib m a)) es && ex (var (left_distrib m a)) es &&
    AbelianGroup.is_for es (a,i,z) && ex (var (associativity m)) es
  ;;

  let symbols es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let us = [ f | f,a <- fs; a = 1 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    let syms = [ m,a,i,z | m <- bs; a <- bs; i <- us; z <- cs] in
    List.filter (is_for es) syms
  ;;

  let count es = List.length (symbols es)

  let is_contained es = count es > 0

  let is_left_distributivity = function
    F(m,[V x;F(a,[V y;V z])]), F(a',[F(m',[V x';V y']); F(m'',[V x'';V z'])]) ->
      m=m' && m'=m'' && a=a' && m<>a &&
      x=x' && x=x'' && y=y' && z=z' && x<>y && x<>z && y<>z
    | _ -> false

  let is_right_distributivity = function
    F(m,[F(a,[V y;V z]);V x]), F(a',[F(m',[V y';V x']); F(m'',[V z';V x''])]) ->
      m=m' && m'=m'' && a=a' && m<>a &&
      x=x' && x=x'' && y=y' && z=z' && x<>y && x<>z && y<>z
    | _ -> false

  let is_distributivity st =
    is_left_distributivity st || is_right_distributivity st
end

module Lattice = struct
  (*** FUNCTIONS **************************************************************)
  let x = V (-1)
  let y = V (-2)

  let absorb f g = F(f, [x; F(g, [x ; y])]), x

  let is_for es (f,g) =
    let var = Variant.eq_variant in
    let ex = List.exists in
    ex (var (absorb f g)) es && ex (var (absorb g f)) es &&
    Ac.is_for es f && Ac.is_for es g
  ;;

  let symbols es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    List.filter (is_for es) [ j,m | j <- bs; m <- bs ]

  let count es = List.length (symbols es) / 2 (* account for symmetry *)

  let is_contained es = count es > 0

  let is_absorb = function
      F(f, [V x1; F(g, [V x2 ; V y])]), V x3 -> x1=x2 && x2=x3 && x1<>y
    | _ -> false 

  let is_axiom st = Ac.is_axiom st || is_absorb st
end