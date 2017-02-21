(*** OPENS *******************************************************************)
open Term

(*** MODULES ******************************************************************)
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

  let count es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    let fs = List.filter (is_for es) [ f,id | f <- bs; id <- cs ] in
    List.length fs

  let is_contained es = count es > 0

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

  let count es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let us = [ f | f,a <- fs; a = 1 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    let fs = List.filter (is_for es) [ f,i,id | f <- bs; i <- us; id <- cs ] in
    List.length fs

  let is_contained es = count es > 0
end

module AbelianGroup = struct
  (*** FUNCTIONS **************************************************************)
  let is_for es (f,i,id) = Group.is_for es (f,i,id) && Ac.is_for es f

  let count es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let us = [ f | f,a <- fs; a = 1 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    let fs = List.filter (is_for es) [ f,i,id | f <- bs; i <- us; id <- cs ] in
    List.length fs

  let is_contained es = count es > 0
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

  let count es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let us = [ f | f,a <- fs; a = 1 ] in
    let cs = [ f | f,a <- fs; a = 0 ] in
    let syms = [ m,a,i,z | m <- bs; a <- bs; i <- us; z <- cs] in
    let fs = List.filter (is_for es) syms in
    List.length fs
  ;;

  let is_contained es = count es > 0
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


  let count es =
    let fs = Rules.signature es in
    let bs = [ f | f,a <- fs; a = 2 ] in
    let fs = List.filter (is_for es) [ j,m | j <- bs; m <- bs ] in
    List.length fs / 2 (* account for symmetry *)

  let is_contained es = count es > 0
end