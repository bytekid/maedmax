(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Leftist heaps.
   See for instance Chris Okasaki's "Purely Functional Data Structures".
   Modified to hold no duplicates of elements, to store the size, and
   support element removal as well as some higher order functions.
*)

module type Ordered = sig
  type t
  val le: t -> t -> bool
end

exception Empty

module Make(X : Ordered) :
sig
  type t
  val empty : t
  val is_empty : t -> bool
  val size : t -> int
  val min: t -> X.t
  val extract_min: t -> X.t * t
  val mem: X.t -> t -> bool
  val insert: X.t -> t -> t
  val merge: t -> t -> t
  val delete: X.t -> t -> t
  val diff: t -> t -> t
  val iter: (X.t -> unit) -> t -> unit
  val fold: ('a -> X.t -> 'a) -> 'a -> t -> 'a
  val filter: (X.t -> bool) -> t -> t
  val exists: (X.t -> bool) -> (X.t -> bool) -> t -> bool
  val to_list: t -> X.t list
end
=
struct

  type t = E | T of int * X.t * t * t * int

  let rank = function E -> 0 | T (r,_,_,_,_) -> r

  let size = function E -> 0 | T (_,_,_,_,s) -> s

  let make x a b =
    let ra = rank a and rb = rank b in
    let s = size a + (size b) + 1 in
    if ra >= rb then T (rb + 1, x, a, b, s)
    else T (ra + 1, x, b, a, s)

  let empty = E

  let is_empty = function E -> true | T _ -> false

  let rec mem y = function
    | E -> false
    | T (_,x,_,_,_) when x = y -> true
    | T (_,x,_,_,_) when not (X.le x y) -> false
    | T (_,_,a,b,_) -> mem y a || mem y b

  let rec merge h1 h2 = match h1,h2 with
    | E, h | h, E -> h
    | T (_,x,a1,b1,_), t when mem x t -> merge (merge a1 b1) t
    | T (_,x,a1,b1,_), T (_,y,a2,b2,_) ->
        if x=y then make x (merge a1 a2) (merge b1 b2)
        else if X.le x y then make x a1 (merge b1 h2)
        else make y a2 (merge h1 b2)

  let insert x h = merge (T (1, x, E, E, 1)) h

  let min = function E -> raise Empty | T (_,x,_,_,_) -> x

  let extract_min = function
    | E -> raise Empty
    | T (_,x,a,b,_) -> x, merge a b

  let rec delete y = function
    | E -> E
    | T (_,x,a,b,_) when x = y -> merge a b
    | T (_,x,_,_,_) as t when not (X.le x y) -> t
    | T (_,x,a,b,_) -> make x (delete y a) (delete y b)

  let rec exists p c = function
    | E -> false
    | T (_,x,_,_,_) when p x -> true
    | T (_,x,_,_,_) when c x -> false
    | T (_,_,a,b,_) -> exists p c a || exists p c b

  let rec filter f = function
    | E -> E
    | T (_,x,a,b,_) when not (f x) -> merge (filter f a) (filter f b)
    | T (_,x,a,b,_) -> make x (filter f a) (filter f b)

  let rec to_list = function
    | E -> []
    | T (_,x,a,b,_) -> (to_list a) @ (x :: (to_list b))

  let rec fold f c = function
    | E -> c
    | T (_,x,a,b,_) -> fold f (f (fold f c a) x) b

  let diff h1 h2 = fold (fun h x -> delete x h) h1 h2

  let to_list = fold (fun l x -> x :: l) []

  let iter f = fold (fun _ x -> f x) ()
end