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

(* Leftist heaps *)

module type Ordered = sig
  type t
  val le: t -> t -> bool
end

exception Empty

module Make(X: Ordered) :
sig
  type t

  val empty: t

  val is_empty: t -> bool
    (* runs in O(1) *)

  val size : t -> int
    (* runs in O(1) *)

  val min: t -> X.t
    (* runs in O(1) *)

  val extract_min: t -> X.t * t
    (* runs in O(log n) *)

  val mem: X.t -> t -> bool

  val insert: X.t -> t -> t
    (* runs in O(log n) *)

  val merge: t -> t -> t
    (* runs in O(log max(n1, n2)) *)

  val delete: X.t -> t -> t
    (* delete one occurrence of given element *)

  val diff: t -> t -> t

  val iter: (X.t -> unit) -> t -> unit

  val fold: ('a -> X.t -> 'a) -> 'a -> t -> 'a

  val filter: (X.t -> bool) -> t -> t 

  (* check whether there is element x such that p x is true; stop search if
     cancel predicate c x is true *)
  val exists: (X.t -> bool) -> (X.t -> bool) -> t -> bool

  val to_list: t -> X.t list
end
