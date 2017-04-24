val init : int -> (int -> 'a) -> 'a list

val ix : ?i:int -> 'a list -> (int * 'a) list

val unique : 'a list -> 'a list

val copy : int -> 'a -> 'a list

(* combinatorial functions *)

val product : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

val pi : 'a list list -> 'a list list
  (** pi [l1; .. ; lN] returns the list of the certesian product l1 * .. * lN *)

val nth_power : 'a list -> int -> 'a list list

val power : 'a list -> 'a list list

val suffix : 'a list -> 'a list list

val prefix : 'a list -> 'a list list

val interleave : 'a -> 'a list -> 'a list list

val permutation : 'a list -> 'a list list

val partitions : 'a list -> 'a list list list

val transpose : 'a list list -> 'a list list

val group : ('a * 'b) list -> ('a * 'b list) list

val group_by : ('a -> 'b) -> 'a list -> ('b * 'a list) list

val count : 'a list -> ('a * int) list

val fold_left1 : ('a -> 'a -> 'a) -> 'a list -> 'a

(* list operations for integer lists. *)

val max : int list -> int

val min : int list -> int

val sum : int list -> int

val interval : int -> int -> int list

val index : ?i:int -> 'a list -> (int * 'a) list 

val take : int -> 'a list -> 'a list

val take_at_most : int -> 'a list -> 'a list

val split_at_most : int -> 'a list -> 'a list * 'a list

val drop : int -> 'a list -> 'a list

val print : (Format.formatter -> 'a -> unit)
  -> (unit,Format.formatter,unit) format
  -> 'a list -> unit

val to_string : ('a -> string) -> string -> 'a list -> string

val remove: 'a -> 'a list -> 'a list

val pos: 'a -> 'a list -> int

val cons : 'a -> 'a list -> 'a list
