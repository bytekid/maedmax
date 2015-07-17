val empty : 'a list
val singleton : 'a -> 'a list
val is_empty : 'a list -> bool
val unique : 'a list -> 'a list
val add : 'a -> 'a list -> 'a list
val subset : 'a list -> 'a list -> bool
val equal : 'a list -> 'a list -> bool
val union : 'a list -> 'a list -> 'a list
val big_union : 'a list list -> 'a list
val inter : 'a list -> 'a list -> 'a list
val diff : 'a list -> 'a list -> 'a list
val remove : 'a -> 'a list -> 'a list
val concat : 'a list list -> 'a list
