type c =
 TRS of int | NEG of c | AND of c list | OR of c list |
 BOT | TOP | R of Rule.t

type t = Rule.t * c

val (<&>) : c -> c -> c

val big_and : c list -> c

val (<|>) : c -> c -> c

val print_ceq : Format.formatter -> t -> unit

val idx : Rule.t -> int

val rules : c -> int list
