(* Simple start/stop timer based on code by
   Jesse D. Guardiani (C) 2004 WingNET Internet Services
   plus functionality to run function timed *)

exception Timeout

type resolution = Seconds | Minutes | Hours | Days

type timer

val start : unit -> timer

val stop : timer -> unit

val length : ?res:resolution -> timer -> float

val run_timed : float option -> ('a -> 'b) -> 'a -> ('b option * float)
