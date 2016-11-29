type 'a printer = Format.formatter -> 'a -> unit

val print_list : 'a printer ->
 ('a printer -> 'a -> unit, Format.formatter, unit, unit, unit,
  'b printer -> 'b -> unit) format6 -> ('a list) printer

val print_eqs : 'a printer -> 'b printer -> (('a * 'b) list) printer
