module Logic = Yicesx

class type t = object
  method bot: Signature.sym option
  method gt: Term.t -> Term.t -> bool
  method gt_extend_sig: Signature.sym list -> Term.t -> Term.t -> bool
  method smt_encode: Logic.context -> Logic.t
  method to_string : string
  method print : unit -> unit
  method to_xml : Xml.xml
  method print_params : unit -> unit
end

let default = object(self)
  method bot = None
  method gt _ _ = false
  method gt_extend_sig _ _ _ = false
  method smt_encode = Logic.mk_false
  method to_string = "(default order)"
  method print = (fun _ -> Format.printf "%s\n%!" self#to_string)
  method to_xml = Xml.Element("unknownOrder", [], [])
  method print_params = (fun _ -> Format.printf "-t Foo\n%!")
end

let extend_sig order syms = object
  method bot = order#bot
  method gt = order#gt_extend_sig syms
  method gt_extend_sig = order#gt_extend_sig
  method smt_encode = order#smt_encode
  method to_string = order#to_string
  method print = order#print
  method to_xml = order#to_xml
  method print_params = order#print_params
end