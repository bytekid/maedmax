module Logic = Yicesx

class type t = object
  method bot: Signature.sym option
  method gt: Term.t -> Term.t -> bool
  method smt_encode: Logic.context -> Logic.t
  method to_string : string
  method print : unit -> unit
  method to_xml : Xml.xml
  method print_params : unit -> unit
end

let default = object(self)
  method bot = None
  method gt _ _ = false
  method smt_encode = Logic.mk_false
  method to_string = "(default order)"
  method print = (fun _ -> Format.printf "%s\n%!" self#to_string)
  method to_xml = Xml.Element("unknownOrder", [], [])
  method print_params = (fun _ -> Format.printf "-t Foo\n%!")
end
