class type t = object
  method bot: Signature.sym option;;
  method gt: Term.t -> Term.t -> bool;;
  method print : unit -> unit;;
  method to_xml : Xml.xml
  method print_params : unit -> unit
end

let default = object
  method bot = None;;
  method gt _ _ = false;;
  method print = (fun _ -> Format.printf "(default order)\n%!")
  method to_xml = Xml.Element("unknownOrder", [], [])
  method print_params = (fun _ -> Format.printf "-t Foo\n%!")
end
