class type t = object
  method bot: Signature.sym option;;
  method gt: Term.t -> Term.t -> bool;;
  method print : unit -> unit;;
  method to_xml : Xml.xml
end

let default = object
  method bot = None;;
  method gt _ _ = false;;
  method print = (fun _ -> Format.printf "(default order)\n%!")
  method to_xml = Xml.Element("unknownOrder", [], [])
end
