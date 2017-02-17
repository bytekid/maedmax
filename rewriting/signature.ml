type var = int

type sym = int

type t = (sym * int) list

let var_count = ref 0

let fun_count = ref 0

let fun_name : (int, string) Hashtbl.t = Hashtbl.create 32
let name_fun : (string,int) Hashtbl.t = Hashtbl.create 32

let var_name : (int,string) Hashtbl.t = Hashtbl.create 32
let name_var : (string,int) Hashtbl.t = Hashtbl.create 32

let get_var_name x =
  try Hashtbl.find var_name x
  with Not_found -> "X" ^ (string_of_int x)

let get_fun_name x =
  try Hashtbl.find fun_name x
  with Not_found -> "F" ^ (string_of_int x)

let fresh_fun_called name =
 let i = !fun_count in
 incr fun_count;
 Hashtbl.add fun_name i name;
 Hashtbl.add name_fun name i;
 i
;;

let fresh_var_called name =
 let i = !var_count in
 incr var_count;
 Hashtbl.add var_name i name;
 Hashtbl.add name_var name i;
 i
;;

let fun_called name =
 try Hashtbl.find name_fun name with Not_found ->
 fresh_fun_called name
;;

let var_called name =
 try Hashtbl.find name_var name with Not_found ->
 fresh_var_called name
;;

let fresh_var () =
 let i = !var_count in
 incr var_count;
 let name = "x"^(string_of_int i) in
 Hashtbl.add var_name i name;
 Hashtbl.add name_var name i;
 i
;;

let sharp_fun f =
 let n = get_fun_name f in fun_called (n ^ "#")
;;

