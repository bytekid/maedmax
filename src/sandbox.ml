(* $Id *)
(** TODO: 
 - Currently only child process is killed. If that process creates
children they become zombies 
 - Is it allowed to raise a timeout in the signal handler ???

*)

(*** TYPES ***************************************************************)

(*** EXCEPTIONS **********************************************************)
exception Timeout;;

(*** SUBMODULES **********************************************************)

(*** GLOBALS *************************************************************)

(*** FUNCTIONS ***********************************************************)
let handler pid _ = raise Timeout 
;;

let enable t pid = 
 Sys.set_signal Sys.sigalrm (Sys.Signal_handle (handler pid));
 let status = 
  {Unix.it_interval = 0.0;
  Unix.it_value = t}
 in
 ignore (Unix.setitimer Unix.ITIMER_REAL status)
;;

let help () = 
 if Array.length Sys.argv < 3 then begin
  Format.printf "This is a sandbox!@\n";
  Format.printf 
   "Syntax: <%s> <timeout> <command> [option1] [option2] ..." Sys.argv.(0);
  exit 1
 end
;;

let main () =
 help ();
 let offset = 2 in
 let cmd_length = (Array.length Sys.argv) - offset in
 let cmd = Array.make cmd_length "" in
 for i = 0 to cmd_length - 1 do
  cmd.(i) <- Sys.argv.(i + offset);
 done;
 let pid = Unix.fork () in
 if pid < 0 then begin
  failwith "Something wrong with fork ()"
 end else if pid = 0 then begin (* son *)
  Unix.execvp cmd.(0) cmd;
 end else begin (* father *)
  try
  enable (float_of_string Sys.argv.(1)) pid;
  ignore (Unix.waitpid [] pid);
  with
   | Timeout -> 
    Unix.kill pid Sys.sigkill;
    Format.printf "TIMEOUT@\n";
 end;
;;

main ();;
(*** TESTS ***************************************************************)
(* [test ()] should perform a nice test suite for the modul under 
consideration *)

