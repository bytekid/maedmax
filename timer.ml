(* Simple start/stop timer
 * Copyright (C) 2004 WingNET Internet Services
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public
 * License along with this library; if not, write to the Free
 * Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *)

(*
 * ----------------------------------------------------------------------------
 *   timer.ml - Simple start/stop timer
 *     Author - Jesse D. Guardiani
 *    Created - 2004/08/16
 *   Modified - 2004/08/16
 * ----------------------------------------------------------------------------
 *
 *  ChangeLog
 *  ---------
 *
 *  2004/08/16 - JDG
 *  ----------------
 *  - Created
 * ----------------------------------------------------------------------------
 * Copyright (C) 2004 WingNET Internet Services
 * Contact: <jesse@wingnet.net>
 * ----------------------------------------------------------------------------
 *)


(** Simple start/stop timer
 *)

exception Not_started;;
exception Not_stopped;;

type resolution = Seconds|Minutes|Hours|Days;;
type timer = {start:float option; mutable stop:float option};;


(**
   [start ()] Start and return [timer].
*)
let start () =
        {
        start=Some (Unix.gettimeofday ());
        stop=None
        }
;;


(**
   [stop timer] Stop [timer].
*)
let stop timer =
        match timer with
          {start=None  ; stop=_} -> raise Not_started
        | {start=Some _; stop=_} -> timer.stop <- Some (Unix.gettimeofday ())
;;


(**
   [length timer] Calculate and return length timer was active.

   @param res Determines returned time resolution; defaults to [Seconds].
*)
let length ?(res=Seconds) timer =
        match timer with
          {start=None  ; stop=     _} -> raise Not_started
        | {start=Some _; stop=None  } -> raise Not_stopped
        | {start=Some s; stop=Some p} -> 
                        let sec = p -. s in
                        match res with
                          Seconds -> sec
                        | Minutes -> sec /. 60.0
                        | Hours   -> sec /. 3600.0
                        | Days    -> sec /. 216000.0
;;

