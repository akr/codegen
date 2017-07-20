(*
Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*)

let () = Mltop.add_known_plugin (fun () ->
  Feedback.msg_info Pp.(str"monomorphization 0.1"))
  "monomorphization"

DECLARE PLUGIN "monomorphization_plugin"

open Monomorph
open Genc

open Stdarg (* for wit_string *)
open Constrarg (* for wit_global *)
open Extraargs (* for lconstr(...). lconstr accepts "Com 1 + 1" addition to "Com (1 + 1)" *)

VERNAC COMMAND EXTEND Monomorphization CLASSIFIED AS SIDEFF
    | [ "Monomorphization" ne_global_list(libref_list) ] ->
      [ monomorphization libref_list ]
    | [ "Terminate" "Monomorphization" lconstr(term) ] ->
      [ terminate_monomorphization term ]
    | [ "GenC" ne_global_list(libref_list) ] -> [ genc libref_list ]
    | [ "GenCFile" string(fn) ne_global_list(libref_list) ] ->
      [ genc_file fn libref_list ]
END;;
