(*
Copyright (C) 2024- National Institute of Advanced Industrial Science and Technology (AIST)

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

open State
open Cgenutil

let defined_sections = [
  "prologue";
  "type_decls";
  "type_impls";
  "func_decls";
  "func_impls";
  "epilogue";
]

let codegen_add_generation (filename : string) (generation : code_generation) : unit =
  generation_map := !generation_map |> CString.Map.update filename
    (fun generation_list_opt ->
      match generation_list_opt with
      | None -> Some [generation]
      | Some generation_list -> Some (generation :: generation_list))

let codegen_add_source_generation (generation : code_generation) : unit =
  match !current_source_filename with
  | None -> Feedback.msg_warning (Pp.str "[codegen] no code will be generated because no CodeGen Source File.")
  | Some filename ->
      codegen_add_generation filename generation

let codegen_add_header_generation (generation : code_generation) : unit =
  match !current_header_filename with
  | None -> ()
  | Some filename ->
      codegen_add_generation filename generation

let check_section (section : string) : unit =
  (if not (List.mem section defined_sections) then
    user_err_hov (Pp.str "[codegen] unexpected section:" +++ Pp.str section))
