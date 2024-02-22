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
  "header_prologue";
  "header_type_decls";
  "header_type_impls";
  "header_func_decls";
  "header_func_impls";
  "header_epilogue";
  "source_prologue";
  "source_type_decls";
  "source_type_impls";
  "source_func_decls";
  "source_func_impls";
  "soruce_epilogue";
]

let codegen_add_generation (filename : string) (section : string) (generation : code_generation) : unit =
  (if not (List.mem section defined_sections) then
    user_err_hov (Pp.str "[codegen] unexpected section:" +++ Pp.str section));
  generation_map := !generation_map |> CString.Map.update filename
    (fun section_map_opt ->
      match section_map_opt with
      | None -> Some (CString.Map.singleton section [generation])
      | Some section_map ->
          Some (section_map |> CString.Map.update section
            (fun generation_list_opt ->
              match generation_list_opt with
              | None -> Some [generation]
              | Some generation_list -> Some (generation :: generation_list))))

let codegen_add_source_generation (section : string) (generation : code_generation) : unit =
  match !current_source_filename with
  | None -> Feedback.msg_warning (Pp.str "[codegen] no code will be generated because no CodeGen Source File.")
  | Some filename ->
      codegen_add_generation filename section generation

let codegen_add_header_generation (section : string) (generation : code_generation) : unit =
  match !current_header_filename with
  | None -> ()
  | Some filename ->
      codegen_add_generation filename section generation
