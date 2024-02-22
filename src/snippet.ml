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

open State
open Cgenutil
open Filegen

let fix_snippet (str : string) : string =
  let len = String.length str in
  if 0 < len && str.[len - 1] <> '\n' then
    str ^ "\n"
  else
    str

let add_snippet (section : string) (str : string) : unit =
  check_section section;
  let str' = fix_snippet str in
  codegen_add_source_generation (GenSnippet (section, str'))

let add_header_snippet (section : string) (str : string) : unit =
  check_section section;
  let str' = fix_snippet str in
  codegen_add_header_generation (GenSnippet (section, str'))

let command_snippet (section : string) (str : string) : unit =
  add_snippet section (delete_indent (expand_tab str))

let command_rawsnippet (section : string) (str : string) : unit =
  add_snippet section str

let command_header_snippet (section : string) (str : string) : unit =
  add_header_snippet section (delete_indent (expand_tab str))

let command_header_rawsnippet (section : string) (str : string) : unit =
  add_header_snippet section str

let add_thunk (section : string) (f : unit -> string) : unit =
  codegen_add_source_generation (GenThunk (section, f))

let add_header_thunk (section : string) (f : unit -> string) : unit =
  codegen_add_header_generation (GenThunk (section, f))
