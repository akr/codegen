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

let fix_snippet (str : string) : string =
  let len = String.length str in
  if 0 < len && str.[len - 1] <> '\n' then
    str ^ "\n"
  else
    str

let add_snippet (str : string) : unit =
  let str' = fix_snippet str in
  codegen_add_source_generation (GenSnippet str')

let add_header_snippet (str : string) : unit =
  let str' = fix_snippet str in
  codegen_add_header_generation (GenSnippet str')

let command_snippet (str : string) : unit =
  add_snippet str

let command_header_snippet (str : string) : unit =
  add_header_snippet str
