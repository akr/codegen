(*
Copyright (C) 2019- National Institute of Advanced Industrial Science and Technology (AIST)

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

open Names

module ConstrMap = HMap.Make(Constr)

let gensym_id = Summary.ref 0 ~name:"CodegenGensymID"

type cstr_config = {
  coq_cstr : Id.t;
  c_cstr : string option;
  c_caselabel : string; (* meaningful if c_swfnc is not None *)
  c_accessors : string array (* meaningful if c_swfnc is not None *)
}

type ind_config = {
  coq_type : Constr.t;
  c_type : string;
  c_swfunc : string option;
  cstr_configs : cstr_config array
}

type ind_cstr_caselabel_accessors = Id.t * string * string list

type s_or_d = SorD_S | SorD_D

type id_or_underscore = Id.t option
type constr_or_underscore = Constrexpr.constr_expr option

type sp_instance_names = {
  spi_cfunc_name : string option;
  spi_partapp_id : Id.t option;
  spi_specialized_id : Id.t option
}

type ind_constructor = {
  ic_coq_cstr : Id.t;
  ic_c_cstr : string;
}

let ind_config_map = Summary.ref (ConstrMap.empty : ind_config ConstrMap.t) ~name:"CodegenIndInfo"

type type_linearity = Linear | Unrestricted | Investigating
let type_linearity_list_empty : (EConstr.t * type_linearity) list = []
let type_linearity_list = Summary.ref type_linearity_list_empty ~name:"CodeGenLinearTypeList"

let mono_global_visited_empty : ((GlobRef.t * EConstr.constr array) * Constant.t) list = []
let mono_global_visited = Summary.ref mono_global_visited_empty ~name:"MonomorphizationVisited"

type specialization_instance_name_status =
  SpExpectedId of Id.t | SpDefinedCtnt of Constant.t

type specialization_instance = {
  sp_static_arguments : Constr.t list; (* The length should be equal to number of "s" *)
  sp_partapp_ctnt : Constant.t;
  sp_specialization_name : specialization_instance_name_status;
  sp_partapp : Constr.t;
  sp_cfunc_name : string;
}

type specialization_config = {
  sp_func : Constant.t;
  sp_sd_list : s_or_d list;
  sp_instance_map : specialization_instance ConstrMap.t;
}

let specialize_config_map = Summary.ref (Cmap.empty : specialization_config Cmap.t) ~name:"CodegenSpecialize"
let gallina_instance_map = Summary.ref ~name:"CodegenGallinaInstance"
  (ConstrMap.empty : (specialization_config * specialization_instance) ConstrMap.t)

let cfunc_instance_map = Summary.ref ~name:"CodegenCInstance"
  (CString.Map.empty : (specialization_config * specialization_instance) CString.Map.t)

(*
 * list of cfunc_name in reverse order.
 * CodeGen EndFile consumes this list.
 *
 * This list will be extended to support non-cfunc-element such as
 * inductive type definition, code snippet specified by user, etc.
 *)
let generation_list = Summary.ref ~name:"CodegenGeneration"
  ([] : string list)

let gensym_ps_num = Summary.ref 0 ~name:"CodegenSpecializationInstanceNum"
let specialize_global_inline = Summary.ref (Cpred.empty : Cpred.t) ~name:"CodegenGlobalInline"
let specialize_local_inline = Summary.ref (Cmap.empty : Cpred.t Cmap.t) ~name:"CodegenLocalInline"
