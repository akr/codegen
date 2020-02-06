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

(* Set/Unset Debug CodeGen Specialization. *)
let opt_debug_specialization = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables printing trace of specialization";
          optkey   = ["Debug";"CodeGen";"Specialization"];
          optread  = (fun () -> !opt_debug_specialization);
          optwrite = (:=) opt_debug_specialization }

(* Set/Unset Debug CodeGen NormalizeK. *)
let opt_debug_normalizeK = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables printing trace of normarizeK";
          optkey   = ["Debug";"CodeGen";"NormalizeK"];
          optread  = (fun () -> !opt_debug_normalizeK);
          optwrite = (:=) opt_debug_normalizeK }

(* Set/Unset Debug CodeGen Reduction. *)
let opt_debug_reduction = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables printing trace of reduction steps";
          optkey   = ["Debug";"CodeGen";"Reduction"];
          optread  = (fun () -> !opt_debug_reduction);
          optwrite = (:=) opt_debug_reduction }

(* Set/Unset Debug CodeGen ReduceExp. *)
let opt_debug_reduce_exp = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables printing trace of reduce_exp";
          optkey   = ["Debug";"CodeGen";"ReduceExp"];
          optread  = (fun () -> !opt_debug_reduce_exp);
          optwrite = (:=) opt_debug_reduce_exp }

(* Set/Unset Debug CodeGen Replace. *)
let opt_debug_replace = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables printing trace of replacement of general function by specialized function";
          optkey   = ["Debug";"CodeGen";"Replace"];
          optread  = (fun () -> !opt_debug_replace);
          optwrite = (:=) opt_debug_replace }

(* Set/Unset Debug CodeGen ExpandEta. *)
let opt_debug_expand_eta = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables printing trace of expand_eta";
          optkey   = ["Debug";"CodeGen";"ExpandEta"];
          optread  = (fun () -> !opt_debug_expand_eta);
          optwrite = (:=) opt_debug_expand_eta }

(* Set/Unset Debug CodeGen DeleteLet. *)
let opt_debug_delete_let = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables printing trace of delete_let";
          optkey   = ["Debug";"CodeGen";"DeleteLet"];
          optread  = (fun () -> !opt_debug_delete_let);
          optwrite = (:=) opt_debug_delete_let }

(* Set/Unset CodeGen Dev. *)
let opt_codegen_dev = ref false
let () = let open Goptions in declare_bool_option
        { optdepr  = false;
          optname  = "Enables code generator of development version";
          optkey   = ["CodeGen";"Dev"];
          optread  = (fun () -> !opt_codegen_dev);
          optwrite = (:=) opt_codegen_dev }

let gensym_id = Summary.ref 0 ~name:"CodegenGensymID"

type cstr_config = {
  coq_cstr : Id.t;
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
  sp_static_arguments : Constr.t list; (* The length should be equal to number of "s" in sp_sd_list *)
  sp_partapp_constr : Constr.t; (* constant or constructor *)
  sp_specialization_name : specialization_instance_name_status;
  sp_partapp : Constr.t;
  sp_cfunc_name : string;
  sp_gen_constant : bool; (* Generate C constant "foo",
                             instead of function call "foo()".
                             true for CodeGen Constant.
                             false for CodeGen Function and Primitive.
                            *)
}

type specialization_config = {
  sp_func : Constr.t; (* constant or constructor *)
  sp_sd_list : s_or_d list;
  sp_instance_map : specialization_instance ConstrMap.t; (* key is partapp *)
}

(* key is constant or constructor which is the target of specialization *)
let specialize_config_map = Summary.ref (ConstrMap.empty : specialization_config ConstrMap.t) ~name:"CodegenSpecialize"

(*
  key is a constant to refer a partapp (codegen_pN_foo),
  the partapp itself (@cons bool) and
  a constant to refer the specialized definition (codegen_sN_foo).
*)
let gallina_instance_map = Summary.ref ~name:"CodegenGallinaInstance"
  (ConstrMap.empty : (specialization_config * specialization_instance) ConstrMap.t)

let cfunc_instance_map = Summary.ref ~name:"CodegenCInstance"
  (CString.Map.empty : (specialization_config * specialization_instance) CString.Map.t)

type code_generation =
  GenFunc of string
| GenSnippet of string

(*
 * list of code_generation in reverse order.
 * CodeGen GenerateFile consumes this list.
 *)
let generation_list = Summary.ref ~name:"CodegenGeneration"
  ([] : code_generation list)

let gensym_ps_num = Summary.ref 0 ~name:"CodegenSpecializationInstanceNum"
let specialize_global_inline = Summary.ref (Cpred.empty : Cpred.t) ~name:"CodegenGlobalInline"
let specialize_local_inline = Summary.ref (Cmap.empty : Cpred.t Cmap.t) ~name:"CodegenLocalInline"
