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
module ConstrSet = CSet.Make(Constr)
module StringSet = CSet.Make(String)

(* Unset/Set Debug CodeGen Simplification. *)
let opt_debug_simplification = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"Simplification"];
          optread  = (fun () -> !opt_debug_simplification);
          optwrite = (:=) opt_debug_simplification }

(* Unset/Set Debug CodeGen NormalizeV. *)
let opt_debug_normalizeV = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"NormalizeV"];
          optread  = (fun () -> !opt_debug_normalizeV);
          optwrite = (:=) opt_debug_normalizeV }

(* Unset/Set Debug CodeGen Reduction. *)
let opt_debug_reduction = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"Reduction"];
          optread  = (fun () -> !opt_debug_reduction);
          optwrite = (:=) opt_debug_reduction }

(* Unset/Set Debug CodeGen ReduceExp. *)
let opt_debug_reduce_exp = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"ReduceExp"];
          optread  = (fun () -> !opt_debug_reduce_exp);
          optwrite = (:=) opt_debug_reduce_exp }

(* Unset/Set Debug CodeGen ReduceApp. *)
let opt_debug_reduce_app = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"ReduceApp"];
          optread  = (fun () -> !opt_debug_reduce_app);
          optwrite = (:=) opt_debug_reduce_app }

(* Unset/Set Debug CodeGen Replace. *)
let opt_debug_replace = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"Replace"];
          optread  = (fun () -> !opt_debug_replace);
          optwrite = (:=) opt_debug_replace }

(* Unset/Set Debug CodeGen ReduceEta. *)
let opt_debug_reduce_eta = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"ReduceEta"];
          optread  = (fun () -> !opt_debug_reduce_eta);
          optwrite = (:=) opt_debug_reduce_eta }

(* Unset/Set Debug CodeGen CompleteArguments. *)
let opt_debug_complete_arguments = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"CompleteArguments"];
          optread  = (fun () -> !opt_debug_complete_arguments);
          optwrite = (:=) opt_debug_complete_arguments }

(* Unset/Set Debug CodeGen ExpandEta. *)
let opt_debug_expand_eta = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"ExpandEta"];
          optread  = (fun () -> !opt_debug_expand_eta);
          optwrite = (:=) opt_debug_expand_eta }

(* Unset/Set Debug CodeGen DeleteLet. *)
let opt_debug_delete_let = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"DeleteLet"];
          optread  = (fun () -> !opt_debug_delete_let);
          optwrite = (:=) opt_debug_delete_let }

(* Unset/Set Debug CodeGen BorrowCheck. *)
let opt_debug_borrowcheck = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"BorrowCheck"];
          optread  = (fun () -> !opt_debug_borrowcheck);
          optwrite = (:=) opt_debug_borrowcheck }

(* Unset/Set Debug CodeGen MatchApp. *)
let opt_debug_matchapp = ref false
let () = let open Goptions in declare_bool_option
        { optstage = Summary.Stage.Interp;
          optdepr  = None;
          optkey   = ["Debug";"CodeGen";"MatchApp"];
          optread  = (fun () -> !opt_debug_matchapp);
          optwrite = (:=) opt_debug_matchapp }

let gensym_id = Summary.ref 0 ~name:"CodegenGensymID"

type string_or_qualid = StrOrQid_Str of string | StrOrQid_Qid of Libnames.qualid

type cstr_config = {
  coq_cstr : Id.t;
  c_caselabel : string; (* meaningful if c_swfnc is not None *)
  c_accessors : string array (* meaningful if c_swfnc is not None *)
}

type c_typedata = {
  c_type_left : string;
  c_type_right : string;
}

type ind_config = {
  coq_type : Constr.t;
  c_type : c_typedata;
  c_swfunc : string option;
  cstr_configs : cstr_config array;
  is_void_type : bool;
}

type ind_cstr_caselabel_accessors = Id.t * string * string list

type s_or_d = SorD_S | SorD_D

type id_or_underscore = Id.t option
type constr_or_underscore = Constrexpr.constr_expr option

type sp_instance_names = {
  spi_cfunc_name : string option;
  spi_presimp_id : Id.t option;
  spi_simplified_id : Id.t option;
}

type ind_constructor = {
  ic_coq_cstr : Id.t;
  ic_c_cstr : string;
}

let ind_config_map = Summary.ref (ConstrMap.empty : ind_config ConstrMap.t) ~name:"CodegenIndInfo"

let linearity_type_set = Summary.ref ConstrSet.empty ~name:"CodeGenLinearTypeSet"

(*
  key is (ind args...) or (cstr args...).
*)
let deallocator_cfunc_map = Summary.ref
  (ConstrMap.empty : string ConstrMap.t) ~name:"CodeGenDeallocatorCfuncMap"

let downward_type_set = Summary.ref
  (ConstrSet.empty : ConstrSet.t) ~name:"CodeGenDownwardTypeSet"

let borrow_function_set = Summary.ref
  (Cset.empty : Cset.t) ~name:"CodeGenBorrowFuncSet"

let borrow_type_set = Summary.ref
  (ConstrSet.empty : ConstrSet.t) ~name:"CodeGenBorrowTypeSet"

type simplified_status =
| SpNoSimplification (* constructor or primitive function *)
| SpExpectedId of Id.t (* simplified_id *)
| SpDefined of (Constant.t * StringSet.t) (* (defined-constant, referred-cfuncs) *)

(*
- CodeGenFunc
  Codegen-generated function.  Gallina function only.  Any dynamic argument.
- CodeGenStaticFunc
  Codegen-generated function.  Gallina function only.  Any dynamic argument.
  The generated function is defined as static function.
- CodeGenPrimitive
  User-defined function.  Function or constructor.  Any dynamic argument.
- CodeGenConstant
  User-defined function.  Function or constructor.  No dynamic argument.
  Generate C constant "foo", instead of function call "foo()".
*)
type instance_command =
| CodeGenFunc
| CodeGenStaticFunc
| CodeGenPrimitive
| CodeGenConstant

type specialization_instance = {
  sp_static_arguments : Constr.t list; (* The length should be equal to number of "s" in sp_sd_list *)
  sp_presimp_constr : Constr.t; (* constant or constructor *)
  sp_simplified_status : simplified_status;
  sp_presimp : Constr.t;
  sp_cfunc_name : string;
  sp_icommand : instance_command;
}

type specialization_config = {
  sp_func : Constr.t; (* constant or constructor *)
  sp_is_cstr : bool; (* sp_func is constructor *)
  sp_sd_list : s_or_d list;
  sp_instance_map : specialization_instance ConstrMap.t; (* key is presimp *)
}

(* key is constant or constructor which is the target of specialization *)
let specialize_config_map = Summary.ref (ConstrMap.empty : specialization_config ConstrMap.t) ~name:"CodegenSpecialize"

(*
  key is a constant to refer a presimp (codegen_pN_foo),
  the presimp itself (@cons bool) and
  a constant to refer the simplified definition (codegen_sN_foo).
*)
let gallina_instance_map = Summary.ref ~name:"CodegenGallinaInstance"
  (ConstrMap.empty : (specialization_config * specialization_instance) ConstrMap.t)

(* CodeGenFunc and CodeGenStaticFunc needs unique C function name
  but CodeGenPrimitive and CodeGenConstant don't need. *)
type cfunc_usage =
| CodeGenCfuncGenerate of (specialization_config * specialization_instance) (* CodeGenFunc or CodeGenStaticFunc *)
| CodeGenCfuncPrimitive of (specialization_config * specialization_instance) list (* CodeGenPrimitive or CodeGenConstant *)

let cfunc_instance_map = Summary.ref ~name:"CodegenCInstance"
  (CString.Map.empty : cfunc_usage CString.Map.t)

type string_or_none = string option

let current_header_filename = Summary.ref ~name:"CodegenCurrentHeaderFilename"
  (None : string option)

let current_source_filename = Summary.ref ~name:"CodegenCurrentImplementationFilename"
  (None : string option)

type code_generation =
  GenFunc of string     (* C function name *)
| GenMutual of string list      (* C function names *)
| GenPrototype of string        (* C function name *)
| GenSnippet of string * string  (* section, code fragment *)
| GenThunk of string * (unit -> string)  (* section, code fragment *)

(*
 * map from filename (string) to list of code_generation in reverse order.
 * CodeGen GenerateFile consumes this.
 *)
let generation_map = Summary.ref ~name:"CodegenGenerationMap"
  (CString.Map.empty : (code_generation list) CString.Map.t)

let gensym_ps_num = Summary.ref 0 ~name:"CodegenSpecializationInstanceNum"
let specialize_global_inline = Summary.ref (Cpred.empty : Cpred.t) ~name:"CodegenGlobalInline"
let specialize_local_inline = Summary.ref (Cmap.empty : Cpred.t Cmap.t) ~name:"CodegenLocalInline"

type genflag = DisableDependencyResolver
             | DisableMutualRecursionDetection

