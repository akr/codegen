module ConstrMap : CMap.UExtS with type key = Constr.t
module ConstrSet : CSet.S with type elt = Constr.t
module StringSet : CSet.S with type elt = String.t

val optread_indimp_auto_linear : unit -> bool
val optread_debug_simplification : unit -> bool
val optread_debug_normalizeV : unit -> bool
val optread_debug_reduction : unit -> bool
val optread_debug_reduce_exp : unit -> bool
val optread_debug_reduce_app : unit -> bool
val optread_debug_replace : unit -> bool
val optread_debug_reduce_eta : unit -> bool
val optread_debug_complete_arguments : unit -> bool
val optread_debug_expand_eta : unit -> bool
val optread_debug_delete_let : unit -> bool
val optread_debug_borrowcheck : unit -> bool
val optread_debug_matchapp : unit -> bool

val global_gensym : ?prefix:string -> unit -> string

type string_or_qualid =
    StrOrQid_Str of string
  | StrOrQid_Qid of Libnames.qualid

type cstr_interface =
| CiPrimitive of string
| CiConstant of string
| CiNoFunc

type cstr_mod = {
  cm_interface: cstr_interface option;
  cm_caselabel: string option;
  cm_accessors: string option array;
  cm_deallocator: string option;
}

type cstr_config = {
  cstr_id: Names.Id.t;
  cstr_caselabel: string option;
  cstr_accessors: string option array;
  cstr_deallocator: string option;
}

type c_typedata = {
  c_type_left : string;
  c_type_right : string;
}
type ind_config = {
  ind_coq_type : Constr.t;
  ind_c_type : c_typedata option;
  ind_c_swfunc : string option;
  ind_cstr_configs : cstr_config array;
}

type s_or_d = SorD_S | SorD_D
type id_or_underscore = Names.Id.t option
type constr_or_underscore = Constrexpr.constr_expr option
type sp_instance_names = {
  spi_cfunc_name : string option;
  spi_presimp_id : Names.Id.t option;
  spi_simplified_id : Names.Id.t option;
}
type ind_constructor = { ic_coq_cstr : Names.Id.t; ic_c_cstr : string; }

val get_ind_config_map : unit -> ind_config ConstrMap.t
val add_ind_config : Constr.t -> ind_config -> unit

val get_linearity_types : unit -> ConstrSet.t
val add_linear_type : Constr.t -> unit

type dealloc_cstr_deallocator = {
  dealloc_cstr_id: Names.Id.t;
  dealloc_cstr_deallocator: string;
}

val get_downward_types : unit -> ConstrSet.t
val add_downward_type : Constr.t -> unit

val get_borrow_functions : unit -> Names.Cset.t
val add_borrow_function : Names.Constant.t -> unit

val get_borrow_types : unit -> ConstrSet.t
val add_borrow_types : ConstrSet.t -> unit

type simplified_status =
  | SpExpectedId of Names.Id.t (* simplified_id *)
  | SpDefined of (Names.Constant.t * StringSet.t)
type instance_command =
    CodeGenFunc
  | CodeGenPrimitive
  | CodeGenConstant
  | CodeGenNoFunc
type specialization_instance_gen = {
  sp_static_storage : bool;
  sp_simplified_status : simplified_status;
}
type specialization_instance_interface = {
  sp_presimp_constr : Constr.t; (* not used for CodeGenNoFunc *)
  sp_cfunc_name : string; (* not used for CodeGenNoFunc *)
  sp_gen : specialization_instance_gen option; (* None for CodeGenPrimitive and CodeGenConstant. Some for CodeGenFunc. *)
}
type specialization_instance = {
  sp_static_arguments : Constr.t option list;
  sp_presimp : Constr.t;
  sp_interface : specialization_instance_interface option; (* None for CodeGenNoFunc. *)
  sp_icommand : instance_command;
}
type specialization_config = {
  sp_func : Constr.t;
  sp_is_cstr : bool;
  sp_sd_list : s_or_d list;
  sp_instance_map : specialization_instance ConstrMap.t;
}

val get_specialize_config_map : unit -> specialization_config ConstrMap.t
val add_specialize_config : Constr.t -> specialization_config -> unit

val get_gallina_instance_specialization_map : unit -> (specialization_config * specialization_instance) ConstrMap.t
val add_gallina_instance_specialization : Constr.t -> specialization_config -> specialization_instance -> unit
val set_gallina_instance_specialization : Constr.t -> specialization_config -> specialization_instance -> unit

val get_gallina_instance_codegeneration_map : unit -> (specialization_config * specialization_instance) ConstrMap.t
val add_gallina_instance_codegeneration : Constr.t -> specialization_config -> specialization_instance -> unit
val set_gallina_instance_codegeneration : Constr.t -> specialization_config -> specialization_instance -> unit

type cfunc_usage =
| CodeGenCfuncGenerate of (specialization_config * specialization_instance * specialization_instance_interface * specialization_instance_gen) (* CodeGenFunc *)
| CodeGenCfuncPrimitive of (specialization_config * specialization_instance) list (* CodeGenPrimitive or CodeGenConstant *)

val get_cfunc_instance_map : unit -> cfunc_usage CString.Map.t
val update_cfunc_instance_map : (cfunc_usage CString.Map.t -> cfunc_usage CString.Map.t) -> unit

type string_or_none = string option
val dummy_header_filename : string
val dummy_source_filename : string

val get_current_header_filename : unit -> string
val set_current_header_filename : string -> unit

val get_current_source_filename : unit -> string
val set_current_source_filename : string -> unit

type code_generation =
    GenFunc of string
  | GenMutual of string list
  | GenPrototype of string
  | GenSnippet of string * string
  | GenThunk of string * (unit -> string)

val get_generation_map : unit -> (code_generation list) CString.Map.t
val set_generation_map : (code_generation list) CString.Map.t -> unit
val update_generation_map : ((code_generation list) CString.Map.t -> (code_generation list) CString.Map.t) -> unit

val inc_gensym_ps_num : unit -> int

val get_specialize_global_inline : unit -> Names.Cpred.t
val update_specialize_global_inline : (Names.Cpred.t -> Names.Cpred.t) -> unit

val get_specialize_local_inline : unit -> Names.Cpred.t Names.Cmap.t
val update_specialize_local_inline : (Names.Cpred.t Names.Cmap.t -> Names.Cpred.t Names.Cmap.t) -> unit

type genflag = DisableDependencyResolver | DisableMutualRecursionDetection
