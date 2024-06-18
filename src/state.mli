module ConstrMap : CMap.ExtS with type key = Constr.t
module ConstrSet : CSet.S with type elt = Constr.t
module StringSet : CSet.S with type elt = String.t

val opt_indimp_auto_linear : bool ref
val opt_debug_simplification : bool ref
val opt_debug_normalizeV : bool ref
val opt_debug_reduction : bool ref
val opt_debug_reduce_exp : bool ref
val opt_debug_reduce_app : bool ref
val opt_debug_replace : bool ref
val opt_debug_reduce_eta : bool ref
val opt_debug_complete_arguments : bool ref
val opt_debug_expand_eta : bool ref
val opt_debug_delete_let : bool ref
val opt_debug_borrowcheck : bool ref
val opt_debug_matchapp : bool ref

val gensym_id : int ref
type string_or_qualid =
    StrOrQid_Str of string
  | StrOrQid_Qid of Libnames.qualid
type cstr_config = {
  coq_cstr : Names.Id.t;
  c_caselabel : string;
  c_accessors : string array;
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
type ind_cstr_caselabel_accessors = {
  cstr_id: Names.Id.t;
  cstr_caselabel: string;
  cstr_accessors: string list;
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
val ind_config_map : ind_config ConstrMap.t ref
val linearity_type_set : ConstrSet.t ref

type dealloc_cstr_deallocator = {
  dealloc_cstr_id: Names.Id.t;
  dealloc_cstr_deallocator: string;
}
val cstr_deallocator_cfunc_map : string ConstrMap.t ref

val downward_type_set : ConstrSet.t ref
val borrow_function_set : Names.Cset.t ref
val borrow_type_set : ConstrSet.t ref

type simplified_status =
    SpNoSimplification
  | SpExpectedId of Names.Id.t (* simplified_id *)
  | SpDefined of (Names.Constant.t * StringSet.t)
type instance_command =
    CodeGenFunc
  | CodeGenStaticFunc
  | CodeGenPrimitive
  | CodeGenConstant
type specialization_instance = {
  sp_static_arguments : Constr.t list;
  sp_presimp_constr : Constr.t;
  sp_simplified_status : simplified_status;
  sp_presimp : Constr.t;
  sp_cfunc_name : string;
  sp_icommand : instance_command;
}
type specialization_config = {
  sp_func : Constr.t;
  sp_is_cstr : bool;
  sp_sd_list : s_or_d list;
  sp_instance_map : specialization_instance ConstrMap.t;
}
val specialize_config_map : specialization_config ConstrMap.t ref
val gallina_instance_map :
  (specialization_config * specialization_instance) ConstrMap.t ref

type cfunc_usage =
| CodeGenCfuncGenerate of (specialization_config * specialization_instance) (* CodeGenFunc or CodeGenStaticFunc *)
| CodeGenCfuncPrimitive of (specialization_config * specialization_instance) list (* CodeGenPrimitive or CodeGenConstant *)
val cfunc_instance_map :
  cfunc_usage CString.Map.t ref
type string_or_none = string option
val current_header_filename : string option ref
val current_source_filename : string option ref
type code_generation =
    GenFunc of string
  | GenMutual of string list
  | GenPrototype of string
  | GenSnippet of string * string
  | GenThunk of string * (unit -> string)
val generation_map : (code_generation list) CString.Map.t ref
val gensym_ps_num : int ref
val specialize_global_inline : Names.Cpred.t ref
val specialize_local_inline : Names.Cpred.t Names.Cmap.t ref
type genflag = DisableDependencyResolver | DisableMutualRecursionDetection
