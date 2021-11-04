module ConstrMap : CMap.ExtS with type key = Constr.t
module StringSet : CSet.S with type elt = String.t
                          and type t = Set.Make(String).t

val opt_debug_simplification : bool ref
val opt_debug_normalizeV : bool ref
val opt_debug_reduction : bool ref
val opt_debug_reduce_exp : bool ref
val opt_debug_reduce_app : bool ref
val opt_debug_replace : bool ref
val opt_debug_expand_eta : bool ref
val opt_debug_delete_let : bool ref
val gensym_id : int ref
type string_or_qualid =
    StrOrQid_Str of string
  | StrOrQid_Qid of Libnames.qualid
type cstr_config = {
  coq_cstr : Names.Id.t;
  c_caselabel : string;
  c_accessors : string array;
}
type ind_config = {
  coq_type : Constr.t;
  c_type : string;
  c_swfunc : string option;
  cstr_configs : cstr_config array;
}
type ind_cstr_caselabel_accessors = Names.Id.t * string * string list
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
type type_linearity = Linear | Unrestricted | Investigating
val type_linearity_map_empty : type_linearity ConstrMap.t
val type_linearity_map : type_linearity ConstrMap.t ref
val deallocator_cfunc_of_type : string ConstrMap.t ref
type simplified_status =
    SpNoSimplification
  | SpExpectedId of Names.Id.t
  | SpDefined of (Names.Constant.t * StringSet.t)
type instance_command =
    CodeGenFunction
  | CodeGenStaticFunction
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
val cfunc_instance_map :
  (specialization_config * specialization_instance) CString.Map.t ref
type string_or_none = string option
val current_header_filename : string option ref
val current_source_filename : string option ref
type code_generation =
    GenFunc of string
  | GenMutual of string list
  | GenPrototype of string
  | GenSnippet of string
val generation_map : code_generation list CString.Map.t ref
val codegen_add_generation : CString.Map.key -> code_generation -> unit
val codegen_add_source_generation : code_generation -> unit
val codegen_add_header_generation : code_generation -> unit
val gensym_ps_num : int ref
val specialize_global_inline : Names.Cpred.t ref
val specialize_local_inline : Names.Cpred.t Names.Cmap.t ref
type genflag = DisableDependencyResolver | DisableMutualRecursionDetection
