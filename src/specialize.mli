type func_mods = {
  func_mods_static : bool option;
}
val func_mods_empty : func_mods
val merge_func_mods : func_mods -> func_mods -> func_mods

val command_print_specialization : Libnames.qualid list -> unit
val func_of_qualid : Environ.env -> Evd.evar_map -> Libnames.qualid -> Evd.evar_map * Constr.t
val codegen_define_or_check_static_arguments : ?cfunc:string -> Environ.env -> Evd.evar_map -> Constr.t -> State.s_or_d list -> State.specialization_config
val command_arguments : Libnames.qualid -> State.s_or_d list -> unit
val codegen_auto_arguments_internal :
  ?cfunc:string ->
  Environ.env -> Evd.evar_map -> Constr.t -> State.specialization_config
val command_auto_arguments : Libnames.qualid list -> unit
val command_test_args : Libnames.qualid -> State.s_or_d list -> unit
val codegen_define_instance :
  ?cfunc:string ->
  Environ.env ->
  Evd.evar_map ->
  State.instance_command ->
  bool ->
  Constr.t ->
  Constr.t list ->
  State.sp_instance_names option ->
  Environ.env * State.specialization_instance
val command_function :
  Constrexpr.constr_expr ->
  State.sp_instance_names -> func_mods -> unit
val command_primitive :
  Constrexpr.constr_expr -> State.sp_instance_names -> unit
val command_constant :
  Constrexpr.constr_expr -> State.sp_instance_names -> unit
val command_nofunc :
  Constrexpr.constr_expr -> unit
val command_global_inline : Libnames.qualid list -> unit
val command_local_inline : Libnames.qualid -> Libnames.qualid list -> unit
val codegen_simplify :
  string -> Environ.env * Names.Constant.t * State.StringSet.t
val command_simplify_function : string list -> unit
val command_simplify_dependencies : string list -> unit
val codegen_resolve_dependencies :
  State.code_generation list -> State.code_generation list
val command_resolve_dependencies : unit -> unit
val command_print_generation_list : State.code_generation list -> unit
val command_print_generation_map : unit -> unit
