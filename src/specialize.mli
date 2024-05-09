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
  Constr.t ->
  Constr.t list ->
  State.sp_instance_names option ->
  Environ.env * State.specialization_instance
val command_function :
  Libnames.qualid ->
  Constrexpr.constr_expr option list -> State.sp_instance_names -> unit
val command_static_function :
  Libnames.qualid ->
  Constrexpr.constr_expr option list -> State.sp_instance_names -> unit
val command_primitive :
  Libnames.qualid ->
  Constrexpr.constr_expr option list -> State.sp_instance_names -> unit
val command_constant :
  Libnames.qualid ->
  Constrexpr.constr_expr list -> State.sp_instance_names -> unit
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
val command_deallocator : Constrexpr.constr_expr -> string -> unit
