val pr_s_or_d : State.s_or_d -> Pp.t
val drop_trailing_d : State.s_or_d list -> State.s_or_d list
val is_function_icommand : State.instance_command -> bool
val string_of_icommand : State.instance_command -> string
val pr_constant_or_constructor : Environ.env -> Constr.t -> Pp.t
val pr_codegen_arguments :
  Environ.env -> Evd.evar_map -> State.specialization_config -> Pp.t
val pr_codegen_instance :
  Environ.env ->
  Evd.evar_map ->
  State.specialization_config -> State.specialization_instance -> Pp.t
val command_print_specialization : Libnames.qualid list -> unit
val func_of_qualid : Environ.env -> Libnames.qualid -> Constr.t
val codegen_define_static_arguments :
  ?cfunc:string ->
  Environ.env ->
  Evd.evar_map ->
  Constr.t -> State.s_or_d list -> State.specialization_config
val codegen_define_or_check_static_arguments :
  ?cfunc:string ->
  Environ.env ->
  Evd.evar_map ->
  Constr.t -> State.s_or_d list -> State.specialization_config
val command_arguments : Libnames.qualid -> State.s_or_d list -> unit
val determine_static_arguments :
  Environ.env -> Evd.evar_map -> EConstr.t -> bool list
val determine_sd_list :
  Environ.env -> Evd.evar_map -> EConstr.t -> State.s_or_d list
val codegen_auto_arguments_internal :
  ?cfunc:string ->
  Environ.env -> Evd.evar_map -> Constr.t -> State.specialization_config
val codegen_auto_sd_list :
  Environ.env -> Evd.evar_map -> Constr.t -> State.s_or_d list
val codegen_auto_arguments_1 :
  Environ.env -> Evd.evar_map -> Libnames.qualid -> unit
val command_auto_arguments : Libnames.qualid list -> unit
val build_presimp :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  EConstr.types ->
  State.s_or_d list ->
  Constr.t list -> Evd.evar_map * Constr.t * EConstr.types
val gensym_ps : string -> Names.Id.t * Names.Id.t
val interp_args :
  Environ.env ->
  Evd.evar_map ->
  bool list -> Constrexpr.constr_expr list -> Evd.evar_map * EConstr.t list
val label_name_of_constant_or_constructor : Constr.t -> string
val codegen_define_instance :
  ?cfunc:string ->
  Environ.env ->
  Evd.evar_map ->
  State.instance_command ->
  Constr.t ->
  Constr.t list ->
  State.sp_instance_names option ->
  Environ.env * State.specialization_instance
val codegen_instance_command :
  State.instance_command ->
  Libnames.qualid ->
  Constrexpr.constr_expr option list ->
  State.sp_instance_names -> Environ.env * State.specialization_instance
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
val check_convertible :
  string -> Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t -> unit
val command_global_inline : Libnames.qualid list -> unit
val command_local_inline : Libnames.qualid -> Libnames.qualid list -> unit
val inline1 :
  Environ.env -> Evd.evar_map -> Names.Cpred.t -> EConstr.t -> EConstr.t
val inline :
  Environ.env -> Evd.evar_map -> Names.Cpred.t -> EConstr.t -> EConstr.t
val expand_eta_top : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val expand_eta_top1 : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val search_fix_to_expand_eta :
  Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val normalizeV : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val normalizeV1 : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val decompose_lets :
  Evd.evar_map ->
  EConstr.t ->
  (Names.Name.t Context.binder_annot * EConstr.t * EConstr.types) list *
  EConstr.t
val compose_lets :
  (Names.Name.t Context.binder_annot * EConstr.t * EConstr.types) list ->
  EConstr.t -> EConstr.t
val reduce_arg : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val debug_reduction : string -> (unit -> Pp.t) -> unit
val fv_range_rec : Environ.env -> Evd.evar_map -> int -> EConstr.t -> (int * int) option
val fv_range_array :
  Environ.env -> Evd.evar_map -> int -> EConstr.t array -> (int * int) option
val fv_range : Environ.env -> Evd.evar_map -> EConstr.t -> (int * int) option
val test_bounded_fix :
  Environ.env ->
  Evd.evar_map ->
  int ->
  (int -> EConstr.t -> EConstr.t) ->
  int array ->
  Names.Name.t Context.binder_annot array * EConstr.types array *
  EConstr.t array -> bool
val find_bounded_fix :
  Environ.env ->
  Evd.evar_map ->
  int array ->
  Names.Name.t Context.binder_annot array * EConstr.types array *
  EConstr.t array -> int option
val is_ind_type : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val reduce_exp : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val reduce_exp1 : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val reduce_app :
  Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t array -> EConstr.t
val reduce_app1 :
  Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t array -> EConstr.t
val reduce_app2 :
  Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t array -> EConstr.t
val normalize_types : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val normalize_static_arguments :
  Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val count_false_in_prefix : int -> bool list -> int
val delete_unused_let_rec :
  Environ.env ->
  Evd.evar_map -> EConstr.t -> Cgenutil.IntSet.t * (bool list -> EConstr.t)
val delete_unused_let_rec1 :
  Environ.env ->
  Evd.evar_map -> EConstr.t -> Cgenutil.IntSet.t * (bool list -> EConstr.t)
val delete_unused_let : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val first_fv_rec : Environ.env -> Evd.evar_map -> int -> EConstr.t -> int option
val first_fv : Environ.env -> Evd.evar_map -> EConstr.t -> int option
val has_fv : Environ.env -> Evd.evar_map -> EConstr.t -> bool
val replace_app :
  cfunc:string ->
  Environ.env ->
  Evd.evar_map ->
  Constr.t -> EConstr.t array -> Environ.env * EConstr.t * string
val replace :
  cfunc:string ->
  Environ.env ->
  Evd.evar_map -> EConstr.t -> Environ.env * EConstr.t * State.StringSet.t
val replace1 :
  cfunc:string ->
  Environ.env ->
  Evd.evar_map -> EConstr.t -> Environ.env * EConstr.t * State.StringSet.t
val complete_args_fun :
  Environ.env -> Evd.evar_map -> EConstr.t -> int -> EConstr.t
val complete_args_fun1 :
  Environ.env -> Evd.evar_map -> EConstr.t -> int -> EConstr.t
val complete_args_exp :
  Environ.env -> Evd.evar_map -> EConstr.t -> int array -> int -> EConstr.t
val complete_args_exp1 :
  Environ.env -> Evd.evar_map -> EConstr.t -> int array -> int -> EConstr.t
val complete_args : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val formal_argument_names :
  Environ.env ->
  Evd.evar_map -> EConstr.t -> Names.Name.t Context.binder_annot list
val rename_vars : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val specialization_time : Unix.process_times ref
val init_debug_simplification : unit -> unit
val debug_simplification :
  Environ.env -> Evd.evar_map -> string -> EConstr.t -> unit
val codegen_simplify :
  string -> Environ.env * Names.Constant.t * State.StringSet.t
val command_simplify_function : string list -> unit
val recursive_simplify :
  State.StringSet.t ref -> string list ref -> State.StringSet.elt -> unit
val command_simplify_dependencies : string list -> unit
val codegen_resolve_dependencies :
  State.code_generation list -> State.code_generation list
val command_resolve_dependencies : unit -> unit
val command_print_generation_list : State.code_generation list -> unit
val command_print_generation_map : unit -> unit
val command_deallocator_type : Constrexpr.constr_expr -> string -> unit
