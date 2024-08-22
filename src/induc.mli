val command_print_inductive : Constrexpr.constr_expr list -> unit
val ind_coq_type_registered_p : Evd.evar_map -> EConstr.t -> bool
val lookup_ind_config : Evd.evar_map -> EConstr.types -> State.ind_config option
val register_ind_type :
  Environ.env -> Evd.evar_map -> EConstr.t -> State.c_typedata -> State.ind_config
val command_ind_type : Constrexpr.constr_expr -> State.c_typedata -> unit
val register_ind_match :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  string -> State.cstr_config list -> State.ind_config
val ind_is_void_type : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val c_type_is_void : State.c_typedata -> bool
val c_typename : Environ.env -> Evd.evar_map -> EConstr.types -> State.c_typedata
val c_closure_function_type : Environ.env -> Evd.evar_map -> EConstr.types -> State.c_typedata
val c_closure_type : State.c_typedata list -> State.c_typedata -> State.c_typedata
val case_swfunc : Environ.env -> Evd.evar_map -> EConstr.types -> string
val case_cstrlabel :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> string option
val case_cstrmember :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> int -> string option
val command_ind_match :
  Constrexpr.constr_expr ->
  string -> State.cstr_config list -> unit
val command_deallocator : Constrexpr.constr_expr -> State.dealloc_cstr_deallocator list -> unit
