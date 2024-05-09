val command_print_inductive : Constrexpr.constr_expr list -> unit
val ind_coq_type_registered_p : Constr.t -> bool
val lookup_ind_config : Constr.types -> State.ind_config option
val register_ind_type :
  Environ.env -> Evd.evar_map -> Constr.t -> State.c_typedata -> State.ind_config
val command_ind_type : Constrexpr.constr_expr -> State.c_typedata -> unit
val register_ind_match :
  Environ.env ->
  Evd.evar_map ->
  Constr.t ->
  string -> State.ind_cstr_caselabel_accessors list -> State.ind_config
val ind_is_void_type : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val c_type_is_void : State.c_typedata -> bool
val c_typename : Environ.env -> Evd.evar_map -> EConstr.types -> State.c_typedata
val c_closure_function_type : Environ.env -> Evd.evar_map -> EConstr.types -> State.c_typedata
val c_closure_type : State.c_typedata list -> State.c_typedata -> State.c_typedata
val coq_type_is_void : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val case_swfunc : Environ.env -> Evd.evar_map -> EConstr.types -> string
val case_cstrlabel :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> string
val case_cstrmember :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> int -> string
val command_ind_match :
  Constrexpr.constr_expr ->
  string -> State.ind_cstr_caselabel_accessors list -> unit
val command_deallocator : Constrexpr.constr_expr -> string -> unit
