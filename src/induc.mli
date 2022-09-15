val nf_interp_type :
  Environ.env ->
  Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * Constr.t
val command_print_inductive : Constrexpr.constr_expr list -> unit
val ind_coq_type_registered_p : Constr.t -> bool
val register_ind_type :
  Environ.env -> Evd.evar_map -> Constr.t -> string -> State.ind_config
val command_ind_type : Constrexpr.constr_expr -> string -> unit
val register_ind_match :
  Environ.env ->
  Evd.evar_map ->
  Constr.t ->
  string -> State.ind_cstr_caselabel_accessors list -> State.ind_config
val ind_is_void_type : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val c_type_is_void : State.c_typedata -> bool
val c_typename : Environ.env -> Evd.evar_map -> EConstr.types -> State.c_typedata
val case_swfunc : Environ.env -> Evd.evar_map -> EConstr.types -> string
val case_cstrlabel :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> string
val case_cstrmember :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> int -> string
val command_ind_match :
  Constrexpr.constr_expr ->
  string -> State.ind_cstr_caselabel_accessors list -> unit
