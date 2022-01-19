val nf_interp_type :
  Environ.env ->
  Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * Constr.t
val codegen_print_inductive_type :
  Environ.env -> Evd.evar_map -> State.ind_config -> unit
val pr_inductive_match :
  Environ.env -> Evd.evar_map -> State.ind_config -> Pp.t
val codegen_print_inductive_match :
  Environ.env -> Evd.evar_map -> State.ind_config -> unit
val codegen_print_inductive1 :
  Environ.env -> Evd.evar_map -> State.ind_config -> unit
val command_print_inductive : Constrexpr.constr_expr list -> unit
val get_ind_coq_type :
  Environ.env ->
  Constr.t ->
  Names.MutInd.t * Declarations.mutual_inductive_body * int *
  Declarations.one_inductive_body * Constr.constr list
val check_ind_coq_type : Environ.env -> Evd.evar_map -> Constr.t -> unit
val ind_coq_type_registered_p : Constr.t -> bool
val check_ind_coq_type_not_registered : Constr.t -> unit
val register_ind_type :
  Environ.env -> Evd.evar_map -> Constr.t -> string -> State.ind_config
val generate_ind_config :
  Environ.env -> Evd.evar_map -> EConstr.types -> State.ind_config
val lookup_ind_config : Constr.types -> State.ind_config option
val get_ind_config :
  Environ.env -> Evd.evar_map -> EConstr.types -> State.ind_config
val command_ind_type : Constrexpr.constr_expr -> string -> unit
val register_ind_match :
  Environ.env ->
  Evd.evar_map ->
  Constr.t ->
  string -> State.ind_cstr_caselabel_accessors list -> State.ind_config
val generate_ind_match :
  Environ.env -> Evd.evar_map -> EConstr.types -> State.ind_config
val ind_is_void_type : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val c_typename : Environ.env -> Evd.evar_map -> EConstr.types -> string option
val case_swfunc : Environ.env -> Evd.evar_map -> EConstr.types -> string
val case_cstrlabel :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> string
val case_cstrmember :
  Environ.env -> Evd.evar_map -> EConstr.types -> int -> int -> string
val command_ind_match :
  Constrexpr.constr_expr ->
  string -> State.ind_cstr_caselabel_accessors list -> unit
