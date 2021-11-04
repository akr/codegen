val ind_recursive_p : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val ind_mutual_p : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val check_ind_id_conflict : Declarations.mutual_inductive_body -> unit
val generate_indimp_names :
  Environ.env ->
  Evd.evar_map ->
  EConstr.types ->
  Names.MutInd.t * EConstr.t array *
  (string * string * string *
   (Names.Id.t * string * string * string * string *
    (string * string * string) list)
   list)
  list
val generate_indimp_immediate :
  Environ.env -> Evd.evar_map -> EConstr.types -> unit
val generate_indimp_heap :
  Environ.env -> Evd.evar_map -> EConstr.types -> unit
val command_indimp : Constrexpr.constr_expr -> unit
