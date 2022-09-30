val command_linear : Constrexpr.constr_expr -> unit
val command_downward : Constrexpr.constr_expr -> unit
val command_borrow_type : Constrexpr.constr_expr -> unit
val component_types : Environ.env -> Evd.evar_map -> EConstr.types -> State.ConstrSet.t option
val is_linear : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val downwardcheck : Environ.env -> Evd.evar_map -> string -> EConstr.t -> unit
val borrowcheck : Environ.env -> Evd.evar_map -> EConstr.t -> unit
val command_test_linear : Constrexpr.constr_expr -> unit
val command_test_unrestricted : Constrexpr.constr_expr -> unit
val command_borrow_function : Libnames.qualid -> unit
val command_test_borrowcheck : Constrexpr.constr_expr -> unit

