val command_linear : Constrexpr.constr_expr -> unit
val command_downward : Constrexpr.constr_expr -> unit
val command_borrow_type : Constrexpr.constr_expr -> unit
val is_linear : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val linear_type_check_term : Environ.env -> Evd.evar_map -> EConstr.t -> unit
val check_function_downwardness : Environ.env -> Evd.evar_map -> string -> EConstr.t -> unit
val borrowcheck : Environ.env -> Evd.evar_map -> EConstr.t -> unit
val command_linear_check : Libnames.qualid list -> unit
val command_test_linear : Constrexpr.constr_expr -> unit
val command_test_unrestricted : Constrexpr.constr_expr -> unit
val command_linear_test : Constrexpr.constr_expr -> Constrexpr.constr_expr -> unit
val command_borrow_function : Libnames.qualid -> unit
val command_test_borrowcheck : Constrexpr.constr_expr -> unit

