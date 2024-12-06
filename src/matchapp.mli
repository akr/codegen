type verification_step = {
  vstep_lhs_fun : EConstr.t;
  vstep_rhs_fun : EConstr.t;
  vstep_goal : EConstr.types;
  vstep_proof : EConstr.t;
}

val verify_transformation : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t -> (Evd.evar_map * verification_step option)
val combine_verification_steps : Environ.env -> Evd.evar_map -> EConstr.t -> verification_step list -> EConstr.t -> Evd.evar_map * EConstr.types * EConstr.t
val simplify_matchapp : Environ.env -> Evd.evar_map -> EConstr.t -> (Evd.evar_map * EConstr.t * verification_step option)
