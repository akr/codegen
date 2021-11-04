module IntMap : CMap.ExtS with type key = Int.t
val whd_all : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val nf_all : Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t
val prod_appvect : Evd.evar_map -> EConstr.t -> EConstr.t array -> EConstr.t
val is_concrete_inductive_type :
  Environ.env -> Evd.evar_map -> EConstr.t -> bool
val command_linear : Constrexpr.constr_expr -> unit
val type_of_inductive_arity :
  (Declarations.regular_inductive_arity, Declarations.template_arity)
  Declarations.declaration_arity -> Constr.t
val valid_type_param :
  Environ.env -> Evd.evar_map -> Constr.rel_declaration -> bool
val hasRel : Evd.evar_map -> EConstr.t -> bool
val destProdX_rec :
  Evd.evar_map ->
  EConstr.t ->
  Names.Name.t Context.binder_annot list * EConstr.t list * EConstr.t
val destProdX :
  Evd.evar_map ->
  EConstr.t ->
  Names.Name.t Context.binder_annot array * EConstr.t array * EConstr.t
val is_linear_type : Environ.env -> Evd.evar_map -> EConstr.t -> bool
val is_linear_ind1 : Environ.env -> Evd.evar_map -> EConstr.t -> bool
val is_linear_ind : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val is_linear : Environ.env -> Evd.evar_map -> EConstr.types -> bool
val check_type_linearity :
  Environ.env -> Evd.evar_map -> EConstr.types -> unit
val ntimes : int -> ('a -> 'a) -> 'a -> 'a
val with_local_var :
  Environ.env ->
  Evd.evar_map ->
  EConstr.rel_declaration ->
  bool list ->
  int -> (Environ.env -> bool list -> int -> int IntMap.t) -> int IntMap.t
val merge_count : int IntMap.t -> int IntMap.t -> int IntMap.t
val linearcheck_function :
  Environ.env -> Evd.evar_map -> bool list -> EConstr.t -> unit
val linearcheck_function_rec :
  Environ.env ->
  Evd.evar_map -> bool list -> int -> EConstr.t -> int IntMap.t
val linearcheck_exp :
  Environ.env ->
  Evd.evar_map -> bool list -> int -> EConstr.t -> int -> Int.t IntMap.t
val linear_type_check_term : Environ.env -> Evd.evar_map -> EConstr.t -> unit
val linear_type_check_single : Libnames.qualid -> unit
val command_linear_check : Libnames.qualid list -> unit
val command_test_linear : Constrexpr.constr_expr -> unit
val command_test_unrestricted : Constrexpr.constr_expr -> unit
val command_linear_test :
  Constrexpr.constr_expr -> Constrexpr.constr_expr -> unit
