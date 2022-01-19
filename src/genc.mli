type fixterm_t = {
  fixterm_term_id : Names.Id.t;
  fixterm_tail_position : bool;
  fixterm_term_env : Environ.env;
  fixterm_term : EConstr.t;
  fixterm_inlinable : bool;
}
type fixfunc_t = {
  fixfunc_func_id : Names.Id.t;
  fixfunc_term_id : Names.Id.t;
  fixfunc_term_env : Environ.env;
  fixfunc_func : EConstr.t;
  fixfunc_inlinable : bool;
  fixfunc_used_as_call : bool;
  fixfunc_used_as_goto : bool;
  fixfunc_formal_arguments : (string * string option) list;
  fixfunc_return_type : string option;
  fixfunc_top_call : string option;
  fixfunc_c_name : string;
  fixfunc_outer_variables : (string * string) list;
}
type fixfunc_table = (Names.Id.t, fixfunc_t) Hashtbl.t
val show_fixfunc_table : Environ.env -> Evd.evar_map -> fixfunc_table -> unit
val c_args_and_ret_type :
  Environ.env -> Evd.evar_map -> EConstr.t -> (string * string option) list * string option
val disjoint_id_map_union :
  'a Names.Id.Map.t -> 'a Names.Id.Map.t -> 'a Names.Id.Map.t
val detect_inlinable_fixterm_rec :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  int -> bool Names.Id.Map.t * Cgenutil.IntSet.t * Cgenutil.IntSet.t
val detect_inlinable_fixterm_rec1 :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  int -> bool Names.Id.Map.t * Cgenutil.IntSet.t * Cgenutil.IntSet.t
val detect_inlinable_fixterm :
  Environ.env -> Evd.evar_map -> EConstr.t -> int -> bool Names.Id.Map.t
val collect_fix_usage_rec :
  inlinable_fixterms:bool Names.Id.Map.t ->
  Environ.env ->
  Evd.evar_map ->
  bool ->
  EConstr.t ->
  int ->
  used_as_call:bool ref list ->
  used_as_goto:bool ref list -> fixterm_t Seq.t * fixfunc_t Seq.t
val collect_fix_usage_rec1 :
  inlinable_fixterms:bool Names.Id.Map.t ->
  Environ.env ->
  Evd.evar_map ->
  bool ->
  EConstr.t ->
  int ->
  used_as_call:bool ref list ->
  used_as_goto:bool ref list -> fixterm_t Seq.t * fixfunc_t Seq.t
val make_fixfunc_table : fixfunc_t list -> fixfunc_table
val collect_fix_usage :
  inlinable_fixterms:bool Names.Id.Map.t ->
  Environ.env -> Evd.evar_map -> EConstr.t -> fixterm_t list * fixfunc_table
val fixfunc_initialize_top_calls :
  Environ.env ->
  Evd.evar_map ->
  string ->
  EConstr.t ->
  (bool * string * int * Names.Id.t) list ->
  fixfunc_tbl:fixfunc_table -> unit
val fixfunc_initialize_c_names : fixfunc_table -> unit
val fixterm_free_variables_rec :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  result:(Names.Id.t, Names.Id.Set.t) Hashtbl.t -> Names.Id.Set.t
val fixterm_free_variables :
  Environ.env ->
  Evd.evar_map -> EConstr.t -> (Names.Id.t, Names.Id.Set.t) Hashtbl.t
val pr_outer_variable : (string * string) list -> Pp.t
val check_eq_outer_variables :
  (string * string) list -> (string * string) list -> unit
val compute_naive_outer_variables :
  fixfunc_tbl:fixfunc_table ->
  Environ.env -> Evd.evar_map -> (string * string) list
val compute_precise_outer_variables :
  fixfunc_tbl:fixfunc_table ->
  Environ.env ->
  Evd.evar_map ->
  (Names.Id.t, Names.Id.Set.t) Hashtbl.t ->
  (Names.Id.t, Names.Id.Set.t) Hashtbl.t
val fixfunc_initialize_outer_variables :
  Environ.env ->
  Evd.evar_map -> EConstr.t -> fixfunc_tbl:fixfunc_table -> unit
val collect_fix_info :
  Environ.env ->
  Evd.evar_map ->
  string ->
  EConstr.t ->
  (bool * string * int * Names.Id.t) list -> fixterm_t list * fixfunc_table
val local_gensym_id : int ref option ref
val local_gensym_with : (unit -> 'a) -> 'a
val local_gensym : unit -> string
val local_vars : (string * string) list ref option ref
val local_vars_with : (unit -> 'a) -> (string * string) list * 'a
val add_local_var : string -> string -> unit
val carg_of_garg : Environ.env -> int -> string
val gen_assignment : Pp.t -> Pp.t -> Pp.t
val gen_return : Pp.t -> Pp.t
val gen_void_return : string -> Pp.t -> Pp.t
val gen_funcall : string -> string array -> Pp.t
val gen_app_const_construct :
  Environ.env -> Evd.evar_map -> EConstr.t -> string array -> Pp.t
val gen_switch_without_break : Pp.t -> (string * Pp.t) array -> Pp.t
val gen_switch_with_break : Pp.t -> (string * Pp.t) array -> Pp.t
val gen_match :
  Names.Id.Set.t ->
  (Pp.t -> (string * Pp.t) array -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> EConstr.t -> string option list -> Pp.t) ->
  Environ.env ->
  Evd.evar_map ->
  Constr.case_info ->
  EConstr.t -> EConstr.t -> EConstr.t array -> string option list -> Pp.t
val gen_proj :
  Environ.env -> Evd.evar_map -> Names.Projection.t -> EConstr.t -> Pp.t
val gen_parallel_assignment : (string * string * string) array -> Pp.t
val gen_function_header :
  bool -> string option -> string -> (string * string) list -> Pp.t
val fixfuncs_for_internal_entfuncs : fixfunc_table -> fixfunc_t list
val detect_fixterms_for_bodies :
  fixterms:fixterm_t list ->
  fixfunc_tbl:fixfunc_table ->
  ((string * string) list * Environ.env * EConstr.t) list
val labels_for_stacked_fixfuncs :
  fixfunc_tbl:fixfunc_table ->
  primary_cfunc:string -> string list -> string list
val gen_func_single :
  fixterms:fixterm_t list ->
  fixfunc_tbl:fixfunc_table ->
  static:bool ->
  primary_cfunc:string ->
  Environ.env ->
  Evd.evar_map -> EConstr.t -> string option -> Names.Id.Set.t -> Pp.t
val gen_func_multi :
  fixterms:fixterm_t list ->
  fixfunc_tbl:fixfunc_table ->
  static:bool ->
  primary_cfunc:string ->
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  (string * string) list ->
  string option ->
  Names.Id.Set.t ->
  fixfunc_t list -> (bool * string * int * Names.Id.t) list -> Pp.t
val used_variables :
  Environ.env -> Evd.evar_map -> EConstr.t -> Names.Id.Set.t
val is_static_function_icommand : State.instance_command -> bool
val make_simplified_for_cfunc : string -> bool * Constr.types * Constr.t
val gen_func_sub : string -> (bool * string * int * Names.Id.t) list -> Pp.t
val gen_function :
  ?sibling_entfuncs:(bool * string * int * Names.Id.t) list -> string -> Pp.t
val entfunc_of_sibling_cfunc :
  string -> (bool * string * int * Names.Id.t) option
val gen_mutual : string list -> Pp.t
val gen_prototype : string -> Pp.t
val common_key_for_siblings : Constr.t -> (int * Constr.t) option
val codegen_detect_siblings :
  State.code_generation list -> State.code_generation list
val gen_pp_iter : (Pp.t -> unit) -> State.code_generation list -> unit
val complete_gen_map :
  State.genflag list ->
  State.code_generation list CString.Map.t ->
  State.code_generation list CString.Map.t
val command_gen : State.string_or_qualid list -> unit
val gen_file : string -> State.code_generation list -> unit
val command_generate_file : State.genflag list -> unit
val command_generate_test : State.genflag list -> unit
