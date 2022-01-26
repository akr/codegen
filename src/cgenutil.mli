module IntSet : Set.S with type elt = Int.t
val abort : 'a -> 'a
exception CodeGenError of string
val array_rev : 'a array -> 'a array
val array_map2 : ('a -> 'b -> 'c) -> 'a array -> 'b array -> 'c array
val array_map3 :
  ('a -> 'b -> 'c -> 'd) -> 'a array -> 'b array -> 'c array -> 'd array
val array_map4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a array -> 'b array -> 'c array -> 'd array -> 'e array
val array_iter2 : ('a -> 'b -> unit) -> 'a array -> 'b array -> unit
val array_iter3 :
  ('a -> 'b -> 'c -> unit) -> 'a array -> 'b array -> 'c array -> unit
val array_for_all : ('a -> bool) -> 'a array -> bool
val array_exists : ('a -> bool) -> 'a array -> bool
val array_find_map : ('a -> 'b option) -> 'a array -> 'b option
val array_find_map2 : ('a -> 'b -> 'c option) -> 'a array -> 'b array -> 'c option
val array_map_right : ('a -> 'b) -> 'a array -> 'b array
val array_fold_right_map :
  ('a -> 'b -> 'c * 'b) -> 'a array -> 'b -> 'c array * 'b
val array_find_index_opt : ('a -> bool) -> 'a array -> int option
val array_copy_set : 'a array -> int -> 'a -> 'a array
val array_find_index : ('a -> bool) -> 'a array -> int
val array_combine : 'a array -> 'b array -> ('a * 'b) array
val array_flatten : 'a array array -> 'a array
val ncons : int -> 'a -> 'a list -> 'a list
val ntimes : int -> ('a -> 'a) -> 'a -> 'a
val list_prepend_map_rev : ('a -> 'b) -> 'a list -> 'b list -> 'b list
val list_prepend_mapi_rev : (int -> 'a -> 'b) -> 'a list -> 'b list -> 'b list
val list_rev_map_append : ('a -> 'b) -> 'a list -> 'b list -> 'b list
val list_map_append : ('a -> 'b) -> 'a list -> 'b list -> 'b list
val list_find_index : ('a -> bool) -> 'a list -> int
val list_filter_map2 : ('a -> 'b -> 'c option) -> 'a list -> 'b list -> 'c list
val list_filter_none : 'a option list -> 'a list
val seq_map2 :
  ('a -> 'b -> 'c) -> 'a Seq.t -> 'b Seq.t -> unit -> 'c Seq.node
val seq_mapi : (int -> 'a -> 'b) -> 'a Seq.t -> unit -> 'b Seq.node
val seq_flat_map2 :
  ('a -> 'b -> 'c Seq.t) -> 'a Seq.t -> 'b Seq.t -> unit -> 'c Seq.node
val seq_flat_mapi :
  (int -> 'a -> 'b Seq.t) -> 'a Seq.t -> unit -> 'b Seq.node
val seq_flat_map2_i :
  (int -> 'a -> 'b -> 'c Seq.t) ->
  'a Seq.t -> 'b Seq.t -> unit -> 'c Seq.node
val concat_list_seq : 'a Seq.t list -> 'a Seq.t
val concat_array_seq : 'a Seq.t array -> 'a Seq.t
val unique_string_list : string list -> string list
val quote_coq_string : string -> string
val id_of_name : Names.Name.t -> Names.Id.t
val id_of_annotated_name : Names.Name.t Context.binder_annot -> Names.Id.t
val str_of_name : Names.Name.t -> string
val str_of_annotated_name : Names.Name.t Context.binder_annot -> string
val str_of_name_permissive : Names.Name.t -> string
val iota_ary : int -> int -> int array
val iota_list : int -> int -> int list
val array_option_exists_rec :
  ('a -> 'b option) -> 'a array -> int -> int -> 'b option
val shortcut_option_or : 'a option -> (unit -> 'a option) -> 'a option
val array_option_exists : ('a -> 'b option) -> 'a array -> 'b option
val int_pred : int -> int
val int_succ : int -> int
val merge_range :
  (int * int) option -> (int * int) option -> (int * int) option
val merge_range3 :
  (int * int) option ->
  (int * int) option -> (int * int) option -> (int * int) option
val merge_range_ary : (int * int) option array -> (int * int) option
val intset_union_ary : IntSet.t array -> IntSet.t
val ( ++ ) : Pp.t -> Pp.t -> Pp.t
val ( +++ ) : Pp.t -> Pp.t -> Pp.t
val pp_sjoin_ary : Pp.t array -> Pp.t
val pp_sjoin_list : Pp.t list -> Pp.t
val pp_sjoinmap_ary : ('a -> Pp.t) -> 'a array -> Pp.t
val pp_sjoinmap_list : ('a -> Pp.t) -> 'a list -> Pp.t
val pp_join_ary : Pp.t -> Pp.t array -> Pp.t
val pp_join_list : Pp.t -> Pp.t list -> Pp.t
val pp_joinmap_ary : Pp.t -> (Pp.t -> Pp.t) -> Pp.t array -> Pp.t
val pp_joinmap_list : Pp.t -> ('a -> Pp.t) -> 'a list -> Pp.t
val pp_prejoin_ary : Pp.t -> Pp.t array -> Pp.t
val pp_prejoin_list : Pp.t -> Pp.t list -> Pp.t
val pp_postjoin_ary : Pp.t -> Pp.t array -> Pp.t
val pp_postjoin_list : Pp.t -> Pp.t list -> Pp.t
val hbrace : Pp.t -> Pp.t
val hovbrace : Pp.t -> Pp.t
val vbrace : Pp.t -> Pp.t
val msg_info_hov : Pp.t -> unit
val msg_debug_hov : Pp.t -> unit
val user_err_hov : Pp.t -> 'a
val format_deep : Pp.t -> string
val pr_deep : Pp.t -> Pp.t
val is_monomorphic_type : Environ.env -> Evd.evar_map -> EConstr.t -> bool
val new_env_with_rels : Environ.env -> Environ.env
val decompose_lam_n_env :
  Environ.env -> Evd.evar_map -> int -> EConstr.t -> Environ.env * EConstr.t
val numargs_of_type : Environ.env -> Evd.evar_map -> EConstr.types -> int
val numargs_of_exp : Environ.env -> Evd.evar_map -> EConstr.t -> int
val out_punivs : 'a EConstr.puniverses -> 'a
val mangle_term_buf :
  Environ.env -> Evd.evar_map -> Buffer.t -> EConstr.t -> unit
val mangle_term : Environ.env -> Evd.evar_map -> EConstr.t -> string
val squeeze_white_spaces : string -> string
val c_id : string -> string
exception Invalid_as_C_identifier
val valid_c_id_p : string -> bool
val check_c_id : string -> unit
val escape_as_coq_string : string -> string
val compose_prod :
  (Names.Name.t Context.binder_annot * EConstr.t) list ->
  EConstr.t -> EConstr.t
val free_variables_rec :
  Environ.env -> Evd.evar_map -> int -> bool array -> EConstr.t -> unit
val free_variables_without :
  Environ.env -> Evd.evar_map -> int -> int -> EConstr.t -> bool array
val free_variables_index_set : Environ.env -> Evd.evar_map -> EConstr.t -> IntSet.t
val free_variables_level_set : ?without:int -> Environ.env -> Evd.evar_map -> EConstr.t -> IntSet.t
val first_fv : Environ.env -> Evd.evar_map -> EConstr.t -> int option
val has_fv : Environ.env -> Evd.evar_map -> EConstr.t -> bool
val constr_name : Evd.evar_map -> EConstr.t -> string
val constr_expr_cstr_name : Constrexpr.constr_expr -> string
val global_gensym : ?prefix:string -> unit -> string
val global_gensym_with_id : Names.Id.t -> string
