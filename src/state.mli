module ConstrMap :
  sig
    type key = Constr.t
    type 'a t = 'a HMap.Make(Constr).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val max_binding : 'a t -> key * 'a
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    module Set :
      sig
        type elt = key
        type t = HMap.Make(Constr).Set.t
        val empty : t
        val is_empty : t -> bool
        val mem : elt -> t -> bool
        val add : elt -> t -> t
        val singleton : elt -> t
        val remove : elt -> t -> t
        val union : t -> t -> t
        val inter : t -> t -> t
        val diff : t -> t -> t
        val compare : t -> t -> int
        val equal : t -> t -> bool
        val subset : t -> t -> bool
        val iter : (elt -> unit) -> t -> unit
        val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
        val for_all : (elt -> bool) -> t -> bool
        val exists : (elt -> bool) -> t -> bool
        val filter : (elt -> bool) -> t -> t
        val partition : (elt -> bool) -> t -> t * t
        val cardinal : t -> int
        val elements : t -> elt list
        val min_elt : t -> elt
        val max_elt : t -> elt
        val choose : t -> elt
        val split : elt -> t -> t * bool * t
      end
    val get : key -> 'a t -> 'a
    val set : key -> 'a -> 'a t -> 'a t
    val modify : key -> (key -> 'a -> 'a) -> 'a t -> 'a t
    val domain : 'a t -> Set.t
    val bind : (key -> 'a) -> Set.t -> 'a t
    val fold_left : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val fold_right : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val height : 'a t -> int
    val filter_range : (key -> int) -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    module Smart :
      sig
        val map : ('a -> 'a) -> 'a t -> 'a t
        val mapi : (key -> 'a -> 'a) -> 'a t -> 'a t
      end
    module Unsafe : sig val map : (key -> 'a -> key * 'b) -> 'a t -> 'b t end
    module Monad :
      functor (M : CMap.MonadS) ->
        sig
          val fold : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
          val fold_left : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
          val fold_right :
            (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
        end
  end
module StringSet :
  sig
    type elt = String.t
    type t = Set.Make(String).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val disjoint : t -> t -> bool
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val filter_map : (elt -> elt option) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val to_rev_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t
  end
val opt_debug_simplification : bool ref
val opt_debug_normalizeV : bool ref
val opt_debug_reduction : bool ref
val opt_debug_reduce_exp : bool ref
val opt_debug_reduce_app : bool ref
val opt_debug_replace : bool ref
val opt_debug_expand_eta : bool ref
val opt_debug_delete_let : bool ref
val gensym_id : int ref
type string_or_qualid =
    StrOrQid_Str of string
  | StrOrQid_Qid of Libnames.qualid
type cstr_config = {
  coq_cstr : Names.Id.t;
  c_caselabel : string;
  c_accessors : string array;
}
type ind_config = {
  coq_type : Constr.t;
  c_type : string;
  c_swfunc : string option;
  cstr_configs : cstr_config array;
}
type ind_cstr_caselabel_accessors = Names.Id.t * string * string list
type s_or_d = SorD_S | SorD_D
type id_or_underscore = Names.Id.t option
type constr_or_underscore = Constrexpr.constr_expr option
type sp_instance_names = {
  spi_cfunc_name : string option;
  spi_presimp_id : Names.Id.t option;
  spi_simplified_id : Names.Id.t option;
}
type ind_constructor = { ic_coq_cstr : Names.Id.t; ic_c_cstr : string; }
val ind_config_map : ind_config ConstrMap.t ref
type type_linearity = Linear | Unrestricted | Investigating
val type_linearity_map_empty : type_linearity ConstrMap.t
val type_linearity_map : type_linearity ConstrMap.t ref
val deallocator_cfunc_of_type : string ConstrMap.t ref
type simplified_status =
    SpNoSimplification
  | SpExpectedId of Names.Id.t
  | SpDefined of (Names.Constant.t * StringSet.t)
type instance_command =
    CodeGenFunction
  | CodeGenStaticFunction
  | CodeGenPrimitive
  | CodeGenConstant
type specialization_instance = {
  sp_static_arguments : Constr.t list;
  sp_presimp_constr : Constr.t;
  sp_simplified_status : simplified_status;
  sp_presimp : Constr.t;
  sp_cfunc_name : string;
  sp_icommand : instance_command;
}
type specialization_config = {
  sp_func : Constr.t;
  sp_is_cstr : bool;
  sp_sd_list : s_or_d list;
  sp_instance_map : specialization_instance ConstrMap.t;
}
val specialize_config_map : specialization_config ConstrMap.t ref
val gallina_instance_map :
  (specialization_config * specialization_instance) ConstrMap.t ref
val cfunc_instance_map :
  (specialization_config * specialization_instance) CString.Map.t ref
type string_or_none = string option
val current_header_filename : string option ref
val current_source_filename : string option ref
type code_generation =
    GenFunc of string
  | GenMutual of string list
  | GenPrototype of string
  | GenSnippet of string
val generation_map : code_generation list CString.Map.t ref
val codegen_add_generation : CString.Map.key -> code_generation -> unit
val codegen_add_source_generation : code_generation -> unit
val codegen_add_header_generation : code_generation -> unit
val gensym_ps_num : int ref
val specialize_global_inline : Names.Cpred.t ref
val specialize_local_inline : Names.Cpred.t Names.Cmap.t ref
type genflag = DisableDependencyResolver | DisableMutualRecursionDetection
