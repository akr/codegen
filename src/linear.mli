module IntMap :
  sig
    type key = Int.t
    type 'a t = 'a HMap.Make(Int).t
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
        type t = HMap.Make(Int).Set.t
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
