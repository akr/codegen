open Names
open GlobRef
open CErrors
open Constr
open EConstr

open Cgenutil
open State

module IntMap = HMap.Make(Int)

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = Reductionops.nf_all env sigma term

let rec is_concrete_inductive_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool =
  let termty = Retyping.get_type_of env sigma term in
  (if isSort sigma (whd_all env sigma termty) then
    match EConstr.kind sigma term with
    | Ind _ -> true
    | App (f, argsary) ->
        isInd sigma f &&
        Array.for_all (is_concrete_inductive_type env sigma) argsary
    | _ -> false
  else
    false) (* "list" is not "concrete" inductive type because it has concrete parameter *)

let add_linear_type ?(msg_new:bool=false) ?(msg_already:bool=false)
    (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : unit =
  let ty = nf_all env sigma ty in
  (if not (is_concrete_inductive_type env sigma ty) then
    user_err (Pp.str "[codegen] linear: concrete inductive type expected:" +++ Printer.pr_econstr_env env sigma ty));
  if ConstrSet.mem (EConstr.to_constr sigma ty) !linearity_type_set then
    (if msg_already then
      Feedback.msg_info (Pp.str "[codegen] linearity already defined:" +++ Printer.pr_econstr_env env sigma ty))
  else
    (linearity_type_set := ConstrSet.add (EConstr.to_constr sigma ty) !linearity_type_set;
    if msg_new then
      Feedback.msg_info (Pp.str "[codegen] linear type registered:" +++ Printer.pr_econstr_env env sigma ty))

let command_linear (ty : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty2) = Constrintern.interp_constr_evars env sigma ty in
  add_linear_type ~msg_new:true ~msg_already:true env sigma ty2

let command_downward (ty : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty2) = Constrintern.interp_constr_evars env sigma ty in
  let ty4 = nf_all env sigma ty2 in
  (if not (is_concrete_inductive_type env sigma ty4) then
    user_err (Pp.str "[codegen] downward: concrete inductive type expected:" +++ Printer.pr_econstr_env env sigma ty4));
  (if ConstrSet.mem (EConstr.to_constr sigma ty4) !downward_type_set then
    user_err (Pp.str "[codegen] downwardness already defined:" +++ Printer.pr_econstr_env env sigma ty4));
  downward_type_set := ConstrSet.add (EConstr.to_constr sigma ty4) !downward_type_set;
  Feedback.msg_info (Pp.str "[codegen] downward type registered:" +++ Printer.pr_econstr_env env sigma ty2)

let valid_type_param (env : Environ.env) (sigma : Evd.evar_map) (decl : Constr.rel_declaration) : bool =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> isSort sigma (whd_all env sigma (EConstr.of_constr ty))
  | Context.Rel.Declaration.LocalDef _ -> false

let make_ind_ary (env : Environ.env) (sigma : Evd.evar_map) (mutind : MutInd.t) (u : EInstance.t) : Declarations.mutual_inductive_body * EConstr.t array =
  let open Declarations in
  let mind_body = Environ.lookup_mind mutind env in
  let pp_all_ind_names () =
    pp_sjoinmap_ary
      (fun oind_body -> Id.print oind_body.mind_typename)
      mind_body.mind_packets
  in
  let pp_indexed_ind_names () =
    pp_sjoinmap_ary
      (fun oind_body ->
        if oind_body.mind_nrealargs <> 0 then
          Id.print oind_body.mind_typename
        else
          Pp.mt ())
      mind_body.mind_packets
  in
  if mind_body.mind_nparams <> mind_body.mind_nparams_rec then
    user_err (Pp.str "[codegen] inductive type has non-uniform parameters:" +++ pp_all_ind_names ());
  if (Array.exists (fun oind_body -> oind_body.mind_nrealargs <> 0) mind_body.mind_packets) then
    user_err (Pp.str "[codegen] indexed types not supported:" +++ pp_indexed_ind_names ());
  if not (List.for_all (valid_type_param env sigma) mind_body.mind_params_ctxt) then
    user_err (Pp.str "[codegen] inductive type has non-type parameter:" +++ pp_all_ind_names ());
  let ind_ary = Array.map (fun j -> EConstr.mkIndU ((mutind, j), u))
    (iota_ary 0 mind_body.mind_ntypes) in
  (mind_body,ind_ary)

let mutual_inductive_types (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : EConstr.t array =
  let (ty_f, ty_args) = decompose_appvect sigma ty in
  let ((mutind,i), u) =
    match EConstr.kind sigma ty_f with
    | Ind (ind,u) -> ind, u
    | _ -> user_err_hov (Pp.str "[codegen:mutual_inductive_types] inductive type expected:" +++
                         Printer.pr_econstr_env env sigma ty)
  in
  let (_,ind_ary) = make_ind_ary env sigma mutind u in
  Array.map (fun ind -> nf_all env sigma (mkApp (ind, ty_args))) ind_ary

let ind_cstrarg_iter (env : Environ.env) (sigma : Evd.evar_map) (ind : inductive) (u : EInstance.t) (params : EConstr.t array)
  (f : (*typename*)Id.t -> (*consname*)Id.t -> (*argtype*)EConstr.types -> unit) : unit =
  let open Declarations in
  let open Context.Rel.Declaration in
  let (mutind, i) = ind in
  let (mind_body,ind_ary) = make_ind_ary env sigma mutind u in
  (*msg_debug_hov (Pp.str "[codegen:ind_cstrarg_iter] mutind=[" ++
    pp_sjoinmap_ary (fun oind_body -> Id.print oind_body.mind_typename) mind_body.mind_packets ++ Pp.str "]" +++
    Pp.str "params=[" ++
    pp_sjoinmap_ary (fun p -> Printer.pr_econstr_env env sigma p) params ++ Pp.str "]");*)
  let oind_body = mind_body.mind_packets.(i) in
  let ind_id = oind_body.mind_typename in
  Array.iter2
    (fun cons_id nf_lc ->
      (* ctx is a list of innermost-first binder decls of the constructor (including inductive type parameters) *)
      let (ctx, t) = nf_lc in
      (*msg_debug_hov (Pp.str "[codegen:ind_cstrarg_iter] reduce" +++
                     Pp.str "typename=" ++ Id.print ind_id +++
                     Pp.str "consname=" ++ Id.print cons_id +++
                     Pp.str "nf_lc_ctx=[" ++ Printer.pr_rel_context env sigma ctx ++ Pp.str "]" +++
                     Pp.str "nf_lc_t=" ++ Printer.pr_constr_env (Environ.push_rel_context ctx env) sigma t);*)
      let rev_ctx = array_rev (Array.of_list ctx) in
      let env2 = ref env in
      let params = ref (Array.to_list params) in
      let h = Array.length rev_ctx in
      for j = 0 to h - 1 do
        (* msg_debug_hov (Pp.str "[codegen:ind_cstrarg_iter] j=" ++ Pp.int j +++ Printer.pr_rel_context_of !env2 sigma); *)
        let decl = rev_ctx.(j) in
        match decl with
        | LocalDef (x,e,ty) ->
            env2 := Environ.push_rel decl !env2
        | LocalAssum (x,ty) ->
            let ty = EConstr.of_constr ty in
            (match !params with
            | param :: rest ->
                params := rest;
                env2 := env_push_def !env2 x param ty
            | [] ->
                let ty' = nf_all !env2 sigma ty in
                (*msg_debug_hov (Pp.str "[codegen:ind_cstrarg_iter] normalize_argtype" +++ Printer.pr_econstr_env !env2 sigma ty +++ Pp.str "to" +++ Printer.pr_econstr_env !env2 sigma ty');*)
                if not (Vars.closed0 sigma ty') then
                  user_err_hov (Pp.str "[codegen] dependent constructor argument:" +++ Id.print ind_id +++ Id.print cons_id +++ Printer.pr_econstr_env !env2 sigma ty');
                f ind_id cons_id ty';
                env2 := Environ.push_rel decl !env2)
      done)
    oind_body.mind_consnames oind_body.mind_nf_lc

let rec traverse_constructor_argument_types_acc (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) (ty_set_ref : ConstrSet.t ref) (has_func_ref : bool ref) (has_sort_ref : bool ref) : unit =
  if ConstrSet.mem (EConstr.to_constr sigma ty) !ty_set_ref then
    ()
  else
    (let (ty_f,ty_args) = decompose_appvect sigma ty in
    match EConstr.kind sigma ty_f with
    | Sort _ -> has_sort_ref := true
    | Prod _ -> has_func_ref := true
    | Ind (ind, u) ->
        ty_set_ref := (ConstrSet.add (EConstr.to_constr sigma ty) !ty_set_ref);
        ind_cstrarg_iter env sigma ind u ty_args
          (fun ind_id cons_id argty ->
            traverse_constructor_argument_types_acc env sigma argty ty_set_ref has_func_ref has_sort_ref)
    | _ -> user_err (Pp.str "[codegen:component_types] unexpected type:" +++ Printer.pr_econstr_env env sigma ty))

let traverse_constructor_argument_types (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : (ConstrSet.t * bool * bool) =
  let ty_set_ref = ref (ConstrSet.empty) in
  let has_func_ref = ref false in
  let has_sort_ref = ref false in
  traverse_constructor_argument_types_acc env sigma ty ty_set_ref has_func_ref has_sort_ref;
  (!ty_set_ref, !has_func_ref, !has_sort_ref)

let component_types (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : ConstrSet.t option =
  let (ty_set, has_func, has_sort) = traverse_constructor_argument_types env sigma ty in
  if has_func || has_sort then
    None
  else
    Some (ty_set)

(*
  is_linear_type env sigma ty returns true if
  ty is code generatable and it is linear.
  It returns false otherwise.

  - code-generatable means that the type is inductive type or function type.
    other types, such as sorts, are not code-generatable.
  - linear type is
    - a inductive type which is registered with CodeGen Linear, or
    - a inductive type which has (possibly indirectly) have a component which type is linear.
  - function type is always unrestricted.
*)
let is_linear_type (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  let (ty_set, has_func, has_sort) = traverse_constructor_argument_types env sigma ty in
  if has_sort then
    false (* not code-generatable *)
  else
    not (ConstrSet.disjoint ty_set !linearity_type_set)

let is_linear (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (str "[codegen] is_linear:argument:" ++ Printer.pr_econstr_env env sigma ty);*)
  let sort = Retyping.get_type_of env sigma ty in
  if not (isSort sigma (whd_all env sigma sort)) then
    user_err (Pp.str "[codegen] not a type:" +++ Printer.pr_econstr_env env sigma ty +++ Pp.str ":" +++ Printer.pr_econstr_env env sigma sort);
  let ty2 = nf_all env sigma ty in
  (if not (Vars.closed0 sigma ty2) then
    user_err_hov (Pp.str "[codegen:is_linear] free variable in type:" +++ Printer.pr_econstr_env env sigma ty2));
  is_linear_type env sigma ty2

(*
  is_downward_type env sigma ty returns true if
  ty is code generatable and it is DownwardOnly.
  It returns false otherwise.

  - code-generatable means that the type is inductive type or function type.
    other types, such as sorts, are not code-generatable.
  - downward type is
    - a inductive type which is registered with CodeGen Downward, or
    - a inductive type which has (possibly indirectly) have a component which type is DownwardOnly.
  - function type is always DownwardOnly.
*)
let is_downward_type (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  let (ty_set, has_func, has_sort) = traverse_constructor_argument_types env sigma ty in
  if has_sort then
    false (* not code-generatable *)
  else if has_func then
    true
  else
    not (ConstrSet.disjoint ty_set !downward_type_set)

let is_downward (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (Pp.str "[codegen] is_downward:argument:" ++ Printer.pr_econstr_env env sigma ty);*)
  let sort = Retyping.get_type_of env sigma ty in
  if not (isSort sigma (whd_all env sigma sort)) then
    user_err (Pp.str "[codegen] not a type:" +++ Printer.pr_econstr_env env sigma ty +++ Pp.str ":" +++ Printer.pr_econstr_env env sigma sort);
  let ty2 = nf_all env sigma ty in
  (if not (Vars.closed0 sigma ty2) then
    user_err_hov (Pp.str "[codegen:is_downward] free variable in type:" +++ Printer.pr_econstr_env env sigma ty2));
  is_downward_type env sigma ty2

(*let check_type_downwardness (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : unit =
  ignore (is_downward env sigma ty)*)

let rec check_fix_downwardness (env : Environ.env) (sigma : Evd.evar_map) (cfunc : string) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:check_fix_downwardness] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | Rel _ | Const _ | Construct _ -> ()
  | Lambda (x, ty, b) ->
      let env2 = env_push_assum env x ty in
      check_fix_downwardness env2 sigma cfunc b
  | LetIn (x, e, ty, b) ->
      check_fix_downwardness env sigma cfunc e;
      let env2 = env_push_def env x e ty in
      check_fix_downwardness env2 sigma cfunc b
  | App (f, argsary) ->
      check_fix_downwardness env sigma cfunc f;
      Array.iter (check_fix_downwardness env sigma cfunc) argsary
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      check_fix_downwardness env sigma cfunc item;
      Array.iter2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          check_fix_downwardness env2 sigma cfunc body)
        bl bl0
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      Array.iter2
        (fun n ty ->
          let (_, retty) = decompose_prod sigma ty in
          if is_downward env sigma retty then
            user_err (Pp.str "[codegen] fixpoint function returns downward value:" +++ Id.print (id_of_name (Context.binder_name n)) +++ Pp.str "in" +++ Pp.str cfunc))
        nary tary;
      let env2 = EConstr.push_rec_types prec env in
      Array.iter (check_fix_downwardness env2 sigma cfunc) fary
  | Proj (proj, sr, expr) ->
      check_fix_downwardness env sigma cfunc expr

let downwardcheck (env : Environ.env) (sigma : Evd.evar_map) (cfunc : string) (term : EConstr.t) : unit =
  let termty = nf_all env sigma (Retyping.get_type_of env sigma term) in
  let (argtys, retty) = EConstr.decompose_prod sigma termty in
  if is_downward env sigma retty then
    user_err (Pp.str "[codegen] function returns downward value:" +++ Pp.str cfunc);
  check_fix_downwardness env sigma cfunc term

let pr_deBruijn_level (env : Environ.env) (l : int) : Pp.t =
  let i = Environ.nb_rel env - l in
  if 0 < i && i <= Environ.nb_rel env then
    match Context.Rel.Declaration.get_name (Environ.lookup_rel i env) with
    | Name.Anonymous -> Pp.str "_"
    | Name.Name id -> Id.print id
  else
    Pp.str "<INVALIDREL:" ++ Pp.int i ++ Pp.str ">"

let pr_deBruijn_level_set (env : Environ.env) (vs : IntSet.t) : Pp.t =
  IntSet.fold
    (fun l pp -> pr_deBruijn_level env l +++ pp)
    vs
    (Pp.mt ())

let count_intlist (l : int list) : int IntMap.t =
  List.fold_left
    (fun m i ->
      IntMap.update i
        (fun opt ->
          match opt with
          | None -> Some 1
          | Some n -> Some (n+1))
        m)
    IntMap.empty
    l

let intlist_duplicates (l : int list) : int list =
  let counts = count_intlist l in
  List.filter_map
    (fun (i,n) -> if 1 < n then Some i else None)
    (IntMap.bindings counts)

(*
  let rec borrowcheck_function (env : Environ.env) (sigma : Evd.evar_map)
      (lvar_env : int option list) (borrow_env : borrow_t list)
      (term : EConstr.t) : borrow_t = ...

  and borrowcheck_expression (env : Environ.env) (sigma : Evd.evar_map)
      (lvar_env : int option list) (borrow_env : borrow_t list)
      (term : EConstr.t) (term_ty : EConstr.types) : (IntSet.t * borrow_t * borrow_t) = ...

  bresult = borrowcheck_function env sigma lvar_env borrow_env term
  (lconsumed, bused, bresult) = borrowcheck_expression env sigma lvar_env borrow_env term term_ty

  borrowcheck_function verifies `term` as a function.
  It returns bresult that is a set of free borrowed variables in term.

  borrowcheck_expression verifies `term` as an expression.
  It returns (lconsumed,bused,bresult).

  term : term to evaluate

  They raises an error for invalid borrowing.

  They verify that a borrowed variable, y in following example, is only usable
  before the original linear variable, x, is consumed.

  fun (x : linear_type) =>
  let y := borrow x in
  let z1 := ... in      (* y is usable *)
  let _ := dealloc x in
  let z2 := ... in      (* y is not usable *)
  ...

  They uses de Bruijn's level (Environ.nb_rel - de_Bruijn_index) to represent linear variables.

  lconsumed is the set of free linear variables used.
  bused is the set of free linear variables used with borrowing.
  bresult is the set of free linear variables which may be contained in the result value by borrowing.

  bused and bresult are represented as borrow_t = IntSet.t ConstrMap.t.
  It is a map from a type to set of linear variables.

  For example, if the type of `borrow x` is A and
  A doesn't contain borrow types except A,
  bresult (and bused) of `borrow x` is `{A => {x}}`.
  It means the evaluation of `borrow x` needs `x` is live (not deallocated yet) and
  the result of `borrow x` contains values of type A which is only usable while `x` is live.

  lvar_env : int option list
    This represents original linear variables.
    Basically, each linear variables are distinct but
    there is one exception in codegen.
    codegen treats `y1` and `y2` in `match x with ... | C => fun y2 => ... | ... end y1`
    same variable.
    So we maintain a map to normalize such variables (y2 to y1 in this example).
    We represent such map using `int option list` where the length of list is same as
    Environ.nb_rel.
    The list is indexed by de Bruijn index. (innermost variable is first)
    Each element is `int option`.
    `None` means the variable is not linear.
    `Some l` means the variable is linear and
    the original linear variable is represented as de Bruijn level `l`.

  borrow_env :
    This represents borrowed values used in variables.
    It is a list that length is same as Environ.nb_rel.
    It is indexed by de Bruijn index. (innermost variable is first)
    The type of each element is `borrow_t`.
    If i'th element (base-1) is `{A => {x}}`,
    i'th variable may contains values of type `A` borrowed from `x`.

  Constraint: bresult is a subset of bused - lconsumed
  *)

type borrow_t = IntSet.t ConstrMap.t

let pr_borrow (env : Environ.env) (sigma : Evd.evar_map) (brw : borrow_t) =
  Pp.str "{" ++
  pp_joinmap_list (Pp.str "," ++ Pp.spc ())
    (fun (ty,set) -> Printer.pr_constr_env env sigma ty +++ Pp.str "in" +++ pr_deBruijn_level_set env set)
    (ConstrMap.bindings brw) ++
  Pp.str "}"

let borrow_of_list (pairs : (Constr.t*int) list) : borrow_t =
  List.fold_left
    (fun m (ty,l) ->
      ConstrMap.update ty
        (fun opt ->
          match opt with
          | None -> Some (IntSet.singleton l)
          | Some set -> Some (IntSet.add l set))
        m)
    ConstrMap.empty
    pairs

(*
let borrow_of_array (pairs : (Constr.t*int) array) : borrow_t =
  borrow_of_list (Array.to_list pairs)

let borrow_singleton (ty : Constr.t) (l : int) : borrow_t =
  ConstrMap.singleton ty (IntSet.singleton l)
*)

let borrow_union (brw1 : borrow_t) (brw2 : borrow_t) : borrow_t =
  ConstrMap.merge
    (fun ty opt1 opt2 ->
      match opt1, opt2 with
      | Some set1, Some set2 -> Some (IntSet.union set1 set2)
      | Some set1, None -> Some set1
      | None, Some set2 -> Some set2
      | None, None -> None)
    brw1 brw2

let borrow_union_ary (brws : borrow_t array) : borrow_t =
  Array.fold_left borrow_union ConstrMap.empty brws

let constrmap_filter_map (f : ConstrMap.key -> 'a -> 'b option) (m : 'a ConstrMap.t) : 'b ConstrMap.t =
  List.fold_left
    (fun m (k,b) -> ConstrMap.add k b m)
    ConstrMap.empty
    (List.filter_map
      (fun (k,a) ->
        match f k a with
        | Some b -> Some (k,b)
        | None -> None)
      (ConstrMap.bindings m))

let borrow_filter_lvar (pred : int -> bool) (brw : borrow_t) : borrow_t =
  constrmap_filter_map
    (fun ty set ->
      let set' = IntSet.filter pred set in
      if IntSet.is_empty set' then
        None
      else
        Some set')
    brw

let borrow_remove (l : int) (brw : borrow_t) : borrow_t =
  constrmap_filter_map
    (fun ty set ->
      let set' = IntSet.remove l set in
      if IntSet.is_empty set' then
        None
      else
        Some set')
    brw

let lvariables_of_borrow (brw : borrow_t) : IntSet.t =
  ConstrMap.fold
    (fun ty set set0 -> IntSet.union set set0)
    brw
    IntSet.empty

    (*
let borrow_equal (brw1 : borrow_t) (brw2 : borrow_t) : bool =
  ConstrMap.cardinal brw1 = ConstrMap.cardinal brw2 &&
  ConstrMap.for_all
    (fun ty set1 -> match ConstrMap.find_opt ty brw2 with None -> false | Some set2 -> IntSet.equal set1 set2)
    brw1
    *)

    (*
let borrow_disjoint (brw1 : borrow_t) (brw2 : borrow_t) : bool =
  IntSet.disjoint (lvariables_of_borrow brw1) (lvariables_of_borrow brw2)
  *)

let borrow_max_elt (brw : borrow_t) : int =
  IntSet.max_elt (lvariables_of_borrow brw)

let is_borrow_type (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : bool =
  let ty = nf_all env sigma ty in
  (if not (Vars.closed0 sigma ty) then
    user_err_hov (Pp.str "[codegen:is_borrow_type] free variable in type:" +++ Printer.pr_econstr_env env sigma ty));
  ConstrSet.mem (EConstr.to_constr sigma ty) !borrow_type_set

let filter_borrow env sigma term_ty bresult =
  match component_types env sigma term_ty with
  | None -> bresult
  | Some tyset ->
      ConstrMap.filter
        (fun ty _ ->
          ConstrSet.mem ty tyset)
        bresult

let rec borrowcheck_function (env : Environ.env) (sigma : Evd.evar_map)
    (lvar_env : int option list) (borrow_env : borrow_t list)
    (term : EConstr.t) : borrow_t =
  if !opt_debug_borrowcheck then
    msg_debug_hov (Pp.str "[codegen:borrowcheck_function] start:" +++ Printer.pr_econstr_env env sigma term);
  let ret = borrowcheck_function1 env sigma lvar_env borrow_env term in
  if !opt_debug_borrowcheck then
    msg_debug_hov (Pp.str "[codegen:borrowcheck_function] retutrn:" +++
      Pp.str "bresult=" ++ pr_borrow env sigma ret +++
      Printer.pr_econstr_env env sigma term);
  ret
and borrowcheck_function1 (env : Environ.env) (sigma : Evd.evar_map)
    (lvar_env : int option list) (borrow_env : borrow_t list)
    (term : EConstr.t) : borrow_t =
  match EConstr.kind sigma term with
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let h = Array.length fary in
      let lvar_env2 = CList.addn h None lvar_env in
      (* The fix-bounded functions may access borrowed values via free variables.
         So this assumption of borrow_env2, fix-bounded functions contain no borrowed values, is invalid.
         However, it is harmless because corresponding linear value cannot be consumed in the fix-term.
         Consider an application: (fix ...) args
         - (fix ...) cannot capture linear variables because it is a function
         - borrowcheck_function returns correct bused for (fix ...).
         - borrowcheck_function apply an constraint that
           args must not contain linear variables corresponds to bused of (fix ...).
         Thus, the corresponding linear variables of bused are not consumed and the borrowed values are usable in this fix-term.
       *)
      let borrow_env2 = CList.addn h ConstrMap.empty borrow_env in
      let bresults = Array.map (borrowcheck_function env2 sigma lvar_env2 borrow_env2) fary in
      borrow_union_ary bresults
  | Lambda _ ->
      let (args, body) = EConstr.decompose_lambda sigma term in
      (* args is a list of pairs of name and type from innermost (last) argument to outermost (first) argument *)
      if isFix sigma body then
        (* linear argument is prohibited in args (because fix-bounded functions may be called multiple times) *)
        let (env3, lvar_env3) =
          List.fold_right
            (fun (x,ty) (env,lvar_env) ->
              let env2 = env_push_assum env x ty in
              if is_linear_type env sigma ty then
                user_err_hov (Pp.str "[codegen] linear argument outside of fix-term:" +++
                  Pp.str (str_of_name (Context.binder_name x)))
              else
                (env2, None :: lvar_env))
            args (env, lvar_env)
        in
        let borrow_env3 =
          CList.addn (List.length args) ConstrMap.empty borrow_env
        in
        borrowcheck_function env3 sigma lvar_env3 borrow_env3 body
      else
        (* function/closure body found *)
        (* linear argument is possible in args *)
        let (env3, lvar_env3) =
          List.fold_right
            (fun (x,ty) (env,lvar_env) ->
              let env2 = env_push_assum env x ty in
              if is_linear_type env sigma ty then
                (env2, Some (Environ.nb_rel env) :: lvar_env)
              else
                (env2, None :: lvar_env))
            args (env, lvar_env)
        in
        let borrow_env3 =
          CList.addn (List.length args) ConstrMap.empty borrow_env
        in
        let body_ty = nf_all env sigma (Retyping.get_type_of env3 sigma body) in
        let (lconsumed,bused,bresult) = borrowcheck_expression env3 sigma lvar_env3 borrow_env3 body body_ty in
        let linear_args = IntSet.of_list (List.filter_map (fun opt -> opt) (CList.firstn (List.length args) lvar_env3)) in
        let (lconsumed_in_args, lconsumed_in_fv) = IntSet.partition (fun l -> Environ.nb_rel env <= l) lconsumed in
        if not (IntSet.equal linear_args lconsumed_in_args) then
          if IntSet.is_empty (IntSet.diff lconsumed_in_args linear_args) then
            user_err_hov (Pp.str "[codegen] linear argument not consumed:" +++
              pr_deBruijn_level_set env3 (IntSet.diff linear_args lconsumed_in_args))
          else
            user_err_hov (Pp.str "[codegen:bug] non-linear argument consumed as linear variable:" +++
              pr_deBruijn_level_set env3 (IntSet.diff lconsumed_in_args linear_args))
        else if not (IntSet.is_empty lconsumed_in_fv) then
          user_err_hov (Pp.str "[codegen] function cannot refer free linear variables:" +++ pr_deBruijn_level_set env lconsumed_in_fv)
        else
          borrow_filter_lvar (fun l -> l < Environ.nb_rel env) bused

  | _ ->
      (* global constant *)
      (if not (Environ.nb_rel env = 0) then
        user_err_hov (Pp.str "[codegen:bug] borrowcheck_function1 takes non-lambda/fix only when env is empty"));
      let term_ty = nf_all env sigma (Retyping.get_type_of env sigma term) in
      ignore (borrowcheck_expression env sigma lvar_env borrow_env term term_ty);
      ConstrMap.empty

and borrowcheck_expression (env : Environ.env) (sigma : Evd.evar_map)
    (lvar_env : int option list) (borrow_env : borrow_t list)
    (term : EConstr.t) (term_ty : EConstr.types) : (IntSet.t * borrow_t * borrow_t) =
  if !opt_debug_borrowcheck then
    msg_debug_hov (Pp.str "[codegen:borrowcheck_expression] start:" +++
      Pp.str "lvar_env=[" ++
      pp_sjoinmap_ary
        (fun i ->
          Pp.str (str_of_name_permissive (Context.Rel.Declaration.get_name (Environ.lookup_rel i env))) ++
          Pp.str "=>" ++
          match List.nth lvar_env (i-1) with
          | None -> Pp.str "None"
          | Some l -> pr_deBruijn_level env l)
        (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
      Pp.str "]" +++
      Pp.str "borrow_env=[" ++
      pp_sjoinmap_ary
        (fun i ->
          Pp.str (str_of_name_permissive (Context.Rel.Declaration.get_name (Environ.lookup_rel i env))) ++
          Pp.str "=>{" ++
          pp_sjoinmap_list
            (fun (ty,set) ->
              Printer.pr_constr_env env sigma ty ++ Pp.str ":{" ++
              pr_deBruijn_level_set env set ++ Pp.str "}")
            (ConstrMap.bindings (List.nth borrow_env (i-1))) ++
          Pp.str "}")
        (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
      Pp.str "]" +++
      Printer.pr_econstr_env env sigma term +++
      Pp.str ":" +++ Printer.pr_econstr_env env sigma term_ty);
  let (lconsumed, bused, bresult) = borrowcheck_expression1 env sigma lvar_env borrow_env term term_ty in
  (if not (IntSet.subset (lvariables_of_borrow bresult) (IntSet.diff (lvariables_of_borrow bused) lconsumed)) then
    user_err_hov (Pp.str "[codegen:bug] not (bresult <= (bused - lconsumed))"));
  (if not (IntSet.is_empty lconsumed) && not (IntSet.max_elt lconsumed < Environ.nb_rel env) then
    user_err_hov (Pp.str "[codegen:bug] lconsumed contains too big de Bruijn level:" +++
      Pp.str "env has" +++ Pp.int (Environ.nb_rel env) +++ Pp.str "variables" +++
      Pp.str "[" ++
        pp_sjoinmap_ary
          (fun i -> Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)))
          (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
      Pp.str "]" +++
      Pp.str "but lconsumed contains" +++
      Pp.int (IntSet.max_elt lconsumed)));
  (if not (ConstrMap.is_empty bused) && not (borrow_max_elt bused < Environ.nb_rel env) then
    user_err_hov (Pp.str "[codegen:bug] bused contains too big de Bruijn level:" +++
      Pp.str "env has" +++ Pp.int (Environ.nb_rel env) +++ Pp.str "variables" +++
      Pp.str "[" ++
        pp_sjoinmap_ary
          (fun i -> Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)))
          (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
      Pp.str "]" +++
      Pp.str "but bused contains" +++
      Pp.int (borrow_max_elt bused)));
  (if not (ConstrMap.is_empty bresult) && not (borrow_max_elt bresult < Environ.nb_rel env) then
    user_err_hov (Pp.str "[codegen:bug] bresult contains too big de Bruijn level:" +++
      Pp.str "env has" +++ Pp.int (Environ.nb_rel env) +++ Pp.str "variables" +++
      Pp.str "[" ++
        pp_sjoinmap_ary
          (fun i -> Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)))
          (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
      Pp.str "]" +++
      Pp.str "but bresult contains" +++
      Pp.int (borrow_max_elt bresult)));
  if !opt_debug_borrowcheck then
    msg_debug_hov (Pp.str "[codegen:borrowcheck_expression] return:" +++
      Pp.str "lconsumed=" ++ pr_deBruijn_level_set env lconsumed +++
      Pp.str "bused=" ++ pr_borrow env sigma bused +++
      Pp.str "bresult=" ++ pr_borrow env sigma bresult +++
      Printer.pr_econstr_env env sigma term +++
      Pp.str ":" +++ Printer.pr_econstr_env env sigma term_ty);
  (lconsumed, bused, bresult)
and borrowcheck_expression1 (env : Environ.env) (sigma : Evd.evar_map)
    (lvar_env : int option list) (borrow_env : borrow_t list)
    (term : EConstr.t) (term_ty : EConstr.types) : (IntSet.t * borrow_t * borrow_t) =
  let (term, argsary) = decompose_appvect sigma term in
  let vs = CArray.map_to_list (fun rel -> Environ.nb_rel env - destRel sigma rel) argsary in
  let check_app (lconsumed : IntSet.t) (bresult : borrow_t) : IntSet.t * borrow_t =
    if CList.is_empty vs then
      (lconsumed, bresult)
    else if not (IntSet.is_empty lconsumed) then
      (* cannot reached? *)
      user_err_hov (Pp.str "[codegen] function cannot refer free linear variables:" +++ pr_deBruijn_level_set env lconsumed)
    else
      let lvars_in_args_list =
        List.filter_map
          (fun l ->
            let i = Environ.nb_rel env - l in
            List.nth lvar_env (i-1))
          vs
      in
      let lvars_in_args_set = IntSet.of_list lvars_in_args_list in
      let borrow_in_app =
        List.fold_left
          (fun brw l ->
            let i = Environ.nb_rel env - l in
            borrow_union
              brw
              (List.nth borrow_env (i-1)))
          bresult vs
      in
      let duplicates = intlist_duplicates lvars_in_args_list in
      if not (CList.is_empty duplicates) then
        user_err_hov (Pp.str "[codegen] linear variables used multiply in arguments:" +++
          pp_sjoinmap_list (pr_deBruijn_level env) duplicates)
      else if not (IntSet.disjoint lvars_in_args_set (lvariables_of_borrow borrow_in_app)) then
        (* We don't know how free variables of the function (term) and its arguments (vs) are used in term.
           So we determine its safety conservatively *)
        user_err_hov (Pp.str "[codegen] linear variable and its borrowed value are used both in an application:" +++ pr_deBruijn_level_set env (IntSet.inter lvars_in_args_set (lvariables_of_borrow borrow_in_app)))
      else
        (lvars_in_args_set, borrow_in_app)
  in
  let filter_result bresult = filter_borrow env sigma term_ty bresult in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _
  | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
      user_err_hov (Pp.str "[codegen:borrowcheck_expression] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      let bresult = List.nth borrow_env (i-1) in
      let lconsumed =
        match List.nth lvar_env (i-1) with
        | Some l -> IntSet.singleton l
        | None -> IntSet.empty
      in
      if CList.is_empty vs then
        (lconsumed, bresult, bresult)
      else (* term is a function.  So term is not linear and lconsumed should be empty. *)
        let (lconsumed', bused') = check_app lconsumed bresult in
        (lconsumed', bused', filter_result bused')
  | Const (ctnt, univ) ->
      if Cset.mem ctnt !borrow_function_set then
        (assert (List.length vs = 1);
        let l = List.hd vs in (* the argument is a linear variable which we borrow it here *)
        let i = Environ.nb_rel env - l in
        let (x,argty,retty) = destProd sigma (nf_all env sigma (Retyping.get_type_of env sigma term)) in
        let env2 = env_push_assum env x argty in
        let tys =
          match component_types env2 sigma retty with
          | None -> user_err_hov (Pp.str "[codegen:bug] borrow function's result contains a function:" +++ Constant.print ctnt);
          | Some set ->
              (ConstrSet.iter
                (fun ty ->
                  if is_linear_type env sigma (EConstr.of_constr ty) then
                    user_err_hov (Pp.str "[codegen] borrow function's return type contains linear type:" +++
                                  Pp.str "the return type (" ++ Printer.pr_econstr_env env sigma retty ++ Pp.str ")" +++
                                  Pp.str "contains a linear type (" ++ Printer.pr_constr_env env sigma ty ++ Pp.str ")"))
                set;
              List.filter (fun ty -> is_borrow_type env sigma (EConstr.of_constr ty)) (ConstrSet.elements set))
        in
        let l =
          match List.nth lvar_env (i-1) with
          | Some l' -> l'
          | None -> user_err_hov (Pp.str "[codegen:bug] borrow function's argument is non-linear:" +++
                                  Constant.print ctnt +++
                                  Pp.str "(" ++ Printer.pr_econstr_env env sigma (mkRel i) ++ Pp.str ")")
        in
        let bresult = borrow_of_list (List.map (fun ty -> (ty,l)) tys) in
        (IntSet.empty, bresult, bresult))
      else
        if CList.is_empty vs then
          (IntSet.empty, ConstrMap.empty, ConstrMap.empty)
        else
          let (lconsumed', bused') = check_app IntSet.empty ConstrMap.empty in
          (lconsumed', bused', filter_result bused')
  | Construct _ ->
      let (lconsumed', bused') = check_app IntSet.empty ConstrMap.empty in
      (* the return value of constructor application contains all arguments including the borrowed values *)
      (lconsumed', bused', bused')
  | Fix _ ->
      if CList.is_empty vs then
        (* closure creation *)
        let bresult = borrowcheck_function env sigma lvar_env borrow_env term in
        (IntSet.empty, bresult, bresult)
      else
        let bresult = borrowcheck_function env sigma lvar_env borrow_env term in
        let (lconsumed', bused') = check_app IntSet.empty bresult in
        (lconsumed', bused', filter_result bused')

  | Lambda (x, ty, b) ->
      (* closure creation *)
      let bresult = borrowcheck_function env sigma lvar_env borrow_env term in
      (IntSet.empty, bresult, bresult)

  | LetIn (x, e, ty, b) ->
      assert (vs = []);
      let (lconsumed1, bused1, bresult1) = borrowcheck_expression env sigma lvar_env borrow_env e ty in
      let env2 = env_push_def env x e ty in
      let ty_is_linear = is_linear_type env sigma ty in
      let l = Environ.nb_rel env in
      let lvar_env2 =
        (if ty_is_linear then Some l else None) :: lvar_env
      in
      let borrow_env2 = bresult1 :: borrow_env in
      let (lconsumed2, bused2, bresult2) = borrowcheck_expression env2 sigma lvar_env2 borrow_env2 b term_ty in
      if not (IntSet.disjoint lconsumed1 lconsumed2) then
        user_err_hov (Pp.str "[codegen] linear variables consumed multiply:" +++ pr_deBruijn_level_set env (IntSet.inter lconsumed1 lconsumed2))
      else if ty_is_linear && not (IntSet.mem l lconsumed2) then
        user_err_hov (Pp.str "[codegen] linear variable not consumed:" +++ Pp.str (str_of_name (Context.binder_name x)))
      else if not (IntSet.disjoint lconsumed1 (lvariables_of_borrow bused2)) then
        user_err (Pp.str "[codegen] linear variable and its borrowed value are used inconsistently in let-in:" +++ pr_deBruijn_level_set env (IntSet.inter lconsumed1 (lvariables_of_borrow bused2)))
      else
        let lconsumed0 = IntSet.remove l (IntSet.union lconsumed1 lconsumed2) in
        let bused0 = borrow_remove l (borrow_union bused1 bused2) in
        let bresult0 = borrow_remove l bresult2 in
        (lconsumed0, bused0, bresult0)

  | Case (ci,u,pms,p,iv,item,bl) ->
      assert (vs = []);
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let item_ty = Retyping.get_type_of env sigma item in
      let (lconsumed1, bused1, bresult1) = borrowcheck_expression env sigma lvar_env borrow_env item item_ty in
      let branch_results =
        Array.map2
          (fun (nas,body) (ctx,_) -> (* ctx is a list from inside declaration to outside declaration *)
            (*let env2 = EConstr.push_rel_context ctx env in*)
            let (env2,lvar_env2,borrow_env2) =
              Context.Rel.fold_outside
                (fun decl (env1,lvar_env1,borrow_env1) ->
                  let env1' = EConstr.push_rel decl env1 in
                  match decl with
                  | Context.Rel.Declaration.LocalAssum (x, ty) ->
                      let lvar_env1' =
                        (if is_linear_type env1 sigma ty then
                          Some (Environ.nb_rel env1)
                        else
                          None) :: lvar_env1
                      in
                      (*msg_debug_hov (Pp.str "[codegen:borrowcheck_expression] match constructor argument:" +++
                        Id.print (id_of_name (Context.binder_name x)) +++ Pp.str "is" +++
                        (if is_borrow_type env1 sigma ty then Pp.str "borrow" else Pp.str "not-borrowed"));*)
                      let borrow_env1' =
                        filter_borrow env1 sigma ty (List.nth borrow_env (destRel sigma item  - 1)) :: borrow_env1
                      in
                      (env1',lvar_env1',borrow_env1')
                  | Context.Rel.Declaration.LocalDef (x, e, ty) ->
                      user_err_hov (Pp.str "[codegen] let-in in constructor type is not supported yet"))
                ctx ~init:(env,lvar_env,borrow_env)
            in
            let (br_lconsumed,br_bused,br_bresult) = borrowcheck_expression env2 sigma lvar_env2 borrow_env2 body term_ty in
            let linear_args = IntSet.of_list (List.filter_map (fun opt -> opt) (CList.firstn (List.length ctx) lvar_env2)) in
            let (lconsumed_in_fv, lconsumed_in_members) = IntSet.partition (fun l -> Environ.nb_rel env > l) br_lconsumed in
            let bused_in_fv = borrow_filter_lvar (fun l -> Environ.nb_rel env > l) br_bused in
            let bresult_in_fv = borrow_filter_lvar (fun l -> Environ.nb_rel env > l) br_bresult in
            if not (IntSet.equal linear_args lconsumed_in_members) then
              if IntSet.is_empty (IntSet.diff lconsumed_in_members linear_args) then
                user_err_hov (Pp.str "[codegen] linear member not consumed:" +++
                  pr_deBruijn_level_set env2 (IntSet.diff linear_args lconsumed_in_members))
              else
                user_err_hov (Pp.str "[codegen:bug] non-linear member consumed as linear variable:" +++
                  pr_deBruijn_level_set env2 (IntSet.diff lconsumed_in_members linear_args))
            else
              (lconsumed_in_fv,bused_in_fv,bresult_in_fv))
          bl bl0
      in
      let (br0_lconsumed,_,_) = branch_results.(0) in
      if Array.exists (fun (br_lconsumed,_,_) -> not (IntSet.equal br0_lconsumed br_lconsumed)) branch_results then
        let union = Array.fold_left (fun lconsumed (br_lconsumed,_,_) -> IntSet.union lconsumed br_lconsumed) IntSet.empty branch_results in
        let inter = Array.fold_left (fun lconsumed (br_lconsumed,_,_) -> IntSet.inter lconsumed br_lconsumed) br0_lconsumed branch_results in
        let (mutind, i) = ci.ci_ind in
        let mind_body = Environ.lookup_mind mutind env in
        let oind_body = mind_body.Declarations.mind_packets.(i) in
        let consnames = oind_body.Declarations.mind_consnames in
        let msgs =
          List.map
            (fun l ->
              let ids =
                List.filter_map (fun opt -> opt)
                  (Array.to_list
                    (Array.map2
                      (fun id (br_lconsumed,_,_) -> if IntSet.mem l br_lconsumed then Some id else None)
                      consnames branch_results))
              in
              pr_deBruijn_level env l +++ Pp.str "is used only for constructor" +++
                pp_sjoinmap_list Id.print ids +++ Pp.str "of" +++
                Id.print oind_body.Declarations.mind_typename)
            (IntSet.elements (IntSet.diff union inter))
        in
        user_err_hov (Pp.str "[codegen] match-branches uses linear variables inconsistently:" +++
          pp_join_list (Pp.str "," ++ Pp.spc ()) msgs)
      else if not (IntSet.disjoint lconsumed1 br0_lconsumed) then
        user_err_hov (Pp.str "[codegen] linear match-item is used in match-branch:" +++
          pr_deBruijn_level_set env (IntSet.inter lconsumed1 br0_lconsumed))
      else
        let lconsumed2 = br0_lconsumed in
        let bresult2 = Array.fold_left (fun bresult (br_lconsumed,br_bused,br_bresult) -> borrow_union bresult br_bresult) ConstrMap.empty branch_results in
        let bused2 = Array.fold_left (fun bused (br_lconsumed,br_bused,br_bresult) -> borrow_union bused br_bused) ConstrMap.empty branch_results in
        if not (IntSet.disjoint lconsumed1 (lvariables_of_borrow bused2)) then
          user_err_hov (Pp.str "[codegen] linear variable and its borrowed value are used inconsistently in match:" +++ pr_deBruijn_level_set env (IntSet.inter lconsumed1 (lvariables_of_borrow bused2)))
        else
          (IntSet.union lconsumed1 lconsumed2,
           borrow_union bused1 bused2,
           bresult2)

  | Proj (proj, sr, expr) ->
      if CList.is_empty vs then
        let expr_ty = nf_all env sigma (Retyping.get_type_of env sigma expr) in
        let (lconsumed1, bused1, bresult1) = borrowcheck_expression env sigma lvar_env borrow_env expr expr_ty in
        (lconsumed1, bused1, filter_result bresult1)
      else
        user_err_hov (Pp.str "[codegen] the result of projection is a function")

let rec borrowcheck_constructor (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (vs : int list) : unit =
  let open Declarations in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err_hov (Pp.str "[codegen:borrowcheck_constructor] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | App (f, argsary) ->
      borrowcheck_constructor env sigma f
        (List.append (CArray.map_to_list (fun rel -> Environ.nb_rel env - destRel sigma rel) argsary) vs)
  | Rel _ -> ()
  | Const _ -> ()
  | Construct (cstr,u) ->
      let (ind,j) = cstr in
      let (mutind,i) = ind in
      let mind_body = Environ.lookup_mind mutind env in
      let params = CArray.map_of_list (fun l -> mkRel (Environ.nb_rel env - l)) (CList.firstn mind_body.mind_nparams vs) in
      let ty = mkApp (mkIndU (ind, u), params) in
      (*msg_debug_hov (Pp.str "[codegen:borrowcheck_constructor] ty=" ++ Printer.pr_econstr_env env sigma ty);*)
      if is_borrow_type env sigma ty then
        user_err_hov (Pp.str "[codegen] constructor of borrow type used:" +++ Printer.pr_econstr_env env sigma term)

  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      Array.iter (fun f -> borrowcheck_constructor env2 sigma f []) fary

  | Lambda (x, ty, b) ->
      let env2 = env_push_assum env x ty in
      (match vs with
      | [] -> (* closure creation *)
          borrowcheck_constructor env2 sigma b []
      | _ :: rest_vs ->
          borrowcheck_constructor env2 sigma b rest_vs)

  | LetIn (x, e, ty, b) ->
      borrowcheck_constructor env sigma e [];
      let env2 = env_push_def env x e ty in
      borrowcheck_constructor env2 sigma b vs

  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      Array.iter2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          borrowcheck_constructor env2 sigma body vs)
        bl bl0

  | Proj (proj, sr, expr) ->
      borrowcheck_constructor env sigma expr []

let borrowcheck (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : unit =
  ignore (borrowcheck_function env sigma [] [] term);
  borrowcheck_constructor env sigma term []

let add_borrow_type ?(msg_new:bool=false) ?(msg_already:bool=false)
    (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : unit =
  let tyset = ConstrSet.of_list (CArray.map_to_list (EConstr.to_constr sigma) (mutual_inductive_types env sigma ty)) in
  let added = ConstrSet.diff tyset !borrow_type_set in
  let already_added = ConstrSet.inter tyset !borrow_type_set in
  if not (ConstrSet.subset tyset !borrow_type_set) then
    borrow_type_set := ConstrSet.union tyset !borrow_type_set;
  if msg_new then
    List.iter
      (fun ty ->
        Feedback.msg_info (Pp.str "[codegen] borrow type registered:" +++ Printer.pr_constr_env env sigma ty))
      (ConstrSet.elements added);
  if msg_already then
    List.iter
      (fun ty ->
        Feedback.msg_info (Pp.str "[codegen] borrow type already registered:" +++ Printer.pr_constr_env env sigma ty))
      (ConstrSet.elements already_added);
  ()

let command_borrow_type (ty : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty2) = Constrintern.interp_constr_evars env sigma ty in
  let ty4 = nf_all env sigma ty2 in
  (if not (is_concrete_inductive_type env sigma ty4) then
    user_err (Pp.str "[codegen] BorrowType: concrete inductive type expected:" +++ Printer.pr_econstr_env env sigma ty4));
  add_borrow_type ~msg_new:true ~msg_already:true env sigma ty4;
  ()

let command_borrow_function (libref : Libnames.qualid) : unit =
  let set_linear env sigma ty =
    add_linear_type ~msg_new:true env sigma ty
  in
  let set_borrow_type env sigma ty = add_borrow_type ~msg_new:true env sigma (EConstr.of_constr ty) in
  let set_borrow_function ctnt =
    if Cset.mem ctnt !borrow_function_set then
      ()
    else
      borrow_function_set := Cset.add ctnt !borrow_function_set
  in
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match gref with
  | ConstRef ctnt ->
      (let fctntu = UVars.in_punivs ctnt in
      let (ty, u) = Environ.constant_type env fctntu in
      let ty = nf_all env sigma (EConstr.of_constr ty) in
      (match EConstr.kind sigma ty with
      | Prod (x, argty, retty) ->
          if not (isInd sigma (fst (decompose_appvect sigma argty))) then
            user_err (Pp.str "[codegen] CodeGen BorrowFunc needs a function which argument type is an inductive type:" +++ Printer.pr_constant env ctnt);
          if not (isInd sigma (fst (decompose_appvect sigma retty))) then
            user_err (Pp.str "[codegen] CodeGen BorrowFunc needs a function which result type is an inductive type:" +++ Printer.pr_constant env ctnt);
          let env2 = env_push_assum env x argty in
          let ret_comptypes = component_types env2 sigma retty in
          let arg_comptypes = component_types env2 sigma argty in
          (match ret_comptypes, arg_comptypes with
          | None, _ ->
              user_err_hov (Pp.str "[codegen] borrow function's result contains a function:" +++ Constant.print ctnt);
          | _, None ->
              user_err_hov (Pp.str "[codegen] borrow function's argument contains a function:" +++ Constant.print ctnt);
          | Some ret_comptypes, Some arg_comptypes ->
              (let borrow_types = ConstrSet.diff ret_comptypes arg_comptypes in
              let linear_types = ConstrSet.diff arg_comptypes ret_comptypes in
              if ConstrSet.is_empty borrow_types then
                user_err_hov (Pp.str "[codegen] couldn't find borrow types from borrow function:" +++
                              Printer.pr_constant env ctnt);
              if ConstrSet.is_empty linear_types then
                user_err_hov (Pp.str "[codegen] couldn't find linear types from borrow function:" +++
                              Printer.pr_constant env ctnt);
              ConstrSet.iter
                (fun ty -> set_borrow_type env sigma ty)
                borrow_types;
              ConstrSet.iter
                (fun ty -> set_linear env sigma (EConstr.of_constr ty))
                linear_types;
              set_borrow_function ctnt))
      | _ -> user_err (Pp.str "[codegen] CodeGen BorrowFunc needs a function:" +++ Printer.pr_constant env ctnt)))
  | _ -> user_err (Pp.str "[codegen] CodeGen BorrowFunc needs a constant reference:" +++ Printer.pr_global gref)

let command_test_linear (t : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_constr_evars env sigma t in
  if is_linear env sigma t then
    Feedback.msg_info (Pp.str "linear type:" +++ Printer.pr_econstr_env env sigma t)
  else
    user_err (Pp.str "[codegen] unrestricted type:" +++ Printer.pr_econstr_env env sigma t)

let command_test_unrestricted (t : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_constr_evars env sigma t in
  if is_linear env sigma t then
    user_err (Pp.str "[codegen] linear type:" +++ Printer.pr_econstr_env env sigma t)
  else
    Feedback.msg_info (Pp.str "unrestricted type:" +++ Printer.pr_econstr_env env sigma t)

let command_test_borrowcheck (term : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, term) = Constrintern.interp_constr_evars env sigma term in
  borrowcheck env sigma term


