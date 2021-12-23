open Names
open GlobRef
open CErrors
open Term
open Constr
open EConstr

open Cgenutil
open State

module IntMap = HMap.Make(Int)

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = Reductionops.nf_all env sigma term

let prod_appvect (sigma : Evd.evar_map) (c : EConstr.t) (v : EConstr.t array) : EConstr.t = EConstr.of_constr (prod_appvect (EConstr.to_constr sigma c) (Array.map (EConstr.to_constr sigma) v))

let rec is_concrete_inductive_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool =
  let termty = Retyping.get_type_of env sigma term in
  (if isSort sigma termty then
    match EConstr.kind sigma term with
    | Ind _ -> true
    | App (f, argsary) ->
        isInd sigma f &&
        Array.for_all (is_concrete_inductive_type env sigma) argsary
    | _ -> false
  else
    false) (* "list" is not "concrete" inductive type because it has concrete parameter *)

let command_linear (ty : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty2) = Constrintern.interp_constr_evars env sigma ty in
  let ty4 = nf_all env sigma ty2 in
  (if not (is_concrete_inductive_type env sigma ty4) then
    user_err (Pp.str "[codegen] linear: concrete inductive type expected:" +++ Printer.pr_econstr_env env sigma ty4));
  (match ConstrMap.find_opt (EConstr.to_constr sigma ty4) !type_linearity_map with
  | Some _ -> user_err (Pp.str "[codegen] linearity already defined:" +++ Printer.pr_econstr_env env sigma ty4)
  | None -> ());
  type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty4) LinearityIsLinear !type_linearity_map;
  Feedback.msg_info (Pp.str "[codegen] linear type registered:" +++ Printer.pr_econstr_env env sigma ty2)

let command_downward (ty : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty2) = Constrintern.interp_constr_evars env sigma ty in
  let ty4 = nf_all env sigma ty2 in
  (if not (is_concrete_inductive_type env sigma ty4) then
    user_err (Pp.str "[codegen] downward: concrete inductive type expected:" +++ Printer.pr_econstr_env env sigma ty4));
  (match ConstrMap.find_opt (EConstr.to_constr sigma ty4) !type_downward_map with
  | Some _ -> user_err (Pp.str "[codegen] downwardness already defined:" +++ Printer.pr_econstr_env env sigma ty4)
  | None -> ());
  type_downward_map := ConstrMap.add (EConstr.to_constr sigma ty4) DownwardOnly !type_downward_map;
  Feedback.msg_info (Pp.str "[codegen] downward type registered:" +++ Printer.pr_econstr_env env sigma ty2)

let type_of_inductive_arity (mind_arity : (Declarations.regular_inductive_arity, Declarations.template_arity) Declarations.declaration_arity) : Constr.t =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Constr.mkType (temp_arity : Declarations.template_arity).Declarations.template_level

let valid_type_param (env : Environ.env) (sigma : Evd.evar_map) (decl : Constr.rel_declaration) : bool =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> isSort sigma (whd_all env sigma (EConstr.of_constr ty))
  | Context.Rel.Declaration.LocalDef _ -> false

let make_ind_ary (env : Environ.env) (sigma : Evd.evar_map) (mutind : MutInd.t) : Declarations.mutual_inductive_body * EConstr.t array =
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
  let ind_ary = Array.map (fun j -> EConstr.mkInd (mutind, j))
    (iota_ary 0 mind_body.mind_ntypes) in
  (mind_body,ind_ary)

let mutual_inductive_types (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : EConstr.t array =
  let (ty_f, ty_args) = EConstr.decompose_app sigma ty in
  let (mutind,i) =
    match EConstr.kind sigma ty_f with
    | Ind (ind,univ) -> ind
    | _ -> user_err_hov (Pp.str "[codegen:mutual_inductive_types] inductive type expected:" +++
                         Printer.pr_econstr_env env sigma ty)
  in
  let (_,ind_ary) = make_ind_ary env sigma mutind in
  Array.map (fun ind -> mkApp (ind, Array.of_list ty_args)) ind_ary

let mutind_cstrarg_iter (env : Environ.env) (sigma : Evd.evar_map) (mutind : MutInd.t) (params : EConstr.t array)
  (f : Environ.env -> (*typename*)Id.t -> (*consname*)Id.t ->
       (*argtype*)EConstr.types -> (*subst_ind*)Vars.substl -> unit) : unit =
  let open Declarations in
  let open Context.Rel.Declaration in
  let (mind_body,ind_ary) = make_ind_ary env sigma mutind in
  let subst_ind = Array.to_list (array_rev ind_ary) in
  let env2 = Environ.push_rel_context
              (Array.to_list
                (Array.map (fun oind_body ->
                  LocalAssum
                    (Context.annotR (Names.Name.Name oind_body.mind_typename),
                     type_of_inductive_arity oind_body.mind_arity))
                  (array_rev mind_body.mind_packets)))
              env
  in
  Array.iter
    (fun oind_body ->
      Array.iter
        (fun k ->
          (*msg_debug_hov (Pp.str "[codegen:mutind_cstrarg_iter] check env2" +++
                         Pp.str "typename=" ++ Id.print oind_body.mind_typename +++
                         Pp.str "consname=" ++ Id.print (oind_body.mind_consnames.(k)) +++
                         Pp.str "constype=" ++ Printer.pr_constr_env env2 sigma (oind_body.mind_user_lc.(k)));*)
          let (ctx, t) = oind_body.mind_nf_lc.(k) in
          let (t_f,t_args) = Constr.decompose_app t in
          if not (Constr.isRel t_f) then
            user_err_hov (Pp.str "[codegen:mutind_cstrarg_iter:bug] result of constructor type is not Rel:" +++
                          Printer.pr_constr_env env2 sigma t);
          let i = Constr.destRel t_f - List.length ctx in
          let decl = Environ.lookup_rel i env2 in
          let ind_id = oind_body.mind_typename in
          let id_in_env = id_of_name (get_name decl) in
          if not (Id.equal ind_id id_in_env) then
            user_err_hov (Pp.str "[codegen:mutind_cstrarg_iter:bug] inductive type name mismatch (1):" +++
                          Pp.str "expected:" ++ Id.print ind_id +++ Pp.str "but" +++
                          Pp.str "actual:" ++ Id.print id_in_env))
        (iota_ary 0 (Array.length oind_body.mind_consnames)))
    mind_body.mind_packets;
  Array.iter
    (fun oind_body ->
      let ind_id = oind_body.mind_typename in
      Array.iter2
        (fun cons_id nf_lc ->
          (* ctx is a list of decls from innermost to outermost *)
          let (ctx, t) = nf_lc in
          let t = EConstr.of_constr t in
          let rev_ctx = array_rev (Array.of_list ctx) in
          let env3 = ref env2 in
          let params = ref (Array.to_list params) in
          let h = Array.length rev_ctx in
          for i = 0 to h - 1 do
            let decl = rev_ctx.(i) in
            match decl with
            | LocalDef (x,e,ty) ->
                env3 := Environ.push_rel decl !env3
            | LocalAssum (x,ty) ->
                let ty = EConstr.of_constr ty in
                (match !params with
                | param :: rest ->
                    params := rest;
                    env3 := EConstr.push_rel (LocalDef (x, param, ty)) !env3
                | [] ->
                    let ty = whd_all !env3 sigma ty in
                    if not (Vars.noccur_between sigma 1 (i - List.length mind_body.mind_params_ctxt) ty) then
                      user_err_hov (Pp.str "[codegen] dependent constructor:" +++ Id.print ind_id +++ Id.print cons_id);
                    let ty = Vars.lift (-i) ty in
                    f env2 ind_id cons_id ty subst_ind;
                    env3 := Environ.push_rel decl !env3)
          done;
          let t = whd_all !env3 sigma t in
          if not (Vars.noccur_between sigma 1 (h - List.length mind_body.mind_params_ctxt) t) then
            user_err_hov (Pp.str "[codegen] dependent constructor result:" +++ Id.print ind_id +++ Id.print cons_id +++ Printer.pr_econstr_env !env3 sigma t);
          let t = Vars.lift (-h) t in
          let t' = Vars.substl subst_ind t in
          let (tf, targs) = decompose_app sigma t' in
          if not (EConstr.isInd sigma tf) then
            user_err_hov (Pp.str "[codegen:mutind_cstrarg_iter:bug] result of constructor type is not Ind:" +++
                          Printer.pr_econstr_env env sigma t');
          let ((mutind2, i2), univ) = EConstr.destInd sigma tf in
          let mind_body2 = Environ.lookup_mind mutind2 env2 in
          let id_via_substitution = mind_body2.mind_packets.(i2).mind_typename in
          if not (Id.equal ind_id id_via_substitution) then
            user_err_hov (Pp.str "[codegen:mutind_cstrarg_iter:bug] inductive type name mismatch (2):" +++
                          Pp.str "expected:" ++ Id.print ind_id +++ Pp.str "but" +++
                          Pp.str "actual:" ++ Id.print id_via_substitution))
        oind_body.mind_consnames oind_body.mind_nf_lc)
    mind_body.mind_packets

let rec component_types (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : ConstrSet.t option =
  let ret = ref (ConstrSet.of_list (CArray.map_to_list (EConstr.to_constr sigma) (mutual_inductive_types env sigma ty))) in
  let exception FoundFunction in
  try
    let (ty_f,ty_args) = EConstr.decompose_app sigma ty in
    let ty_args = Array.of_list ty_args in
    (match EConstr.kind sigma ty_f with
    | Prod _ -> raise FoundFunction
    | Ind (ind, univ) -> ()
    | _ -> user_err (Pp.str "[codegen:component_types] unexpected type:" +++ Printer.pr_econstr_env env sigma ty));
    mutind_cstrarg_iter env sigma (fst (fst (destInd sigma ty_f))) ty_args
      (fun env ind_id cons_id argty subst_ind ->
        let (argty_f,argty_args) = EConstr.decompose_app sigma argty in
        match EConstr.kind sigma argty_f with
        | Sort _ ->
            user_err (Pp.str "[codegen] component_types: constructor has type argument")
        | Prod (x, ty, b) ->
            raise FoundFunction
        | Rel i ->
            ()
        | Ind _ ->
            (ret := ConstrSet.add (EConstr.to_constr sigma argty) !ret;
            match component_types env sigma argty with
            | None -> raise FoundFunction
            | Some set -> ret := ConstrSet.union !ret set)
        | _ ->
            user_err (Pp.str "[codegen:is_linear_ind] unexpected constructor argument:" +++ Printer.pr_econstr_env env sigma argty));
    Some !ret
  with
    FoundFunction -> None

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
let rec is_linear_type (env : Environ.env) (sigma :Evd.evar_map) (ty : EConstr.t) : bool =
  (*Feedback.msg_debug (Pp.str "[codegen] is_linear_type:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match EConstr.kind sigma ty with
  | Prod (name, namety, body) ->
      (* function type can be code-generatable or not.
        - forall (x:nat), nat is code-generatable when we'll support closures but
        - forall (x:nat), Set is not code-generatable.
        When it is code-generable,
        function type cannot be linear.
        So false is returned anyway.  *)
      false (* function (closure) must not reference outside linear variables *)
  | Ind iu -> is_linear_ind1 env sigma ty
  | App (f, argsary) when isInd sigma f -> is_linear_ind1 env sigma ty
  | _ ->
      (* not code-generatable. *)
      false

and is_linear_ind1 (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (Pp.str "[codegen] is_linear_ind1:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match ConstrMap.find_opt (EConstr.to_constr sigma ty) !type_linearity_map with
  | Some LinearityIsLinear -> true
  | Some LinearityIsUnrestricted -> false
  | Some LinearityIsInvestigating -> user_err (Pp.str "[codegen:bug] type linearity checker is calld with a type currently checking:" +++ Printer.pr_econstr_env env sigma ty)
  | None ->
      (type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty) LinearityIsInvestigating !type_linearity_map;
      if is_linear_ind env sigma ty then
        (Feedback.msg_info (Pp.str "[codegen] Linear type registered:" +++ Printer.pr_econstr_env env sigma ty);
        type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty) LinearityIsLinear !type_linearity_map;
        true)
      else
        (Feedback.msg_info (Pp.str "[codegen] Non-linear (unrestricted) type registered:" +++ Printer.pr_econstr_env env sigma ty);
        type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty) LinearityIsUnrestricted !type_linearity_map;
        false))
and is_linear_ind (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (Pp.str "[codegen] is_linear_ind:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  let (ind_f, argsary) =
    match EConstr.kind sigma ty with
    | App (f, argsary) -> (f, argsary)
    | _ -> (ty, [| |])
  in
  Array.iter
    (fun arg ->
      if not (Vars.closed0 sigma arg) then
        user_err (Pp.str "[codegen] is_linear_ind: constructor type has has local reference:" +++ Printer.pr_econstr_env env sigma arg))
    argsary;
  let exception FoundLinear in
  try
    mutind_cstrarg_iter env sigma (fst (fst (destInd sigma ind_f))) argsary
      (fun env ind_id cons_id argty subst_ind ->
        let (argty_f,argty_args) = EConstr.decompose_app sigma argty in
        match EConstr.kind sigma argty_f with
        | Sort _ ->
            user_err (Pp.str "[codegen] is_linear_ind: constructor has type argument")
        | Prod (x, ty, b) ->
            (* function type argument of a constructor is non-linear or non-code-generatable *)
            ()
        | Rel _ ->
            (* Since mutind_cstrarg_iter normalizes argty,
              Rel is only used for recursive references of inductive types.
              We don't need to examine the recursive references.
              Note that we force uniform parameters and prohibit indexed-types,
              argty_args must be unchanged. *)
            ()
        | Ind _ ->
            if is_linear_type env sigma argty then raise FoundLinear
        | _ ->
            user_err (Pp.str "[codegen:is_linear_ind] unexpected constructor argument:" +++ Printer.pr_econstr_env env sigma argty));
    false
  with
    FoundLinear -> true

let is_linear (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (str "[codegen] is_linear:argument:" ++ Printer.pr_econstr_env env sigma ty);*)
  let sort = Retyping.get_type_of env sigma ty in
  if not (isSort sigma sort) then
    user_err (Pp.str "[codegen] not a type:" +++ Printer.pr_econstr_env env sigma ty +++ Pp.str ":" +++ Printer.pr_econstr_env env sigma sort);
  let ty2 = nf_all env sigma ty in
  is_linear_type env sigma ty2

let check_type_linearity (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : unit =
  ignore (is_linear env sigma ty)

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
let rec is_downward_type (env : Environ.env) (sigma :Evd.evar_map) (ty : EConstr.t) : bool =
  (*Feedback.msg_debug (Pp.str "[codegen] is_downward_type:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match EConstr.kind sigma ty with
  | Prod (name, namety, body) ->
      true (* function (closure) must be DownwardOnly *)
  | Ind iu -> is_downward_ind1 env sigma ty
  | App (f, argsary) when isInd sigma f -> is_downward_ind1 env sigma ty
  | _ ->
      (* not code-generatable. *)
      false

and is_downward_ind1 (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (Pp.str "[codegen] is_downward_ind1:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match ConstrMap.find_opt (EConstr.to_constr sigma ty) !type_downward_map with
  | Some DownwardOnly -> true
  | Some DownwardUnrestricted -> false
  | Some DownwardInvestigating -> user_err (Pp.str "[codegen:bug] type downwardness checker is calld with a type currently checking:" +++ Printer.pr_econstr_env env sigma ty)
  | None ->
      (type_downward_map := ConstrMap.add (EConstr.to_constr sigma ty) DownwardInvestigating !type_downward_map;
      if is_downward_ind env sigma ty then
        (Feedback.msg_info (Pp.str "[codegen] Downward type registered:" +++ Printer.pr_econstr_env env sigma ty);
        type_downward_map := ConstrMap.add (EConstr.to_constr sigma ty) DownwardOnly !type_downward_map;
        true)
      else
        (Feedback.msg_info (Pp.str "[codegen] Non-downward (unrestricted) type registered:" +++ Printer.pr_econstr_env env sigma ty);
        type_downward_map := ConstrMap.add (EConstr.to_constr sigma ty) DownwardUnrestricted !type_downward_map;
        false))
and is_downward_ind (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (Pp.str "[codegen] is_downward_ind:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  let (ind_f, argsary) =
    match EConstr.kind sigma ty with
    | App (f, argsary) -> (f, argsary)
    | _ -> (ty, [| |])
  in
  Array.iter
    (fun arg ->
      if not (Vars.closed0 sigma arg) then
        user_err (Pp.str "[codegen] is_downward_ind: constructor type has has local reference:" +++ Printer.pr_econstr_env env sigma arg))
    argsary;
  let exception FoundDownward in
  try
    mutind_cstrarg_iter env sigma (fst (fst (destInd sigma ind_f))) argsary
      (fun env ind_id cons_id argty subst_ind ->
        let (argty_f,argty_args) = EConstr.decompose_app sigma argty in
        match EConstr.kind sigma argty_f with
        | Sort _ ->
            user_err (Pp.str "[codegen] is_downward_ind: constructor has type argument")
        | Prod _ ->
            (* function type argument of a constructor means DownwardOnly *)
            raise FoundDownward
        | Rel _ ->
            ()
        | Ind _ ->
            if is_downward_type env sigma argty then raise FoundDownward
        | _ ->
            user_err (Pp.str "[codegen:is_downward_ind] unexpected constructor argument:" +++ Printer.pr_econstr_env env sigma argty));
    false
  with
    FoundDownward -> true

let is_downward (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (str "[codegen] is_downward:argument:" ++ Printer.pr_econstr_env env sigma ty);*)
  let sort = Retyping.get_type_of env sigma ty in
  if not (isSort sigma sort) then
    user_err (Pp.str "[codegen] not a type:" +++ Printer.pr_econstr_env env sigma ty +++ Pp.str ":" +++ Printer.pr_econstr_env env sigma sort);
  let ty2 = nf_all env sigma ty in
  is_downward_type env sigma ty2

(*let check_type_downwardness (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : unit =
  ignore (is_downward env sigma ty)*)

let with_local_var (env : Environ.env) (sigma : Evd.evar_map)
    (decl : EConstr.rel_declaration) (linear_vars : bool list)
    (numvars_innermost_function : int)
    (f : Environ.env -> bool list -> int -> int IntMap.t) : int IntMap.t =
  let env2 = EConstr.push_rel decl env in
  let name = Context.Rel.Declaration.get_name decl in
  let ty = Context.Rel.Declaration.get_type decl in
  let numvars_innermost_function2 = numvars_innermost_function+1 in
  if not (is_linear env sigma ty) then
    f env2 (false :: linear_vars) numvars_innermost_function2
  else
    (let count = f env2 (true :: linear_vars) numvars_innermost_function2 in
    let opt_n = IntMap.find_opt (Environ.nb_rel env) count in
    if opt_n <> Some 1 then
      user_err (Pp.str "[codegen] linear variable not lineary used:" +++ Names.Name.print name +++ Pp.str "(" ++ Pp.int (Stdlib.Option.value opt_n ~default:0) +++ Pp.str "times used)")
    else
      IntMap.remove (Environ.nb_rel env) count)

let merge_count (c1 : int IntMap.t) (c2 : int IntMap.t) : int IntMap.t =
  IntMap.merge
    (fun j n1 n2 -> Some (Stdlib.Option.value n1 ~default:0 + Stdlib.Option.value n2 ~default:0))
    c1 c2

let rec linearcheck_function (env : Environ.env) (sigma : Evd.evar_map) (linear_vars : bool list) (term : EConstr.t) : unit =
  let count = linearcheck_function_rec env sigma linear_vars 0 term in
  if IntMap.is_empty count then
    ()
  else
    user_err (Pp.str "[codegen] linear variable is referened by an inner function:" +++
      pp_sjoinmap_list
        (fun (j, _) -> Names.Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel (Environ.nb_rel env - j) env)))
        (IntMap.bindings count))
and linearcheck_function_rec (env : Environ.env) (sigma : Evd.evar_map) (linear_vars : bool list) (numvars_innermost_function : int) (term : EConstr.t) : int IntMap.t =
  ((*Feedback.msg_debug (str "[codegen] linearcheck_function:" +++ Printer.pr_econstr_env env sigma term);*)
  match EConstr.kind sigma term with
  | Lambda (name, ty, body) ->
      (check_type_linearity env sigma ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      with_local_var env sigma decl linear_vars numvars_innermost_function
        (fun env2 linear_vars2 numvars_innermost_function2 -> linearcheck_function_rec env2 sigma linear_vars2 numvars_innermost_function2 body))
  | _ -> linearcheck_exp env sigma linear_vars numvars_innermost_function term 0)
and linearcheck_exp (env : Environ.env) (sigma : Evd.evar_map) (linear_vars : bool list) (numvars_innermost_function : int) (term : EConstr.t) (numargs : int) : int IntMap.t =
  ((*Feedback.msg_debug (str "[codegen] linearcheck_exp:" +++ Printer.pr_econstr_env env sigma term);*)
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _
  | Sort _ | Prod _ | Ind _
  | CoFix _ | Array _ ->
      user_err (Pp.str "[codegen:linearcheck_exp] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.nth linear_vars (i-1) then
        IntMap.singleton (Environ.nb_rel env - i) 1
      else
        IntMap.empty
  | Cast (expr, kind, ty) ->
      (check_type_linearity env sigma ty;
      linearcheck_exp env sigma linear_vars numvars_innermost_function expr numargs)
  | Lambda (name, ty, body) ->
      if numargs <= 0 then
        (* closure creation found *)
        (linearcheck_function env sigma linear_vars term;
        IntMap.empty)
      else
	let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
	with_local_var env sigma decl linear_vars numvars_innermost_function
          (fun env2 linear_vars2 numvars_innermost_function2 -> linearcheck_exp env2 sigma linear_vars2 numvars_innermost_function2 body (numargs-1))
  | LetIn (name, expr, ty, body) ->
      (check_type_linearity env sigma ty;
      let count1 = linearcheck_exp env sigma linear_vars numvars_innermost_function expr 0 in
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let count2 = with_local_var env sigma decl linear_vars numvars_innermost_function
        (fun env2 linear_vars2 numvars_innermost_function2 -> linearcheck_exp env2 sigma linear_vars2 numvars_innermost_function2 body numargs) in
      merge_count count1 count2)
  | App (f, argsary) ->
      if isConst sigma f && Cset.mem (fst (destConst sigma f)) !borrow_function_set then
        (* borrow function application found.
           We don't count the linear variable reference of the argument of a borrow function application.
           The defer validity checking of borrow function to borrow checker. *)
        IntMap.empty
      else
        let count = linearcheck_exp env sigma linear_vars numvars_innermost_function f (Array.length argsary + numargs) in
        let counts = Array.map (fun arg -> linearcheck_exp env sigma linear_vars numvars_innermost_function arg 0) argsary in
        (* no partial application after argument completion? *)
        if Array.exists (fun arg -> let ty = Retyping.get_type_of env sigma arg in
                         is_linear env sigma ty) argsary &&
           isProd sigma (Retyping.get_type_of env sigma term) then
             user_err (Pp.str "[codegen] application with linear argument cannot return function value:" +++ Printer.pr_econstr_env env sigma term);
        Array.fold_left merge_count count counts
  | Const ctntu -> IntMap.empty
  | Construct cstru -> IntMap.empty
  | Case (ci,u,pms,p,iv,c,bl) ->
      let (ci, tyf, iv, expr, brs) = EConstr.expand_case env sigma (ci,u,pms,p,iv,c,bl) in
      ((* tyf is not checked because it is not a target of code generation.
          check tyf is (fun _ -> termty) ? *)
      let count0 = linearcheck_exp env sigma linear_vars numvars_innermost_function expr 0 in
      let chk_br cstr_nargs br = linearcheck_exp env sigma linear_vars numvars_innermost_function br (cstr_nargs + numargs) in
      let counts = Array.map2 chk_br ci.ci_cstr_nargs brs in
      Array.iter
        (fun c ->
          if not (IntMap.equal Int.equal c counts.(0)) then
            let pp_vars =
              List.filter_map
                (fun (j, b) ->
                  if b then
                    Some (Names.Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel (Environ.nb_rel env - j) env)))
                  else
                    None)
                (IntMap.bindings
                  (Array.fold_left
                    (fun bmap1 bmap2 ->
                      IntMap.merge
                        (fun j opt_b0 opt_b1 -> Some (Stdlib.Option.value opt_b0 ~default:false || Stdlib.Option.value opt_b1 ~default:false))
                        bmap1 bmap2)
                    IntMap.empty
                    (Array.map
                      (fun c ->
                        IntMap.merge
                          (fun j opt_n0 opt_n1 -> Some (Stdlib.Option.value opt_n0 ~default:0 <> Stdlib.Option.value opt_n1 ~default:0))
                          counts.(0) c)
                      counts)))
            in
            user_err (Pp.str "[codegen] inconsistent linear variable use in match branches:" +++ pp_sjoin_list pp_vars))
        counts;
      merge_count count0 counts.(0))
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      (let h = Array.length fary in
      let env2 = push_rec_types prec env in
      let linear_vars2 = CList.addn h false linear_vars in
      Array.iter (check_type_linearity env sigma) tary;
      (* Since fix-bounded funcitons can be evaluated 0 or more times,
        they cannot reference linear variables declared outside of the fix-expression. *)
      Array.iter (fun f -> linearcheck_function env2 sigma linear_vars2 f) fary;
      IntMap.empty)
  | Proj (proj, expr) ->
      linearcheck_exp env sigma linear_vars numvars_innermost_function expr 0
  | Int n -> IntMap.empty
  | Float n -> IntMap.empty)

let linear_type_check_term (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : unit =
  if not (ConstrMap.is_empty !type_linearity_map) then
    linearcheck_function env sigma [] term

let rec check_fix_downwardness (env : Environ.env) (sigma : Evd.evar_map) (cfunc : string) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _
  | Sort _ | Prod _ | Ind _
  | CoFix _ | Array _
  | Cast _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:check_fix_downwardness] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | Rel _ | Const _ | Construct _ -> ()
  | Lambda (x, ty, b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
      let env2 = EConstr.push_rel decl env in
      check_fix_downwardness env2 sigma cfunc b
  | LetIn (x, e, ty, b) ->
      check_fix_downwardness env sigma cfunc e;
      let decl = Context.Rel.Declaration.LocalDef (x, e, ty) in
      let env2 = EConstr.push_rel decl env in
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
  | Proj (proj, expr) ->
      check_fix_downwardness env sigma cfunc expr

let check_function_downwardness (env : Environ.env) (sigma : Evd.evar_map) (cfunc : string) (term : EConstr.t) : unit =
  let termty = Retyping.get_type_of env sigma term in
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
      (original_linear_var_in_env : int option list) (linear_vars_of_borrow_in_env : borrow_t list)
      (term : EConstr.t) : borrow_t = ...

  and borrowcheck_expression (env : Environ.env) (sigma : Evd.evar_map)
      (original_linear_var_in_env : int option list) (linear_vars_of_borrow_in_env : borrow_t list)
      (term : EConstr.t) (vs : int list) (term_vs_ty : EConstr.types) : (borrow_t * IntSet.t * borrow_t) = ...

  bresult = borrowcheck_function env sigma original_linear_var_in_env linear_vars_of_borrow_in_env term
  (bused, lconsumed, bresult) = borrowcheck_expression env sigma original_linear_var_in_env linear_vars_of_borrow_in_env term vs term_vs_ty

  borrowcheck_function verifies `term` as a function.
  It returns bresult that is a set of free borrowed variables in term.

  borrowcheck_expression verifies `term vs` as an expression.
  It returns (bused,lconsumed,bresult).

  term : term to evaluate
  vs : the list of variables (Rel) which are given to term

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

  original_linear_var_in_env : int option list
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

  linear_vars_of_borrow_in_env :
    This represents borrowed values used in variables.
    It is a list that length is same as Environ.nb_rel.
    It is indexed by de Bruijn index. (innermost variable is first)
    The type of each element is `borrow_t`.
    If i'th element (base-1) is `{A => {x}}`,
    i'th variable may contains values of type `A` borrowed from `x`.

  Constraint: bresult is a subset of bused - lconsumed
  *)

type borrow_t = IntSet.t ConstrMap.t

let pr_borrow (env : Environ.env) (sigma : Evd.evar_map) (lvs : borrow_t) =
  Pp.str "{" ++
  pp_joinmap_list (Pp.str "," ++ Pp.spc ())
    (fun (ty,set) -> Printer.pr_constr_env env sigma ty +++ Pp.str "in" +++ pr_deBruijn_level_set env set)
    (ConstrMap.bindings lvs) ++
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

let borrow_union (lvs1 : borrow_t) (lvs2 : borrow_t) : borrow_t =
  ConstrMap.merge
    (fun ty opt1 opt2 ->
      match opt1, opt2 with
      | Some set1, Some set2 -> Some (IntSet.union set1 set2)
      | Some set1, None -> Some set1
      | None, Some set2 -> Some set2
      | None, None -> None)
    lvs1 lvs2

let borrow_union_ary (lvs : borrow_t array) : borrow_t =
  Array.fold_left borrow_union ConstrMap.empty lvs

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

let borrow_filter_lvar (pred : int -> bool) (lvs : borrow_t) : borrow_t =
  constrmap_filter_map
    (fun ty set ->
      let set' = IntSet.filter pred set in
      if IntSet.is_empty set' then
        None
      else
        Some set')
    lvs

let borrow_remove (l : int) (lvs : borrow_t) : borrow_t =
  constrmap_filter_map
    (fun ty set ->
      let set' = IntSet.remove l set in
      if IntSet.is_empty set' then
        None
      else
        Some set')
    lvs

let lvariables_of_borrow (lvs : borrow_t) : IntSet.t =
  ConstrMap.fold
    (fun term set set0 -> IntSet.union set set0)
    lvs
    IntSet.empty

    (*
let borrow_equal (lvs1 : borrow_t) (lvs2 : borrow_t) : bool =
  ConstrMap.cardinal lvs1 = ConstrMap.cardinal lvs2 &&
  ConstrMap.for_all
    (fun term set1 -> match ConstrMap.find_opt term lvs2 with None -> false | Some set2 -> IntSet.equal set1 set2)
    lvs1
    *)

    (*
let borrow_disjoint (lvs1 : borrow_t) (lvs2 : borrow_t) : bool =
  IntSet.disjoint (lvariables_of_borrow lvs1) (lvariables_of_borrow lvs2)
  *)

let is_borrow_type (env : Environ.env) (sigma :Evd.evar_map) (ty : EConstr.t) : bool =
  ConstrSet.mem (EConstr.to_constr sigma ty) !borrow_type_set

let rec borrowcheck_function (env : Environ.env) (sigma : Evd.evar_map)
    (original_linear_var_in_env : int option list) (linear_vars_of_borrow_in_env : borrow_t list)
    (term : EConstr.t) : borrow_t =
  msg_debug_hov (Pp.str "[codegen:borrowcheck_function] start:" +++ Printer.pr_econstr_env env sigma term);
  let ret = borrowcheck_function1 env sigma original_linear_var_in_env linear_vars_of_borrow_in_env term in
  msg_debug_hov (Pp.str "[codegen:borrowcheck_function] retutrn:" +++
    Pp.str "bresult=" ++ pr_borrow env sigma ret +++
    Printer.pr_econstr_env env sigma term);
  ret
and borrowcheck_function1 (env : Environ.env) (sigma : Evd.evar_map)
    (original_linear_var_in_env : int option list) (linear_vars_of_borrow_in_env : borrow_t list)
    (term : EConstr.t) : borrow_t =
  match EConstr.kind sigma term with
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let original_linear_var_in_env' =
        CList.addn (Array.length fary) None original_linear_var_in_env
      in
      let linear_vars_of_borrow_in_env' =
        CList.addn (Array.length fary) ConstrMap.empty linear_vars_of_borrow_in_env
      in
      let bresults = Array.map (borrowcheck_function env2 sigma original_linear_var_in_env' linear_vars_of_borrow_in_env') fary in
      borrow_union_ary bresults
  | Lambda _ ->
      let (args, body) = EConstr.decompose_lam sigma term in
      (* args is a list of pairs of name and type from inner (last) argument from outer (first) argument *)
      if isFix sigma body then
        (* linear argument is prohibited in args (because fix-bounded functions may be called multiple times) *)
        let (env3, original_linear_var_in_env') =
          List.fold_right
            (fun (x,ty) (env,original_linear_var_in_env) ->
              let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
              let env2 = EConstr.push_rel decl env in
              if is_linear_type env sigma ty then
                user_err_hov (Pp.str "[codegen] linear argument out of fix-term:" +++
                  Pp.str (str_of_name (Context.binder_name x)))
              else
                (env2, None :: original_linear_var_in_env))
            args (env, original_linear_var_in_env)
        in
        let linear_vars_of_borrow_in_env' =
          CList.addn (List.length args) ConstrMap.empty linear_vars_of_borrow_in_env
        in
        borrowcheck_function env3 sigma original_linear_var_in_env' linear_vars_of_borrow_in_env' body
      else
        (* linear argument is possible in args *)
        (* function/closure body found *)
        let (env3, original_linear_var_in_env') =
          List.fold_right
            (fun (x,ty) (env,original_linear_var_in_env) ->
              let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
              let env2 = EConstr.push_rel decl env in
              if is_linear_type env sigma ty then
                (env2, Some (Environ.nb_rel env) :: original_linear_var_in_env)
              else
                (env2, None :: original_linear_var_in_env))
            args (env, original_linear_var_in_env)
        in
        let linear_vars_of_borrow_in_env' =
          CList.addn (List.length args) ConstrMap.empty linear_vars_of_borrow_in_env
        in
        let body_ty = Retyping.get_type_of env3 sigma body in
        let (bused,lconsumed,bresult) = borrowcheck_expression env3 sigma original_linear_var_in_env' linear_vars_of_borrow_in_env' body [] body_ty in
        let linear_args = IntSet.of_list (List.filter_map (fun opt -> opt) (CList.firstn (List.length args) original_linear_var_in_env')) in
        let linear_consumed = IntSet.filter (fun l -> Environ.nb_rel env <= l) lconsumed in
        if not (IntSet.equal linear_args linear_consumed) then
          if IntSet.is_empty (IntSet.diff linear_consumed linear_args) then
            user_err_hov (Pp.str "[codegen] linear argument not consumed:" +++
              pr_deBruijn_level_set env3 (IntSet.diff linear_args linear_consumed))
          else
            user_err_hov (Pp.str "[codegen:bug] non-linear argument consumed as linear variable:" +++
              pr_deBruijn_level_set env3 (IntSet.diff linear_consumed linear_args))
        else
          let bused' = borrow_filter_lvar (fun l -> l < Environ.nb_rel env) bused in
          let lconsumed' = IntSet.filter (fun l -> l < Environ.nb_rel env) lconsumed in
          if not (IntSet.is_empty lconsumed') then
            user_err_hov (Pp.str "[codegen] function cannot refer free linear variables:" +++ pr_deBruijn_level_set env lconsumed')
          else
            bused'

  | _ ->
      (* global constant *)
      let term_ty = Retyping.get_type_of env sigma term in
      let (bused,lconsumed,bresult) = borrowcheck_expression env sigma original_linear_var_in_env linear_vars_of_borrow_in_env term [] term_ty in
      bresult

and borrowcheck_expression (env : Environ.env) (sigma : Evd.evar_map)
    (original_linear_var_in_env : int option list) (linear_vars_of_borrow_in_env : borrow_t list)
    (term : EConstr.t) (vs : int list) (term_vs_ty : EConstr.types) : (borrow_t * IntSet.t * borrow_t) =
  msg_debug_hov (Pp.str "[codegen:borrowcheck_expression] start:" +++
    Pp.str "original_linear_var_in_env=[" ++
    pp_sjoinmap_ary
      (fun i ->
        Pp.str (str_of_name_permissive (Context.Rel.Declaration.get_name (Environ.lookup_rel i env))) ++
        Pp.str "=>" ++
        match List.nth original_linear_var_in_env (i-1) with
        | None -> Pp.str "None"
        | Some l -> pr_deBruijn_level env l)
      (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
    Pp.str "]" +++
    Pp.str "linear_vars_of_borrow_in_env=[" ++
    pp_sjoinmap_ary
      (fun i ->
        Pp.str (str_of_name_permissive (Context.Rel.Declaration.get_name (Environ.lookup_rel i env))) ++
        Pp.str "=>{" ++
        pp_sjoinmap_list
          (fun (ty,set) ->
            Printer.pr_constr_env env sigma ty ++ Pp.str ":{" ++
            pr_deBruijn_level_set env set ++ Pp.str "}")
          (ConstrMap.bindings (List.nth linear_vars_of_borrow_in_env (i-1))) ++
        Pp.str "}")
      (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
    Pp.str "]" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "/" +++ pp_sjoinmap_list (fun l -> Printer.pr_econstr_env env sigma (mkRel (Environ.nb_rel env - l))) vs +++
    Pp.str ":" +++ Printer.pr_econstr_env env sigma term_vs_ty);
  let (bused, lconsumed, bresult) = borrowcheck_expression1 env sigma original_linear_var_in_env linear_vars_of_borrow_in_env term vs term_vs_ty in
  (if not (IntSet.subset (lvariables_of_borrow bresult) (IntSet.diff (lvariables_of_borrow bused) lconsumed)) then
    user_err_hov (Pp.str "[codegen:bug] not (subset bresult (bused - lconsumed))"));
  msg_debug_hov (Pp.str "[codegen:borrowcheck_expression] return:" +++
    Pp.str "bused=" ++ pr_borrow env sigma bused +++
    Pp.str "lconsumed=" ++ pr_deBruijn_level_set env lconsumed +++
    Pp.str "bresult=" ++ pr_borrow env sigma bresult +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "/" +++ pp_sjoinmap_list (fun l -> Printer.pr_econstr_env env sigma (mkRel (Environ.nb_rel env - l))) vs +++
    Pp.str ":" +++ Printer.pr_econstr_env env sigma term_vs_ty);
  (bused, lconsumed, bresult)
and borrowcheck_expression1 (env : Environ.env) (sigma : Evd.evar_map)
    (original_linear_var_in_env : int option list) (linear_vars_of_borrow_in_env : borrow_t list)
    (term : EConstr.t) (vs : int list) (term_vs_ty : EConstr.types) : (borrow_t * IntSet.t * borrow_t) =
  let add_args_and_check (bresult : borrow_t) (lconsumed : IntSet.t) : borrow_t * IntSet.t =
    if CList.is_empty vs then
      (bresult, lconsumed)
    else if not (IntSet.is_empty lconsumed) then
      (* cannot reached? *)
      user_err_hov (Pp.str "[codegen] function cannot refer free linear variables:" +++ pr_deBruijn_level_set env lconsumed)
    else
      let linear_consumed_list =
        List.filter_map
          (fun l ->
            let i = Environ.nb_rel env - l in
            List.nth original_linear_var_in_env (i-1))
          vs
      in
      let linear_consumed = IntSet.of_list linear_consumed_list in
      let linear_used =
        List.fold_left
          (fun lvs l ->
            let i = Environ.nb_rel env - l in
            borrow_union
              lvs
              (List.nth linear_vars_of_borrow_in_env (i-1)))
          bresult vs
      in
      let duplicates = intlist_duplicates linear_consumed_list in
      if not (CList.is_empty duplicates) then
        user_err_hov (Pp.str "[codegen] linear variables used multiply in arguments:" +++
          pp_sjoinmap_list (pr_deBruijn_level env) duplicates)
      else if not (IntSet.disjoint linear_consumed (lvariables_of_borrow linear_used)) then
        (* We don't know how free variables of the function (term) and its arguments (vs) are used in term.
           So we determine its safety conservatively *)
        user_err_hov (Pp.str "[codegen] linear variable and its borrowed value are used both in an application:" +++ pr_deBruijn_level_set env (IntSet.inter linear_consumed (lvariables_of_borrow linear_used)))
      else
        (linear_used, linear_consumed)
  in
  let filter_result bresult =
    match component_types env sigma term_vs_ty with
    | None -> bresult
    | Some tyset ->
        ConstrMap.filter
          (fun ty set ->
            ConstrSet.mem ty tyset)
          bresult
  in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _
  | Sort _ | Prod _ | Ind _
  | CoFix _ | Array _
  | Cast _ | Int _ | Float _ ->
      user_err_hov (Pp.str "[codegen:borrowcheck_expression] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | App (f, argsary) ->
      borrowcheck_expression env sigma original_linear_var_in_env linear_vars_of_borrow_in_env
        f (List.append (CArray.map_to_list (fun rel -> Environ.nb_rel env - destRel sigma rel) argsary) vs)
        term_vs_ty
  | Rel i ->
      let bresult = List.nth linear_vars_of_borrow_in_env (i-1) in
      let lconsumed =
        match List.nth original_linear_var_in_env (i-1) with
        | Some l -> IntSet.singleton l
        | None -> IntSet.empty
      in
      if CList.is_empty vs then
        (bresult, lconsumed, bresult)
      else (* term is a function.  So term is not linear and lconsumed should be empty. *)
        let (bused', lconsumed') = add_args_and_check bresult lconsumed in
        (bused', lconsumed', filter_result bused')
  | Const (ctnt, univ) ->
      if Cset.mem ctnt !borrow_function_set then
        (assert (List.length vs = 1);
        let l = List.hd vs in (* the argument is a linear variable which we borrow it here *)
        let i = Environ.nb_rel env - l in
        let (_,_,ty) = destProd sigma (Retyping.get_type_of env sigma term) in
        let tys =
          match component_types env sigma ty with
          | None -> user_err_hov (Pp.str "[codegen] borrowed type contains a function:" +++ Printer.pr_econstr_env env sigma ty)
          | Some set -> List.filter (fun ty -> is_borrow_type env sigma (EConstr.of_constr ty)) (ConstrSet.elements set)
        in
        (*Context.Rel.Declaration.get_type (Environ.lookup_rel i env)*)
        let l =
          match List.nth original_linear_var_in_env (i-1) with
          | Some l' -> l'
          | None -> l
        in
        let bresult = borrow_of_list (List.map (fun ty -> (ty,l)) tys) in
        (bresult, IntSet.empty, bresult))
      else
        if CList.is_empty vs then
          (ConstrMap.empty, IntSet.empty, ConstrMap.empty)
        else
          let (bused', lconsumed') = add_args_and_check ConstrMap.empty IntSet.empty in
          (bused', lconsumed', filter_result bused')
  | Construct _ ->
      let (bused', lconsumed') = add_args_and_check ConstrMap.empty IntSet.empty in
      (* the return value of constructor application contains all arguments including the borrowed values *)
      (bused', lconsumed', bused')
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      if CList.is_empty vs then
        (* closure creation *)
        let bresult = borrowcheck_function env sigma original_linear_var_in_env linear_vars_of_borrow_in_env term in
        (bresult, IntSet.empty, bresult)
      else
        let env2 = EConstr.push_rec_types prec env in
        let original_linear_var_in_env' =
          CList.addn (Array.length fary) None original_linear_var_in_env
        in
        (* The fix-bounded functions, fary, may reference free borrowed variables but
           cannot reference free linear variables.
           So the free borrowed variables can be used freely in fary
           because the free linear variables are not consumed.
           Thus we don't need to set linear_vars_of_borrow_in_env' with the free borrowed variables.
           The free borrowed variables are collected by borrowcheck_function to bresults.
           Note that the arguments, vs, may reference the free linear variables.
           add_args_and_check verify (conservertively) the condition between sucn linear variables and bresults.
         *)
        let linear_vars_of_borrow_in_env' =
          CList.addn (Array.length fary) ConstrMap.empty linear_vars_of_borrow_in_env
        in
        let bresults = Array.map (borrowcheck_function env2 sigma original_linear_var_in_env' linear_vars_of_borrow_in_env') fary in
        let bresult = borrow_union_ary bresults in
        let (bused', lconsumed') = add_args_and_check bresult IntSet.empty in
        (bused', lconsumed', filter_result bused')

  | Lambda (x, ty, b) ->
      (match vs with
      | [] -> (* closure creation *)
          let bresult = borrowcheck_function env sigma original_linear_var_in_env linear_vars_of_borrow_in_env term in
          (bresult, IntSet.empty, bresult)
      | l :: rest_vs ->
          let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
          let env2 = EConstr.push_rel decl env in
          let i = Environ.nb_rel env - l in
          let original_linear_var_in_env' =
            List.nth original_linear_var_in_env (i-1) :: original_linear_var_in_env
          in
          let linear_vars_of_borrow_in_env' =
            List.nth linear_vars_of_borrow_in_env (i-1) :: linear_vars_of_borrow_in_env
          in
          borrowcheck_expression env2 sigma original_linear_var_in_env' linear_vars_of_borrow_in_env' b rest_vs term_vs_ty)

  | LetIn (x, e, ty, b) ->
      let e_ty = Retyping.get_type_of env sigma e in
      let (bused1, lconsumed1, bresult1) = borrowcheck_expression env sigma original_linear_var_in_env linear_vars_of_borrow_in_env e [] e_ty in
      let decl = Context.Rel.Declaration.LocalDef (x, e, ty) in
      let env2 = EConstr.push_rel decl env in
      let ty_is_linear = is_linear_type env sigma ty in
      let original_linear_var_in_env' =
        (if ty_is_linear then Some (Environ.nb_rel env) else None) :: original_linear_var_in_env
      in
      let linear_vars_of_borrow_in_env' = bresult1 :: linear_vars_of_borrow_in_env in
      let (bused2, lconsumed2, bresult2) = borrowcheck_expression env2 sigma original_linear_var_in_env' linear_vars_of_borrow_in_env' b vs term_vs_ty in
      if not (IntSet.disjoint lconsumed1 lconsumed2) then
        user_err_hov (Pp.str "[codegen] linear variables used multiply:" +++ pr_deBruijn_level_set env (IntSet.inter lconsumed1 lconsumed2))
      else if ty_is_linear && not (IntSet.mem (Environ.nb_rel env) lconsumed2) then
        user_err_hov (Pp.str "[codegen] linear variable not consumed:" +++ Pp.str (str_of_name (Context.binder_name x)))
      else if not (IntSet.disjoint lconsumed1 (lvariables_of_borrow bused2)) then
        user_err (Pp.str "[codegen] linear variable and its borrowed value are used inconsistently in let-in:" +++ pr_deBruijn_level_set env (IntSet.inter lconsumed1 (lvariables_of_borrow bused2)))
      else
        let bused0 = borrow_remove (Environ.nb_rel env) (borrow_union bused1 bused2) in
        let lconsumed0 = IntSet.remove (Environ.nb_rel env) (IntSet.union lconsumed1 lconsumed2) in
        let bresult0 = borrow_remove (Environ.nb_rel env) bresult2 in
        (bused0, lconsumed0, bresult0)

  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let item_ty = Retyping.get_type_of env sigma item in
      let (bused1, lconsumed1, bresult1) = borrowcheck_expression env sigma original_linear_var_in_env linear_vars_of_borrow_in_env item [] item_ty in
      let branch_results =
        Array.map2
          (fun (nas,body) (ctx,_) -> (* ctx is a list from inside declaration to outside declaration *)
            (*let env2 = EConstr.push_rel_context ctx env in*)
            let (env2,original_linear_var_in_env2,linear_vars_of_borrow_in_env2) =
              Context.Rel.fold_outside
                (fun decl (env1,original_linear_var_in_env1,linear_vars_of_borrow_in_env1) ->
                  let env1' = EConstr.push_rel decl env1 in
                  match decl with
                  | Context.Rel.Declaration.LocalAssum (x, ty) ->
                      let original_linear_var_in_env1' =
                        (if is_linear_type env1 sigma ty then
                          Some (Environ.nb_rel env1)
                        else
                          None) :: original_linear_var_in_env1
                      in
                      msg_debug_hov (Pp.str "[codegen:borrowcheck_expression] match constructor argument:" +++
                        Id.print (id_of_name (Context.binder_name x)) +++ Pp.str "is" +++
                        (if is_borrow_type env1 sigma ty then Pp.str "borrow" else Pp.str "not-borrowed"));
                      let linear_vars_of_borrow_in_env1' =
                        (if is_borrow_type env1 sigma ty then
                          List.nth linear_vars_of_borrow_in_env (destRel sigma item  - 1)
                        else
                          ConstrMap.empty) :: linear_vars_of_borrow_in_env1
                      in
                      (env1',original_linear_var_in_env1',linear_vars_of_borrow_in_env1')
                  | Context.Rel.Declaration.LocalDef (x, e, ty) ->
                      user_err_hov (Pp.str "[codegen] let-in in constructor type is not supported yet"))
                ctx ~init:(env,original_linear_var_in_env,linear_vars_of_borrow_in_env)
            in
            let (br_bused,br_lconsumed,br_bresult) = borrowcheck_expression env2 sigma original_linear_var_in_env2 linear_vars_of_borrow_in_env2 body vs term_vs_ty in
            let linear_args = IntSet.of_list (List.filter_map (fun opt -> opt) (CList.firstn (List.length ctx) original_linear_var_in_env2)) in
            let linear_consumed = IntSet.filter (fun l -> Environ.nb_rel env <= l) br_lconsumed in
            if not (IntSet.equal linear_args linear_consumed) then
              if IntSet.is_empty (IntSet.diff linear_consumed linear_args) then
                user_err_hov (Pp.str "[codegen] linear member not consumed:" +++
                  pr_deBruijn_level_set env2 (IntSet.diff linear_args linear_consumed))
              else
                user_err_hov (Pp.str "[codegen:bug] non-linear member consumed as linear variable:" +++
                  pr_deBruijn_level_set env2 (IntSet.diff linear_consumed linear_args))
            else
              (br_bresult,br_bused,br_lconsumed))
          bl bl0
      in
      let (_,_,br0_lconsumed) = branch_results.(0) in
      let br0_lconsumed = IntSet.filter (fun l -> l < Environ.nb_rel env) br0_lconsumed in
      if Array.exists (fun (_,_,br_lconsumed) -> not (IntSet.equal br0_lconsumed (IntSet.filter (fun l -> l < Environ.nb_rel env) br_lconsumed))) branch_results then
        let union = Array.fold_left (fun lconsumed (_,_,br_lconsumed) -> IntSet.union lconsumed br_lconsumed) IntSet.empty branch_results in
        let inter = Array.fold_left (fun lconsumed (_,_,br_lconsumed) -> IntSet.inter lconsumed br_lconsumed) br0_lconsumed branch_results in
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
                      (fun id (_,_,br_lconsumed) -> if IntSet.mem l br_lconsumed then Some id else None)
                      consnames branch_results))
              in
              pr_deBruijn_level env l +++ Pp.str "is used only for" +++
                pp_sjoinmap_list Id.print ids)
            (IntSet.elements (IntSet.diff union inter))
        in
        user_err_hov (Pp.str "[codegen] match-branches uses linear variables inconsistently:" +++
          pp_join_list (Pp.str "," ++ Pp.spc ()) msgs)
      else if not (IntSet.disjoint lconsumed1 br0_lconsumed) then
        user_err_hov (Pp.str "[codegen] linear match-item is used in match-branch:" +++
          pr_deBruijn_level_set env (IntSet.inter lconsumed1 br0_lconsumed))
      else
        let bresult2 = Array.fold_left (fun bresult (br_bresult,br_bused,br_lconsumed) -> borrow_union bresult br_bresult) ConstrMap.empty branch_results in
        let bused2 = Array.fold_left (fun bused (br_bresult,br_bused,br_lconsumed) -> borrow_union bused br_bused) ConstrMap.empty branch_results in
        let lconsumed2 = br0_lconsumed in
        if not (IntSet.disjoint lconsumed1 (lvariables_of_borrow bused2)) then
          user_err_hov (Pp.str "[codegen] linear variable and its borrowed value are used inconsistently in match:" +++ pr_deBruijn_level_set env (IntSet.inter lconsumed1 (lvariables_of_borrow bused2)))
        else
          (borrow_union bused1 bused2, IntSet.union lconsumed1 lconsumed2, borrow_union bresult1 bresult2)

  | Proj (proj, expr) ->
      if CList.is_empty vs then
        let expr_ty = Retyping.get_type_of env sigma expr in
        let (bused1, lconsumed1, bresult1) = borrowcheck_expression env sigma original_linear_var_in_env linear_vars_of_borrow_in_env expr [] expr_ty in
        let termty = Retyping.get_type_of env sigma term in
        if is_borrow_type env sigma termty then
          (bused1, lconsumed1, bresult1)
        else
          (bused1, lconsumed1, ConstrMap.empty)
      else
        user_err_hov (Pp.str "[codegen] the result of projection is a function")

let rec borrowcheck_constructor (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (args : EConstr.t list) : unit =
  let open Declarations in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _
  | Sort _ | Prod _ | Ind _
  | CoFix _ | Array _
  | Cast _ | Int _ | Float _ ->
      user_err_hov (Pp.str "[codegen:borrowcheck_constructor] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | App (f, argsary) ->
      borrowcheck_constructor env sigma f (List.append (Array.to_list argsary) args)
  | Rel _ -> ()
  | Const _ -> ()
  | Construct (cstr,univ) ->
      let (ind,j) = cstr in
      let (mutind,i) = ind in
      let mind_body = Environ.lookup_mind mutind env in
      let params = CList.firstn mind_body.mind_nparams args in
      let ty = mkApp (mkInd ind, Array.of_list params) in
      if is_borrow_type env sigma ty then
        user_err_hov (Pp.str "[codegen] constructor of borrow type used:" +++ Printer.pr_econstr_env env sigma term)

  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      Array.iter (fun f -> borrowcheck_constructor env2 sigma f []) fary

  | Lambda (x, ty, b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
      let env2 = EConstr.push_rel decl env in
      (match args with
      | [] -> (* closure creation *)
          borrowcheck_constructor env2 sigma b []
      | _ :: rest_args ->
          borrowcheck_constructor env2 sigma b rest_args)

  | LetIn (x, e, ty, b) ->
      borrowcheck_constructor env sigma e [];
      let decl = Context.Rel.Declaration.LocalDef (x, e, ty) in
      let env2 = EConstr.push_rel decl env in
      borrowcheck_constructor env2 sigma b args

  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      Array.iter2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          borrowcheck_constructor env2 sigma body args)
        bl bl0

  | Proj (proj, expr) ->
      borrowcheck_constructor env sigma expr []

let borrowcheck (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : unit =
  ignore (borrowcheck_function env sigma [] [] term);
  borrowcheck_constructor env sigma term []

let linear_type_check_single (libref : Libnames.qualid) : unit =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match gref with
  | ConstRef ctnt ->
      (let fctntu = Univ.in_punivs ctnt in
      let value_and_type = Environ.constant_value_and_type env fctntu in
      (match value_and_type with
      | (Some term, termty, uconstraints) ->
        let eterm = EConstr.of_constr term in
        linearcheck_function env sigma [] eterm;
        Feedback.msg_info (Pp.str "[codegen] linearity check passed:" +++ Printer.pr_constant env ctnt);
        ()
      | (_, _, _) -> user_err (Pp.str "[codegen] constant value couldn't obtained:" ++ Printer.pr_constant env ctnt)))
  | _ -> user_err (Pp.str "[codegen] not a constant reference:" +++ Printer.pr_global gref)


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
    match ConstrMap.find_opt ty !type_linearity_map with
    | Some LinearityIsLinear -> ()
    | Some LinearityIsUnrestricted -> user_err (Pp.str "[codegen] the linearity of the argument of borrow function is non-linear:" +++ Printer.pr_constr_env env sigma ty)
    | Some LinearityIsInvestigating -> user_err (Pp.str "[codegen:bug] LinearityIsInvestigating found")
    | None ->
        Feedback.msg_info (Pp.str "[codegen] linear type registered:" +++ Printer.pr_constr_env env sigma ty);
        type_linearity_map := ConstrMap.add ty LinearityIsLinear !type_linearity_map
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
      (let fctntu = Univ.in_punivs ctnt in
      let (ty, u) = Environ.constant_type env fctntu in
      let ty = nf_all env sigma (EConstr.of_constr ty) in
      let ty = EConstr.to_constr sigma ty in
      (match Constr.kind ty with
      | Prod (x, argty, retty) ->
          if not (Constr.isInd (fst (Constr.decompose_app argty))) then
            user_err (Pp.str "[codegen] CodeGen BorrowFunction needs a function which argument type is an inductive type:" +++ Printer.pr_constant env ctnt);
          if not (Constr.isInd (fst (Constr.decompose_app retty))) then
            user_err (Pp.str "[codegen] CodeGen BorrowFunction needs a function which return type is an inductive type:" +++ Printer.pr_constant env ctnt);
          set_borrow_function ctnt;
          set_linear env sigma argty;
          set_borrow_type env sigma retty
      | _ -> user_err (Pp.str "[codegen] CodeGen BorrowFunction needs a function:" +++ Printer.pr_constant env ctnt)))
  | _ -> user_err (Pp.str "[codegen] CodeGen BorrowFunction needs a constant reference:" +++ Printer.pr_global gref)

let command_linear_check (libref_list : Libnames.qualid list) : unit =
  List.iter linear_type_check_single libref_list

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

(* xxx test *)

let command_linear_test t1 t2 =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t1a) = Constrintern.interp_constr_evars env sigma t1 in
  let (sigma, t2a) = Constrintern.interp_constr_evars env sigma t2 in
  Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test t1:" +++ Printer.pr_econstr_env env sigma t1a);
  Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test t2:" +++ Printer.pr_econstr_env env sigma t2a);
  Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test is_conv:" +++ Pp.bool (Reductionops.is_conv env sigma t1a t2a));
  Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test is_conv_leq:" +++ Pp.bool (Reductionops.is_conv_leq env sigma t1a t2a));
  (match Reductionops.infer_conv env sigma t1a t2a with
  | Some _ -> Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test infer_conv succeed")
  | None -> Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test infer_conv failed"));
  (match Reductionops.infer_conv ~pb:Reduction.CONV env sigma t1a t2a with
  | Some _ -> Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test infer_conv(CONV) succeed")
  | None -> Feedback.msg_debug (Pp.str "[codegen] linear_type_check_test infer_conv(CONV) failed"))

let command_test_borrowcheck (term : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, term) = Constrintern.interp_constr_evars env sigma term in
  borrowcheck env sigma term


