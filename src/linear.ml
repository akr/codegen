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

let type_of_inductive_arity (mind_arity : (Declarations.regular_inductive_arity, Declarations.template_arity) Declarations.declaration_arity) : Constr.t =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Constr.mkType (temp_arity : Declarations.template_arity).Declarations.template_level

let valid_type_param (env : Environ.env) (sigma : Evd.evar_map) (decl : Constr.rel_declaration) : bool =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> isSort sigma (whd_all env sigma (EConstr.of_constr ty))
  | Context.Rel.Declaration.LocalDef _ -> false

let rec hasRel (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool =
  match EConstr.kind sigma term with
  | Rel i -> true
  | Var name -> false
  | Meta i -> false
  | Evar (ekey, terms) -> List.exists (hasRel env sigma) terms
  | Sort s -> false
  | Cast (expr, kind, ty) -> hasRel env sigma expr || hasRel env sigma ty
  | Prod (name, ty, body) -> hasRel env sigma ty ||
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      hasRel env2 sigma body
  | Lambda (name, ty, body) -> hasRel env sigma ty ||
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      hasRel env2 sigma body
  | LetIn (name, expr, ty, body) -> hasRel env sigma expr || hasRel env sigma ty ||
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = EConstr.push_rel decl env in
      hasRel env2 sigma body
  | App (f, argsary) -> hasRel env sigma f || Array.exists (hasRel env sigma) argsary
  | Const ctntu -> false
  | Ind iu -> false
  | Construct cstru -> false
  | Case (ci,u,pms,p,iv,c,bl) ->
      let (ci, tyf, iv, expr, brs) = EConstr.expand_case env sigma (ci,u,pms,p,iv,c,bl) in
      hasRel env sigma tyf || hasRel env sigma expr || Array.exists (hasRel env sigma) brs
  | Fix ((ks, j), ((nary, tary, fary) as prec)) -> Array.exists (hasRel env sigma) tary ||
      let env2 = push_rec_types prec env in
      Array.exists (hasRel env2 sigma) fary
  | CoFix (i, ((nary, tary, fary) as prec)) -> Array.exists (hasRel env sigma) tary ||
      let env2 = push_rec_types prec env in
      Array.exists (hasRel env2 sigma) fary
  | Proj (proj, expr) -> hasRel env sigma expr
  | Int n -> false
  | Float n -> false
  | Array (u,t,def,ty) -> Array.exists (hasRel env sigma) t || hasRel env sigma def || hasRel env sigma ty

let ind_nflc_iter (env : Environ.env) (sigma : Evd.evar_map) (ind : inductive) (argsary : EConstr.t array) (f : Environ.env -> Id.t -> EConstr.t array -> Id.t -> (Constr.rel_context * Constr.types) -> unit) : unit =
  (*Feedback.msg_debug (Pp.str "[codegen:ind_nflc_iter] ind:" +++ Printer.pr_inductive env ind);
  for i = 0 to Array.length argsary - 1 do
    Feedback.msg_debug (Pp.str "[codegen:ind_nflc_iter] argsary[" ++ Pp.int i ++ Pp.str "]:" +++ Printer.pr_econstr_env env sigma argsary.(i))
  done;*)
  let (mutind, i) = ind in
  let mind_body = Environ.lookup_mind mutind env in
  if mind_body.Declarations.mind_nparams <> mind_body.Declarations.mind_nparams_rec then
    user_err (Pp.str "[codegen] is_linear_ind: non-uniform inductive type:" +++ Printer.pr_inductive env ind);
  if mind_body.Declarations.mind_nparams <> Array.length argsary then
    user_err (Pp.str "[codegen] is_linear_ind: indexed types not supported:" +++ Printer.pr_inductive env ind +++
              Pp.hv 0 (
                Pp.str "(" ++ Pp.int mind_body.Declarations.mind_nparams +++ Pp.str "arguments expected but" +++
                Pp.int (Array.length argsary) +++ Pp.str "given)"));
  if not (List.for_all (valid_type_param env sigma) mind_body.Declarations.mind_params_ctxt) then
    user_err (Pp.str "[codegen] is_linear_ind: non-type parameter:" +++ Printer.pr_inductive env ind);
  let ind_ary = Array.map (fun j -> Constr.mkInd (mutind, j))
      (iota_ary 0 (Array.length mind_body.Declarations.mind_packets)) in
  let params = Array.sub argsary 0 mind_body.Declarations.mind_nparams in
  let env = Environ.push_rel_context (
      List.map (fun ii0 ->
        let oind_body = mind_body.Declarations.mind_packets.(Array.length mind_body.Declarations.mind_packets - ii0 - 1) in
        Context.Rel.Declaration.LocalDef
          (Context.annotR (Names.Name.Name oind_body.Declarations.mind_typename),
           ind_ary.(Array.length mind_body.Declarations.mind_packets - ii0 - 1),
           type_of_inductive_arity oind_body.Declarations.mind_arity))
        (iota_list 0 (Array.length mind_body.Declarations.mind_packets))
    ) env in
  Array.iter
    (fun oind_body ->
      Array.iter2 (f env oind_body.Declarations.mind_typename params)
        oind_body.Declarations.mind_consnames oind_body.Declarations.mind_nf_lc)
    mind_body.Declarations.mind_packets

let nflc_carg_iter (env : Environ.env) (sigma : Evd.evar_map) (params : EConstr.t array) (nf_lc : Constr.rel_context * Constr.types) (f : Environ.env -> Constr.types -> unit) : unit =
  let ((ctx : Constr.rel_context), (t : Constr.t)) = nf_lc in
  (*for i = 0 to Array.length params - 1 do
    Feedback.msg_debug (Pp.str "[codegen:nflc_carg_iter] params[" ++ Pp.int i ++ Pp.str "]:" +++ Printer.pr_econstr_env env sigma params.(i))
  done;
  Feedback.msg_debug (Pp.str "[codegen:nflc_carg_iter] context:" +++ Printer.pr_rel_context env sigma ctx +++
                      Pp.str "type:" +++ Printer.pr_type_env (Environ.push_rel_context ctx env) sigma t);*)
  (* ctx is a list from inside declaration to outside declaration *)
  let env = ref env in
  let params = ref (CArray.map_to_list (EConstr.to_constr sigma) params) in
  List.iter
    (fun decl ->
      (*Feedback.msg_debug (Pp.str "[codegen:nflc_carg_iter] decl:" +++ Printer.pr_rel_decl !env sigma decl);*)
      match decl with
      | Context.Rel.Declaration.LocalDef (name, expr, ty) ->
          env := Environ.push_rel decl !env
      | Context.Rel.Declaration.LocalAssum (name, ty) ->
          (match !params with
          | param :: rest ->
              params := rest;
              env := Environ.push_rel (Context.Rel.Declaration.LocalDef (name, param, ty)) !env
          | [] ->
              f !env ty;
              env := Environ.push_rel decl !env))
    (List.rev ctx)

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
        (Feedback.msg_info (Pp.str "[codegen] Unrestricted type registered:" +++ Printer.pr_econstr_env env sigma ty);
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
      if hasRel env sigma arg then (* hasRel is too strong.  No free variables is enough *)
        user_err (Pp.str "[codegen] is_linear_ind: constructor type has has local reference:" +++ Printer.pr_econstr_env env sigma arg))
    argsary;
  let exception FoundLinear in
  try
    ind_nflc_iter env sigma (fst (destInd sigma ind_f)) argsary
      (fun env ind_id params cstr_id nf_lc ->
        (*Feedback.msg_debug (Pp.str "[codegen:is_linear_ind] ind_nflc_iter calls with ind=" ++ Id.print ind_id +++ Pp.str "cstr=" ++ Id.print cstr_id);*)
        let nbrel_until_ind = Environ.nb_rel env in
        nflc_carg_iter env sigma params nf_lc
          (fun env argty ->
            let argty = EConstr.of_constr argty in
            (*Feedback.msg_debug (Pp.str "[codegen:is_linear_ind] argty=" ++ Printer.pr_econstr_env env sigma argty +++ Pp.str "argty_type=" ++ Pp.str (constr_name sigma argty));*)
            match EConstr.kind sigma argty with
            | Rel i ->
                (* Since nf_lc is a head normalized constructor types,
                  Rel is only used for recursive references of inductive types or
                  references to earlier declarations in nf_lc (this contains inductive type parameters).  *)
                if i <= Environ.nb_rel env - nbrel_until_ind then (* references to earlier declarations *)
                  if is_linear_type env sigma (whd_all env sigma argty) then raise FoundLinear
            | App (f, args) when isRel sigma f ->
                (* Same as above Rel *)
                let i = destRel sigma f in
                if i <= Environ.nb_rel env - nbrel_until_ind then (* references to earlier declarations *)
                  if is_linear_type env sigma (whd_all env sigma argty) then raise FoundLinear
            | Sort _ ->
                user_err (Pp.str "[codegen] is_linear_ind: constructor has type argument")
            | Prod (x, ty, b) ->
                (* function type argument of a constructor is non-linear or non-code-generatable *)
                ()
            | Ind (ind, univ) ->
                if is_linear_type env sigma argty then raise FoundLinear
            | App (f, args) when isInd sigma f ->
                if is_linear_type env sigma argty then raise FoundLinear
            | _ ->
                user_err (Pp.str "[codegen:is_linear_ind] unexpected constructor argument:" +++ Printer.pr_econstr_env env sigma argty)));
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
      | _ -> user_err (Pp.str "[codegen] constant value couldn't obtained:" ++ Printer.pr_constant env ctnt)))
      | _ -> user_err (Pp.str "[codegen] not constant")

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


