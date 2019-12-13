open Globnames
open Pp
open CErrors
open Term
open EConstr

open Cgenutil
open State

let term_kind sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel _ -> "Rel"
  | Constr.Var _ -> "Var"
  | Constr.Meta _ -> "Meta"
  | Constr.Evar _ -> "Evar"
  | Constr.Sort _ -> "Sort"
  | Constr.Cast _ -> "Cast"
  | Constr.Prod _ -> "Prod"
  | Constr.Lambda _ -> "Lambda"
  | Constr.LetIn _ -> "LetIn"
  | Constr.App _ -> "App"
  | Constr.Const _ -> "Const"
  | Constr.Ind _ -> "Ind"
  | Constr.Construct _ -> "Construct"
  | Constr.Case _ -> "Case"
  | Constr.Fix _ -> "Fix"
  | Constr.CoFix _ -> "CoFix"
  | Constr.Proj _ -> "Proj"
  | Constr.Int _ -> "Int"

let whd_all env sigma term = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all env sigma term = Reductionops.nf_all env sigma term

let prod_appvect sigma c v = EConstr.of_constr (prod_appvect (EConstr.to_constr sigma c) (Array.map (EConstr.to_constr sigma) v))

let rec is_concrete_inductive_type env sigma term =
  let termty = Retyping.get_type_of env sigma term in
  (if isSort sigma termty then
    match EConstr.kind sigma term with
    | Constr.Ind _ -> true
    | Constr.App (f, argsary) ->
        isInd sigma f &&
        Array.for_all (is_concrete_inductive_type env sigma) argsary
    | _ -> false
  else
    false) (* "list" is not "concrete" inductive type because it has concrete parameter *)

let register_linear_type (ty : Constrexpr.constr_expr) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty2) = Constrintern.interp_constr_evars env sigma ty in
  let ty3 = ty2 in
  let ty4 = nf_all env sigma ty2 in
  (if not (is_concrete_inductive_type env sigma ty4) then
    user_err (str "codegen linear: concrete inductive type expected:" ++ spc () ++ Printer.pr_econstr_env env sigma ty4));
  type_linearity_list := (ty4, Linear) :: !type_linearity_list;
  Feedback.msg_info (str "codegen linear type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty3)

let rec is_registered_linear_type env sigma ty l =
  match l with
  | [] -> None
  | (k, linearity) :: rest ->
      if eq_constr sigma ty k then Some linearity else is_registered_linear_type env sigma ty rest

let type_of_inductive_arity mind_arity : Constr.t =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Constr.mkType (temp_arity : Declarations.template_arity).Declarations.template_level

let valid_type_param env sigma decl =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> isSort sigma (whd_all env sigma (EConstr.of_constr ty))
  | Context.Rel.Declaration.LocalDef _ -> false

let rec hasRel sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel i -> true
  | Constr.Var name -> false
  | Constr.Meta i -> false
  | Constr.Evar (ekey, termary) -> Array.exists (hasRel sigma) termary
  | Constr.Sort s -> false
  | Constr.Cast (expr, kind, ty) -> hasRel sigma expr || hasRel sigma ty
  | Constr.Prod (name, ty, body) -> hasRel sigma ty || hasRel sigma body
  | Constr.Lambda (name, ty, body) -> hasRel sigma ty || hasRel sigma body
  | Constr.LetIn (name, expr, ty, body) -> hasRel sigma expr || hasRel sigma ty || hasRel sigma body
  | Constr.App (f, argsary) -> hasRel sigma f || Array.exists (hasRel sigma) argsary
  | Constr.Const ctntu -> false
  | Constr.Ind iu -> false
  | Constr.Construct cstru -> false
  | Constr.Case (ci, tyf, expr, brs) -> hasRel sigma tyf || hasRel sigma expr || Array.exists (hasRel sigma) brs
  | Constr.Fix ((ia, i), (nameary, tyary, funary)) -> Array.exists (hasRel sigma) tyary || Array.exists (hasRel sigma) funary
  | Constr.CoFix (i, (nameary, tyary, funary)) -> Array.exists (hasRel sigma) tyary || Array.exists (hasRel sigma) funary
  | Constr.Proj (proj, expr) -> hasRel sigma expr
  | Constr.Int n -> false

let rec destProdX_rec sigma term =
  match EConstr.kind sigma term with
  | Constr.Prod (name, ty, body) ->
      let (names, tys, body) = destProdX_rec sigma body in
      (name :: names, ty :: tys, body)
  | _ -> ([], [], term)

let destProdX sigma term =
  let (names, tys, body) = destProdX_rec sigma term in
  (Array.of_list names, Array.of_list tys, body)

let rec is_linear_type env sigma ty =
  (*Feedback.msg_debug (str "is_linear_type:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match EConstr.kind sigma ty with
  | Constr.Prod (name, namety, body) ->
      ignore (is_linear_type env sigma namety);
      ignore (is_linear_type env sigma body);
      false (* function (closure) must not reference outside linear variables *)
  | Constr.Ind iu -> is_linear_app env sigma ty ty [| |]
  | Constr.App (f, argsary) -> is_linear_app env sigma ty f argsary
  | _ -> user_err (str "is_linear_type: unexpected term:" ++ spc () ++ Printer.pr_econstr_env env sigma ty)
and is_linear_app env sigma ty f argsary =
  (*Feedback.msg_debug (str "is_linear_app:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match is_registered_linear_type env sigma ty !type_linearity_list with
  | Some Linear -> true
  | Some Unrestricted -> false
  | Some Investigating -> false
  | None ->
      (type_linearity_list := (ty, Investigating) :: !type_linearity_list;
      if isInd sigma f then
        if is_linear_ind env sigma ty (destInd sigma f) argsary then
          (Feedback.msg_info (str "codegen linear type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty);
          type_linearity_list := (ty, Linear) :: !type_linearity_list; true)
        else
          (Feedback.msg_info (str "codegen unrestricted type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty);
          type_linearity_list := (ty, Unrestricted) :: !type_linearity_list; false)
      else
        user_err (str "is_linear_app: unexpected type application:" ++ spc () ++ Printer.pr_econstr_env env sigma f))
and is_linear_ind env sigma ty ie argsary =
  (*Feedback.msg_debug (str "is_linear_ind:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  let ((mutind, i), _) = ie in (* strip EInstance.t *)
  let mind_body = Environ.lookup_mind mutind env in
  if mind_body.Declarations.mind_nparams <> mind_body.Declarations.mind_nparams_rec then
    user_err (str "is_linear_ind: non-uniform inductive type:" ++ spc () ++ Printer.pr_econstr_env env sigma (mkIndU ie))
  else if not (List.for_all (valid_type_param env sigma) mind_body.Declarations.mind_params_ctxt) then
    user_err (str "is_linear_ind: non-sort type binder:" ++ spc () ++ Printer.pr_econstr_env env sigma (mkIndU ie))
  else
    let ind_ary = Array.map (fun j -> Constr.mkInd (mutind, j))
        (iota_ary 0 (Array.length mind_body.Declarations.mind_packets)) in
    let env = Environ.push_rel_context (
        List.map (fun j ->
          let oind_body = mind_body.Declarations.mind_packets.(Array.length mind_body.Declarations.mind_packets - j - 1) in
          Context.Rel.Declaration.LocalDef
            (Context.annotR (Names.Name.Name oind_body.Declarations.mind_typename),
             ind_ary.(j),
             type_of_inductive_arity oind_body.Declarations.mind_arity))
          (iota_list 0 (Array.length mind_body.Declarations.mind_packets))
      ) env in
    let oind_body = mind_body.Declarations.mind_packets.(i) in
    let cons_is_linear = Array.map
      (fun user_lc ->
        (*Feedback.msg_debug (str "user_lc1:" ++ str (term_kind sigma user_lc) ++ str ":" ++ Printer.pr_econstr_env env sigma user_lc);*)
        let user_lc = nf_all env sigma (prod_appvect sigma user_lc argsary) in (* apply type arguments *)
        (*Feedback.msg_debug (str "user_lc2:" ++ str (term_kind sigma user_lc) ++ str ":" ++ Printer.pr_econstr_env env sigma user_lc);*)
        (if hasRel sigma user_lc then
          user_err (str "is_linear_ind: constractor type has has local reference:" ++ spc () ++ Printer.pr_econstr_env env sigma user_lc));
        (* cparam_tys and body can be interpreted under env because they have no Rel *)
        let (cparam_names, cparam_tys, body) = destProdX sigma user_lc in
        (if not (eq_constr sigma body ty) then
          user_err (str "unexpected constructor body type:" ++ spc () ++ Printer.pr_econstr_env env sigma body ++ spc () ++ str (term_kind sigma body)));
        (if Array.exists (isSort sigma) cparam_tys then
          user_err (str "is_linear_ind: constractor has type argument"));
        let consarg_is_linear = Array.map (is_linear_type env sigma) cparam_tys in
        Array.mem true consarg_is_linear)
      (Array.map EConstr.of_constr oind_body.Declarations.mind_user_lc) in
    Array.mem true cons_is_linear

let is_linear env sigma ty =
  (*Feedback.msg_debug (str "is_linear:argument:" ++ Printer.pr_econstr_env env sigma ty);*)
  let ty2 = nf_all env sigma ty in
  is_linear_type env sigma ty2

let check_type_linearity env sigma ty =
  ignore (is_linear env sigma ty)

let rec copy_linear_refs linear_refs =
  match linear_refs with
  | [] -> []
  | None :: rest -> None :: copy_linear_refs rest
  | Some r :: rest -> Some (ref !r) :: copy_linear_refs rest

let rec eq_linear_refs linear_refs1 linear_refs2 =
  match linear_refs1, linear_refs2 with
  | [], [] -> true
  | (None :: rest1), (None :: rest2) -> eq_linear_refs rest1 rest2
  | (Some r1 :: rest1), (Some r2 :: rest2) -> !r1 = !r2 && eq_linear_refs rest1 rest2
  | _, _ -> raise (CodeGenError "inconsistent linear_refs")

let rec update_linear_refs dst_linear_refs src_linear_refs =
  match dst_linear_refs, src_linear_refs with
  | [], [] -> ()
  | (None :: rest1), (None :: rest2) -> update_linear_refs rest1 rest2
  | (Some r1 :: rest1), (Some r2 :: rest2) -> (r1 := !r2; update_linear_refs rest1 rest2)
  | _, _ -> raise (CodeGenError "inconsistent linear_refs")

let update_linear_refs_for_case linear_refs_ary dst_linear_refs =
  Array.iter (fun linear_ref ->
    if not (eq_linear_refs linear_refs_ary.(0) linear_ref) then
      raise (CodeGenError "inconsistent linear variable use in match branches"))
    linear_refs_ary;
  update_linear_refs dst_linear_refs linear_refs_ary.(0)

let push_rec_types env sigma (nameary,tyary,funary) =
  let to_constr = EConstr.to_constr sigma in
  Environ.push_rec_types (nameary, Array.map to_constr tyary, Array.map to_constr funary) env

let rec ntimes n f v =
  if n = 0 then
    v
  else
    ntimes (n-1) f (f v)

let string_of_name name =
  match name with
  | Names.Name.Name id -> Names.Id.to_string id
  | Names.Name.Anonymous -> "_"

let name_of_decl decl =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> name
  | Context.Rel.Declaration.LocalDef (name, expr, ty) -> name

let ty_of_decl decl =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> ty
  | Context.Rel.Declaration.LocalDef (name, expr, ty) -> ty

let with_local_var env sigma decl linear_refs num_innermost_locals f =
  let env2 = EConstr.push_rel decl env in
  let name = name_of_decl decl in
  let ty = ty_of_decl decl in
  let num_innermost_locals2 = num_innermost_locals+1 in
  if not (is_linear env sigma ty) then
    f env2 (None :: linear_refs) num_innermost_locals2
  else
    let r = ref 0 in
    let linear_refs2 = Some r :: linear_refs in
    f env2 linear_refs2 num_innermost_locals2;
    if !r <> 1 then
      user_err (str "linear var not lineary used:" ++ spc () ++ Names.Name.print (Context.binder_name name) ++ spc () ++ str "(" ++ int !r ++ spc () ++ str "times used)")
    else
      ()

let rec check_outermost_lambdas env sigma linear_refs num_innermost_locals term =
  ((*Feedback.msg_debug (str "check_outermost_lambdas:" ++ spc() ++ Printer.pr_econstr_env env sigma term);*)
  match EConstr.kind sigma term with
  | Constr.Lambda (name, ty, body) ->
      (check_type_linearity env sigma ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      with_local_var env sigma decl linear_refs num_innermost_locals
        (fun env2 linear_refs2 num_innermost_locals2 -> check_outermost_lambdas env2 sigma linear_refs2 num_innermost_locals2 body))
  | _ -> check_linear_valexp env sigma linear_refs num_innermost_locals term)
and check_linear_valexp env sigma linear_refs num_innermost_locals term =
  ((*Feedback.msg_debug (str "check_linear_valexp:" ++ spc() ++ Printer.pr_econstr_env env sigma term);*)
  let termty = Retyping.get_type_of env sigma term in
  match EConstr.kind sigma term with
  | Constr.Rel i ->
      (match List.nth linear_refs (i-1) with
      | None -> () (* usual (non-linear) variable *)
      | Some cell ->
          (* linear variable *)
          if i <= num_innermost_locals then
            if !cell = 0 then
              cell := 1
            else
              user_err (str "second reference to a linear variable:" ++ spc () ++ Printer.pr_econstr_env env sigma term)
          else
            user_err (str "linear variable reference outside of a function:" ++ spc () ++ Printer.pr_econstr_env env sigma term))
  | Constr.Var name -> ()
  | Constr.Meta i -> ()
  | Constr.Evar (ekey, termary) -> ()
  | Constr.Sort s -> ()
  | Constr.Cast (expr, kind, ty) ->
      (check_type_linearity env sigma ty;
      check_linear_valexp env sigma linear_refs num_innermost_locals expr)
  | Constr.Prod (name, ty, body) ->
      check_type_linearity env sigma term
  | Constr.Lambda (name, ty, body) ->
      check_outermost_lambdas env sigma linear_refs 0 term
  | Constr.LetIn (name, expr, ty, body) ->
      (check_type_linearity env sigma ty;
      check_linear_valexp env sigma linear_refs num_innermost_locals expr;
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      with_local_var env sigma decl linear_refs num_innermost_locals
        (fun env2 linear_refs2 num_innermost_locals2 -> check_linear_valexp env2 sigma linear_refs2 num_innermost_locals2 body))
  | Constr.App (f, argsary) ->
      (check_linear_valexp env sigma linear_refs num_innermost_locals f;
      Array.iter (check_linear_valexp env sigma linear_refs num_innermost_locals) argsary;
      if Array.exists (fun arg -> let ty = Retyping.get_type_of env sigma arg in
                       is_linear env sigma ty) argsary &&
         isProd sigma termty then
        user_err (str "application with linear argument cannot return function value:" ++ spc () ++ Printer.pr_econstr_env env sigma term))
  | Constr.Const ctntu -> ()
  | Constr.Ind iu -> ()
  | Constr.Construct cstru -> ()
  | Constr.Case (ci, tyf, expr, brs) ->
      ((* tyf is not checked because it is not a target of code generation.
          check tyf is (fun _ -> termty) ? *)
      check_linear_valexp env sigma linear_refs num_innermost_locals expr;
      let linear_refs_ary = Array.map (fun _ -> copy_linear_refs linear_refs) brs in
      let f linear_refs cstr_nargs br = check_case_branch env sigma linear_refs num_innermost_locals cstr_nargs br in
      array_iter3 f linear_refs_ary ci.Constr.ci_cstr_nargs brs;
      update_linear_refs_for_case linear_refs_ary linear_refs)
  | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
      (let n = Array.length funary in
      let env2 = push_rec_types env sigma (nameary, tyary, funary) in
      let linear_refs2 = ntimes n (List.cons None) linear_refs in
      Array.iter (check_type_linearity env sigma) tyary;
      Array.iter (check_linear_valexp env2 sigma linear_refs2 0) funary)
  | Constr.CoFix (i, (nameary, tyary, funary)) ->
      (let n = Array.length funary in
      let env2 = push_rec_types env sigma (nameary, tyary, funary) in
      let linear_refs2 = ntimes n (List.cons None) linear_refs in
      Array.iter (check_type_linearity env sigma) tyary;
      Array.iter (check_linear_valexp env2 sigma linear_refs2 0) funary)
  | Constr.Proj (proj, expr) ->
      check_linear_valexp env sigma linear_refs num_innermost_locals expr
  | Constr.Int n -> ())
and check_case_branch env sigma linear_refs num_innermost_locals cstr_nargs br =
  if cstr_nargs = 0 then
    check_linear_valexp env sigma linear_refs num_innermost_locals br
  else
    (match EConstr.kind sigma br with
    | Constr.Lambda (name, ty, body) ->
        (check_type_linearity env sigma ty;
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        with_local_var env sigma decl linear_refs num_innermost_locals
          (fun env2 linear_refs2 num_innermost_locals2 -> check_case_branch env2 sigma linear_refs2 num_innermost_locals2 (cstr_nargs-1) body))
    | _ ->
      user_err (str "unexpected non-Lambda in a case branch")) (* should eta-expansion? *)

let linear_type_check_term term =
  if !type_linearity_list <> [] then
    (let env = Global.env () in
    let sigma = Evd.from_env env in
    let eterm = EConstr.of_constr term in
    check_linear_valexp env sigma [] 0 eterm)

let linear_type_check_single libref =
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
        check_linear_valexp env sigma [] 0 eterm;
        Feedback.msg_info (str "codegen linearity check passed:" ++ spc() ++ Printer.pr_constant env ctnt);
        ()
      | _ -> user_err (str "constant value couldn't obtained:" ++ Printer.pr_constant env ctnt)))
  | _ -> user_err (str "not constant")

let linear_type_check_list libref_list =
  List.iter linear_type_check_single libref_list

(* xxx test *)

let linear_type_check_test t1 t2 =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t1a) = Constrintern.interp_constr_evars env sigma t1 in
  let (sigma, t2a) = Constrintern.interp_constr_evars env sigma t2 in
  Feedback.msg_debug (str "linear_type_check_test t1:" ++ spc() ++ Printer.pr_econstr_env env sigma t1a);
  Feedback.msg_debug (str "linear_type_check_test t2:" ++ spc() ++ Printer.pr_econstr_env env sigma t2a);
  Feedback.msg_debug (str "linear_type_check_test is_conv:" ++ spc() ++ bool (Reductionops.is_conv env sigma t1a t2a));
  Feedback.msg_debug (str "linear_type_check_test is_conv_leq:" ++ spc() ++ bool (Reductionops.is_conv_leq env sigma t1a t2a));
  (match Reductionops.infer_conv env sigma t1a t2a with
  | Some _ -> Feedback.msg_debug (str "linear_type_check_test infer_conv succeed")
  | None -> Feedback.msg_debug (str "linear_type_check_test infer_conv failed"));
  (match Reductionops.infer_conv ~pb:Reduction.CONV env sigma t1a t2a with
  | Some _ -> Feedback.msg_debug (str "linear_type_check_test infer_conv(CONV) succeed")
  | None -> Feedback.msg_debug (str "linear_type_check_test infer_conv(CONV) failed"))


