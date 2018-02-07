open Globnames
open Pp
open CErrors
open Term
open EConstr

open Cgenutil

let term_kind sigma term =
  match EConstr.kind sigma term with
  | Rel _ -> "Rel"
  | Var _ -> "Var"
  | Meta _ -> "Meta"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast _ -> "Cast"
  | Prod _ -> "Prod"
  | Lambda _ -> "Lambda"
  | LetIn _ -> "LetIn"
  | App _ -> "App"
  | Const _ -> "Const"
  | Ind _ -> "Ind"
  | Construct _ -> "Construct"
  | Case _ -> "Case"
  | Fix _ -> "Fix"
  | CoFix _ -> "CoFix"
  | Proj _ -> "Proj"

let whd_all env sigma term = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all env sigma term = Reductionops.nf_all env sigma term

let prod_appvect sigma c v = EConstr.of_constr (prod_appvect (EConstr.to_constr sigma c) (Array.map (EConstr.to_constr sigma) v))

type type_linearity = Linear | Pure | Investigating

let type_linearity_list_empty : (t * type_linearity) list = []

let type_linearity_list = Summary.ref type_linearity_list_empty ~name:"CodeGenLinearTypeList"

let register_linear_type (ty : Constrexpr.constr_expr) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (ty2, euc) = Constrintern.interp_constr env sigma ty in
  let ty3 = EConstr.of_constr ty2 in
  let ty4 = nf_all env sigma (EConstr.of_constr ty2) in
  type_linearity_list := (ty4, Linear) :: !type_linearity_list;
  Feedback.msg_info (str "codegen linear type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty3)

let rec is_registered_linear_type env sigma ty l =
  match l with
  | [] -> None
  | (k, linearity) :: rest ->
      if eq_constr sigma ty k then Some linearity else is_registered_linear_type env sigma ty rest

let type_of_inductive_arity mind_arity : Term.constr =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Term.mkSort (Sorts.Type (temp_arity : Declarations.template_arity).Declarations.template_level)

let valid_type_param env sigma decl =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> isSort sigma (whd_all env sigma (EConstr.of_constr ty))
  | Context.Rel.Declaration.LocalDef _ -> false

let rec hasRel sigma term =
  match EConstr.kind sigma term with
  | Rel i -> true
  | Var name -> false
  | Meta i -> false
  | Evar (ekey, termary) -> Array.exists (hasRel sigma) termary
  | Sort s -> false
  | Cast (expr, kind, ty) -> hasRel sigma expr || hasRel sigma ty
  | Prod (name, ty, body) -> hasRel sigma ty || hasRel sigma body
  | Lambda (name, ty, body) -> hasRel sigma ty || hasRel sigma body
  | LetIn (name, expr, ty, body) -> hasRel sigma expr || hasRel sigma ty || hasRel sigma body
  | App (f, argsary) -> hasRel sigma f || Array.exists (hasRel sigma) argsary
  | Const ctntu -> false
  | Ind iu -> false
  | Construct cstru -> false
  | Case (ci, tyf, expr, brs) -> hasRel sigma tyf || hasRel sigma expr || Array.exists (hasRel sigma) brs
  | Fix ((ia, i), (nameary, tyary, funary)) -> Array.exists (hasRel sigma) tyary || Array.exists (hasRel sigma) funary
  | CoFix (i, (nameary, tyary, funary)) -> Array.exists (hasRel sigma) tyary || Array.exists (hasRel sigma) funary
  | Proj (proj, expr) -> hasRel sigma expr

let rec destProdX_rec sigma term =
  match EConstr.kind sigma term with
  | Prod (name, ty, body) ->
      let (names, tys, body) = destProdX_rec sigma body in
      (name :: names, ty :: tys, body)
  | _ -> ([], [], term)

let destProdX sigma term =
  let (names, tys, body) = destProdX_rec sigma term in
  (Array.of_list names, Array.of_list tys, body)

let rec is_linear_type env sigma ty =
  (*Feedback.msg_debug (str "is_linear_type:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match EConstr.kind sigma ty with
  | Prod (name, namety, body) ->
      is_linear_type env sigma namety;
      is_linear_type env sigma body;
      false (* function (closure) must not reference outside linear variables *)
  | Ind iu -> is_linear_app env sigma ty ty [| |]
  | App (f, argsary) -> is_linear_app env sigma ty f argsary
  | _ -> user_err (str "is_linear_type: unexpected term:" ++ spc () ++ Printer.pr_econstr_env env sigma ty)
and is_linear_app env sigma ty f argsary =
  (*Feedback.msg_debug (str "is_linear_app:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match is_registered_linear_type env sigma ty !type_linearity_list with
  | Some Linear -> true
  | Some Pure -> false
  | Some Investigating -> false
  | None ->
      (type_linearity_list := (ty, Investigating) :: !type_linearity_list;
      if isInd sigma f then
        if is_linear_ind env sigma ty (destInd sigma f) argsary then
          (Feedback.msg_info (str "codegen linear type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty);
          type_linearity_list := (ty, Linear) :: !type_linearity_list; true)
        else
          (Feedback.msg_info (str "codegen pure type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty);
          type_linearity_list := (ty, Pure) :: !type_linearity_list; false)
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
    let ind_ary = Array.map (fun j -> Term.mkInd (mutind, j))
        (iota_ary 0 (Array.length mind_body.Declarations.mind_packets)) in
    let env = Environ.push_rel_context (
        List.map (fun j ->
          let oind_body = mind_body.Declarations.mind_packets.(Array.length mind_body.Declarations.mind_packets - j - 1) in
          Context.Rel.Declaration.LocalDef
            (Names.Name.Name oind_body.Declarations.mind_typename,
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

let with_local_var env evdref decl linear_refs num_innermost_locals f =
  let env2 = EConstr.push_rel decl env in
  let name = name_of_decl decl in
  let ty = ty_of_decl decl in
  let num_innermost_locals2 = num_innermost_locals+1 in
  if not (is_linear env !evdref ty) then
    f env2 (None :: linear_refs) num_innermost_locals2
  else
    let r = ref 0 in
    let linear_refs2 = Some r :: linear_refs in
    f env2 linear_refs2 num_innermost_locals2;
    if !r <> 1 then
      user_err (str "linear var not lineary used:" ++ spc () ++ Names.Name.print name ++ spc () ++ str "(" ++ int !r ++ spc () ++ str "times used)")
    else
      ()

let rec check_outermost_lambdas env evdref linear_refs num_innermost_locals term =
  ((*Feedback.msg_debug (str "check_outermost_lambdas:" ++ spc() ++ Printer.pr_econstr_env env !evdref term);*)
  match EConstr.kind !evdref term with
  | Lambda (name, ty, body) ->
      (check_type_linearity env !evdref ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      with_local_var env evdref decl linear_refs num_innermost_locals
        (fun env2 linear_refs2 num_innermost_locals2 -> check_outermost_lambdas env2 evdref linear_refs2 num_innermost_locals2 body))
  | _ -> check_linear_valexp env evdref linear_refs num_innermost_locals term)
and check_linear_valexp env evdref linear_refs num_innermost_locals term =
  ((*Feedback.msg_debug (str "check_linear_valexp:" ++ spc() ++ Printer.pr_econstr_env env !evdref term);*)
  let termty = Typing.e_type_of env evdref term in
  match EConstr.kind !evdref term with
  | Rel i ->
      (match List.nth linear_refs (i-1) with
      | None -> () (* usual (non-linear) variable *)
      | Some cell ->
          (* linear variable *)
          if i <= num_innermost_locals then
            if !cell = 0 then
              cell := 1
            else
              user_err (str "second reference to a linear variable:" ++ spc () ++ Printer.pr_econstr_env env !evdref term)
          else
            user_err (str "linear variable reference outside of a function:" ++ spc () ++ Printer.pr_econstr_env env !evdref term))
  | Var name -> ()
  | Meta i -> ()
  | Evar (ekey, termary) -> ()
  | Sort s -> ()
  | Cast (expr, kind, ty) ->
      (check_type_linearity env !evdref ty;
      check_linear_exp env evdref linear_refs num_innermost_locals expr)
  | Prod (name, ty, body) ->
      check_type_linearity env !evdref term
  | Lambda (name, ty, body) ->
      check_outermost_lambdas env evdref linear_refs 0 term
  | LetIn (name, expr, ty, body) ->
      (check_type_linearity env !evdref ty;
      check_linear_exp env evdref linear_refs num_innermost_locals expr;
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      with_local_var env evdref decl linear_refs num_innermost_locals
        (fun env2 linear_refs2 num_innermost_locals2 -> check_linear_exp env2 evdref linear_refs2 num_innermost_locals2 body))
  | App (f, argsary) ->
      (check_linear_exp env evdref linear_refs num_innermost_locals f;
      Array.iter (check_linear_exp env evdref linear_refs num_innermost_locals) argsary;
      if Array.exists (fun arg -> is_linear env !evdref (Typing.e_type_of env evdref arg)) argsary &&
         isProd !evdref termty then
        user_err (str "application with linear argument cannot return function value:" ++ spc () ++ Printer.pr_econstr_env env !evdref term))
  | Const ctntu -> ()
  | Ind iu -> ()
  | Construct cstru -> ()
  | Case (ci, tyf, expr, brs) ->
      ((* check_linear_exp env evdref linear_refs num_innermost_locals tyf; *)
      check_linear_exp env evdref linear_refs num_innermost_locals expr;
      let linear_refs_ary = Array.map (fun _ -> copy_linear_refs linear_refs) brs in
      let f linear_refs cstr_nargs br = check_case_branch env evdref linear_refs num_innermost_locals cstr_nargs br in
      array_iter3 f linear_refs_ary ci.Constr.ci_cstr_nargs brs;
      update_linear_refs_for_case linear_refs_ary linear_refs)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      (let n = Array.length funary in
      let env2 = push_rec_types env !evdref (nameary, tyary, funary) in
      let linear_refs2 = ntimes n (List.cons None) linear_refs in
      Array.iter (check_type_linearity env !evdref) tyary;
      Array.iter (check_linear_exp env2 evdref linear_refs2 0) funary)
  | CoFix (i, (nameary, tyary, funary)) ->
      (let n = Array.length funary in
      let env2 = push_rec_types env !evdref (nameary, tyary, funary) in
      let linear_refs2 = ntimes n (List.cons None) linear_refs in
      Array.iter (check_type_linearity env !evdref) tyary;
      Array.iter (check_linear_exp env2 evdref linear_refs2 0) funary)
  | Proj (proj, expr) ->
      check_linear_exp env evdref linear_refs num_innermost_locals expr)
and check_case_branch env evdref linear_refs num_innermost_locals cstr_nargs br =
  if cstr_nargs = 0 then
    check_linear_exp env evdref linear_refs num_innermost_locals br
  else
    (match EConstr.kind !evdref br with
    | Lambda (name, ty, body) ->
        (check_type_linearity env !evdref ty;
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        with_local_var env evdref decl linear_refs num_innermost_locals
          (fun env2 linear_refs2 num_innermost_locals2 -> check_case_branch env2 evdref linear_refs2 num_innermost_locals2 (cstr_nargs-1) body))
    | _ ->
      user_err (str "unexpected non-Lambda in a case branch")) (* should eta-expansion? *)
and check_linear_exp env evdref linear_refs num_innermost_locals term =
  ((*Feedback.msg_debug (str "check_linear_exp:" ++ spc() ++ Printer.pr_econstr_env env !evdref term);*)
  let termty = Typing.e_type_of env evdref term in
  if isSort !evdref termty then
    check_type_linearity env !evdref term
  else
    check_linear_valexp env evdref linear_refs num_innermost_locals term)

let linear_type_check_term term =
  if !type_linearity_list <> [] then
    (let env = Global.env () in
    let sigma = Evd.from_env env in
    let evdref = ref sigma in
    let eterm = EConstr.of_constr term in
    check_linear_valexp env evdref [] 0 eterm)

let linear_type_check_single libref =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let evdref = ref sigma in
  match gref with
  | ConstRef cnst ->
      (let fctntu = Univ.in_punivs cnst in
      let (term, uconstraints) = Environ.constant_value env fctntu in
      let eterm = EConstr.of_constr term in
      check_linear_valexp env evdref [] 0 eterm;
      Feedback.msg_info (str "codegen linearity check passed:" ++ spc() ++ Printer.pr_constant env cnst);
      ())
  | _ -> user_err (str "not constant")

let linear_type_check_list libref_list =
  List.iter linear_type_check_single libref_list

(* xxx test *)

let linear_type_check_test t1 t2 =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let t1a : EConstr.constr = Constrintern.interp_constr_evars env evdref t1 in
  let t2a = Constrintern.interp_constr_evars env evdref t2 in
  Feedback.msg_debug (str "linear_type_check_test t1:" ++ spc() ++ Printer.pr_econstr_env env !evdref t1a);
  Feedback.msg_debug (str "linear_type_check_test t2:" ++ spc() ++ Printer.pr_econstr_env env !evdref t2a);
  Feedback.msg_debug (str "linear_type_check_test is_conv:" ++ spc() ++ bool (Reductionops.is_conv env !evdref t1a t2a));
  Feedback.msg_debug (str "linear_type_check_test is_conv_leq:" ++ spc() ++ bool (Reductionops.is_conv_leq env !evdref t1a t2a));
  let (sigma1, ib1) = Reductionops.infer_conv env !evdref t1a t2a in
  Feedback.msg_debug (str "linear_type_check_test infer_conv:" ++ spc() ++ bool ib1);
  let (sigma2, ib2) = Reductionops.infer_conv ~pb:Reduction.CONV env !evdref t1a t2a in
  Feedback.msg_debug (str "linear_type_check_test infer_conv(CONV):" ++ spc() ++ bool ib2)


