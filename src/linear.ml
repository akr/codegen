open Globnames
open Pp
open CErrors
open Term
open EConstr

open Cgenutil

let linear_type_list_empty : (t * bool) list = []

let linear_type_list = Summary.ref linear_type_list_empty ~name:"CodeGenLinearTypeList"

let register_linear_type (ty : Constrexpr.constr_expr) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (ty2, euc) = Constrintern.interp_constr env sigma ty in
  let ty3 = EConstr.of_constr ty2 in
  linear_type_list := (ty3, true) :: !linear_type_list;
  Feedback.msg_info (str "codegen linear type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty3)

let whd_all env sigma term = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))

let rec is_linear_type_rec env sigma ty l =
  match l with
  | [] -> None
  | (k, b) :: rest ->
      if eq_constr sigma ty k then Some b else is_linear_type_rec env sigma ty rest

let type_of_inductive_arity mind_arity : Term.constr =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Term.mkSort (Sorts.Type (temp_arity : Declarations.template_arity).Declarations.template_level)

let valid_type_param env sigma decl =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> isSort sigma (whd_all env sigma (EConstr.of_constr ty))
  | Context.Rel.Declaration.LocalDef _ -> false

let rec destProdN_rec sigma term n =
  if n = 0 then
    ([], [], term)
  else
    match EConstr.kind sigma term with
    | Prod (name, ty, body) ->
        let (names, tys, body) = destProdN_rec sigma body (n-1) in
        (name :: names, ty :: tys, body)
    | _ ->
        raise (CodeGenError "destProdN_rec: prod expected")

let destProdN sigma term n =
  let (names, tys, body) = destProdN_rec sigma term n in
  (Array.of_list names, Array.of_list tys, body)

let rec destProdX_rec sigma term =
  match EConstr.kind sigma term with
  | Prod (name, ty, body) ->
      let (names, tys, body) = destProdX_rec sigma body in
      (name :: names, ty :: tys, body)
  | _ ->
      raise (CodeGenError "destProdX_rec: prod expected")

let destProdX sigma term =
  let (names, tys, body) = destProdX_rec sigma term in
  (Array.of_list names, Array.of_list tys, body)

let rec is_linear_type_test env sigma ty =
  if isProd sigma ty then
    false
  else
    match is_linear_type_rec env sigma ty !linear_type_list with
    | Some b -> b
    | None ->
      (match EConstr.kind sigma ty with
      | Prod _ -> false
      | Ind iu -> is_linear_ind env sigma iu [| |]
      | App (f, argsary) ->
          if isInd sigma f then
            if array_for_all (is_linear_type_test env sigma) argsary &&
                let iu = destInd sigma f in
                is_linear_ind env sigma (destInd sigma f) argsary then
              (linear_type_list := (ty, true) :: !linear_type_list; true)
            else
              (linear_type_list := (ty, false) :: !linear_type_list; false)
          else
            raise (CodeGenError "is_linear_type_test: unexpected type function application")
      | _ -> raise (CodeGenError "is_linear_type_test: unexpected term"))
and is_linear_ind env sigma iu argsary =
  let ((mutind, i), _) = iu in (* strip EInstance.t *)
  let mind_body = Environ.lookup_mind mutind env in
  if mind_body.Declarations.mind_nparams <> mind_body.Declarations.mind_nparams_rec then
    false
  else if not (List.for_all (valid_type_param env sigma) mind_body.Declarations.mind_params_ctxt) then
    false
  else
    let env = Environ.push_rel_context (
      List.map (fun oind_body ->
        Context.Rel.Declaration.LocalAssum (Names.Name.Name oind_body.Declarations.mind_typename, type_of_inductive_arity oind_body.Declarations.mind_arity))
        (List.rev (Array.to_list mind_body.Declarations.mind_packets))
    ) env in
    Array.exists
      (fun oind_body ->
        Array.exists
          (fun user_lc ->
            let (tparam_names, tparam_tys, body) = destProdN sigma user_lc mind_body.Declarations.mind_nparams in
            (* typaram_names and typaram_tys should be match to mind_body.Declarations.mind_params_ctxt *)
            let (cparam_names, cparam_tys, body) = destProdX sigma body in
            let cparam_tys = Array.map (whd_all env sigma) cparam_tys in
            let body = whd_all env sigma body in
            (if not (isRel sigma body || (isApp sigma body && isRel sigma (fst (destApp sigma body)))) then
              raise (CodeGenError "is_linear_ind: constractor has non-prod"));
            (if Array.exists (isSort sigma) cparam_tys then raise (CodeGenError "is_linear_ind: constractor has type argument"));
            Array.exists
              (fun cparam_ty ->
                if isRel sigma cparam_ty || (isApp sigma cparam_ty && isRel sigma (fst (destApp sigma cparam_ty))) then
                  false
                else
                  is_linear_type_test env sigma cparam_ty)
              cparam_tys)
          (Array.map EConstr.of_constr oind_body.Declarations.mind_user_lc))
      mind_body.Declarations.mind_packets

let is_linear_type env sigma ty =
  let ty2 = whd_all env sigma ty in
  is_linear_type_test env sigma ty2

(*
let f env evdref term =
  (match EConstr.kind !evdref term with
  | Rel i -> Feedback.msg_info (str "rel")
  | Var name -> Feedback.msg_info (str "var")
  | Meta i -> Feedback.msg_info (str "meta")
  | Evar (ekey, termary) -> Feedback.msg_info (str "evar")
  | Sort s -> Feedback.msg_info (str "sort")
  | Cast (expr, kind, ty) -> Feedback.msg_info (str "cast")
  | Prod (name, ty, body) -> Feedback.msg_info (str "prod")
  | Lambda (name, ty, body) -> Feedback.msg_info (str "lambda")
  | LetIn (name, expr, ty, body) -> Feedback.msg_info (str "letin")
  | App (f, argsary) -> Feedback.msg_info (str "app")
  | Const ctntu -> Feedback.msg_info (str "const")
  | Ind iu -> Feedback.msg_info (str "ind")
  | Construct cstru -> Feedback.msg_info (str "construct")
  | Case (ci, tyf, expr, brs) -> Feedback.msg_info (str "case")
  | Fix ((ia, i), (nameary, tyary, funary)) -> Feedback.msg_info (str "fix")
  | CoFix (i, (nameary, tyary, funary)) -> Feedback.msg_info (str "cofix")
  | Proj (proj, expr) -> Feedback.msg_info (str "proj"));
  Feedback.msg_info (str "codegen linear type f:" ++ spc() ++ Printer.pr_econstr_env env !evdref term)
*)

let check_not_linear_type env sigma ty =
  if is_linear_type env sigma ty then
    raise (CodeGenError "unexpected linear type binding")

(* check follows:
   1. no reference to local linear variables (Ref)
   2. not bind local linear variable (Prod, Lambda, LetIn)
   Note that this doesn't prohibit the term itself is a linear type.
 *)
let rec check_no_linear_var env evdref linear_refs term =
  (match EConstr.kind !evdref term with
  | Rel i ->
      (match List.nth linear_refs (i-1) with
      | None -> () (* usual (non-linear) variable *)
      | Some cell -> (* linear variable *)
          raise (CodeGenError "unexpected linear variable reference"))
  | Var name -> ()
  | Meta i -> ()
  | Evar (ekey, termary) -> ()
  | Sort s -> ()
  | Cast (expr, kind, ty) ->
      (check_no_linear_var env evdref linear_refs expr;
      check_no_linear_var env evdref linear_refs ty)
  | Prod (name, ty, body) ->
      (check_no_linear_var env evdref linear_refs ty;
      check_not_linear_type env !evdref ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      check_no_linear_var env2 evdref (None :: linear_refs) body)
  | Lambda (name, ty, body) ->
      (check_no_linear_var env evdref linear_refs ty;
      check_not_linear_type env !evdref ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      check_no_linear_var env2 evdref (None :: linear_refs) body)
  | LetIn (name, expr, ty, body) ->
      (check_no_linear_var env evdref linear_refs ty;
      check_no_linear_var env evdref linear_refs expr;
      check_not_linear_type env !evdref ty;
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = EConstr.push_rel decl env in
      check_no_linear_var env2 evdref (None :: linear_refs) body)
  | App (f, argsary) ->
      (check_no_linear_var env evdref linear_refs f;
      Array.iter (check_no_linear_var env evdref linear_refs) argsary)
  | Const ctntu -> ()
  | Ind iu -> ()
  | Construct cstru -> ()
  | Case (ci, tyf, expr, brs) ->
      (check_no_linear_var env evdref linear_refs tyf;
      check_no_linear_var env evdref linear_refs expr;
      Array.iter (check_no_linear_var env evdref linear_refs) brs)
  | Const ctntu -> ()
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      (Array.iter (check_no_linear_var env evdref linear_refs) tyary;
      Array.iter (check_no_linear_var env evdref linear_refs) funary)
  | CoFix (i, (nameary, tyary, funary)) ->
      (Array.iter (check_no_linear_var env evdref linear_refs) tyary;
      Array.iter (check_no_linear_var env evdref linear_refs) funary)
  | Proj (proj, expr) ->
      check_no_linear_var env evdref linear_refs expr);
  Feedback.msg_info (str "codegen linear type f:" ++ spc() ++ Printer.pr_econstr_env env !evdref term)

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

let add_linear_var linear_refs f =
  let r = ref 0 in
  let linear_refs2 = Some r :: linear_refs in
  f linear_refs2;
  if !r <> 1 then
    raise (CodeGenError "linear var not lineary used")
  else
    ()

let rec check_outermost_lambdas env evdref linear_refs num_innermost_locals term =
  match EConstr.kind !evdref term with
  | Lambda (name, ty, body) ->
      (check_no_linear_var env evdref linear_refs ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      if is_linear_type env !evdref ty then
        add_linear_var linear_refs (fun linear_refs2 -> check_outermost_lambdas env evdref linear_refs2 (num_innermost_locals+1) body)
      else
        check_outermost_lambdas env evdref (None :: linear_refs) (num_innermost_locals+1) body)
  | _ -> check_linear_var env evdref linear_refs num_innermost_locals term
and check_linear_var env evdref linear_refs num_innermost_locals term =
  (Feedback.msg_info (str "check_linear_var:" ++ spc() ++ Printer.pr_econstr_env env !evdref term);
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
              raise (CodeGenError "second reference to a linear variable")
          else
            raise (CodeGenError "linear variable reference outside of a function"))
  | Var name -> ()
  | Meta i -> ()
  | Evar (ekey, termary) -> ()
  | Sort s -> ()
  | Cast (expr, kind, ty) ->
      (check_no_linear_var env evdref linear_refs ty;
      check_linear_var env evdref linear_refs num_innermost_locals expr)
  | Prod (name, ty, body) ->
      check_no_linear_var env evdref linear_refs term
  | Lambda (name, ty, body) ->
      check_outermost_lambdas env evdref linear_refs 0 term
  | LetIn (name, expr, ty, body) ->
      (check_no_linear_var env evdref linear_refs ty;
      check_linear_var env evdref linear_refs num_innermost_locals expr;
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = EConstr.push_rel decl env in
      if is_linear_type env !evdref ty then
        add_linear_var linear_refs (fun linear_refs2 -> check_linear_var env evdref linear_refs2 (num_innermost_locals+1) body)
      else
        check_linear_var env evdref (None :: linear_refs) (num_innermost_locals+1) body)
  | App (f, argsary) ->
      (check_linear_var env evdref linear_refs num_innermost_locals f;
      Array.iter (check_linear_var env evdref linear_refs num_innermost_locals) argsary)
  | Const ctntu -> ()
  | Ind iu -> ()
  | Construct cstru -> ()
  | Case (ci, tyf, expr, brs) ->
      (check_no_linear_var env evdref linear_refs tyf;
      check_linear_var env evdref linear_refs num_innermost_locals expr;
      let linear_refs_ary = Array.map (fun _ -> copy_linear_refs linear_refs) brs in
      let f linear_refs cstr_nargs br = check_case_branch env evdref linear_refs num_innermost_locals cstr_nargs br in
      array_iter3 f linear_refs_ary ci.Constr.ci_cstr_nargs brs;
      update_linear_refs_for_case linear_refs_ary linear_refs)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      (let n = Array.length funary in
      let env2 = push_rec_types env !evdref (nameary, tyary, funary) in
      let linear_refs2 = ntimes n (List.cons None) linear_refs in
      Array.iter (check_no_linear_var env evdref linear_refs) tyary;
      Array.iter (check_linear_var env2 evdref linear_refs2 0) funary)
  | CoFix (i, (nameary, tyary, funary)) ->
      (let n = Array.length funary in
      let env2 = push_rec_types env !evdref (nameary, tyary, funary) in
      let linear_refs2 = ntimes n (List.cons None) linear_refs in
      Array.iter (check_no_linear_var env evdref linear_refs) tyary;
      Array.iter (check_linear_var env2 evdref linear_refs2 0) funary)
  | Proj (proj, expr) ->
      check_linear_var env evdref linear_refs num_innermost_locals expr)
and check_case_branch env evdref linear_refs num_innermost_locals cstr_nargs br =
  if cstr_nargs = 0 then
    check_linear_var env evdref linear_refs num_innermost_locals br
  else
    (match EConstr.kind !evdref br with
    | Lambda (name, ty, body) ->
        (check_no_linear_var env evdref linear_refs ty;
        check_not_linear_type env !evdref ty;
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        check_case_branch env evdref (None :: linear_refs) (num_innermost_locals+1) (cstr_nargs-1) body)
    | _ ->
      raise (CodeGenError "unexpected non-Lambda in a case branch"))

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
      check_linear_var env evdref [] 0 eterm;
      ())
  | _ -> user_err (Pp.str "not constant")

let linear_type_check_list libref_list =
  List.iter linear_type_check_single libref_list

(* xxx test *)

let linear_type_check_test t1 t2 =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let t1a : EConstr.constr = Constrintern.interp_constr_evars env evdref t1 in
  let t2a = Constrintern.interp_constr_evars env evdref t2 in
  Feedback.msg_info (str "linear_type_check_test t1:" ++ spc() ++ Printer.pr_econstr_env env !evdref t1a);
  Feedback.msg_info (str "linear_type_check_test t2:" ++ spc() ++ Printer.pr_econstr_env env !evdref t2a);
  Feedback.msg_info (str "linear_type_check_test is_conv:" ++ spc() ++ bool (Reductionops.is_conv env !evdref t1a t2a));
  Feedback.msg_info (str "linear_type_check_test is_conv_leq:" ++ spc() ++ bool (Reductionops.is_conv_leq env !evdref t1a t2a));
  let (sigma1, ib1) = Reductionops.infer_conv env !evdref t1a t2a in
  Feedback.msg_info (str "linear_type_check_test infer_conv:" ++ spc() ++ bool ib1);
  let (sigma2, ib2) = Reductionops.infer_conv ~pb:Reduction.CONV env !evdref t1a t2a in
  Feedback.msg_info (str "linear_type_check_test infer_conv(CONV):" ++ spc() ++ bool ib2)


