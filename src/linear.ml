open Globnames
open Pp
open CErrors
open Term
open EConstr

open Cgenutil

let linear_type_list_empty : t list = []

let linear_type_list = Summary.ref linear_type_list_empty ~name:"CodeGenLinearTypeList"

let register_linear_type (ty : Constrexpr.constr_expr) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (ty2, euc) = Constrintern.interp_constr env sigma ty in
  let ty3 = EConstr.of_constr ty2 in
  linear_type_list := ty3 :: !linear_type_list;
  Feedback.msg_info (str "codegen linear type registered:" ++ spc() ++ Printer.pr_econstr_env env sigma ty3)

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

let is_linear_type env sigma ty =
  List.exists (fun lty -> Reductionops.is_conv_leq env sigma ty lty) !linear_type_list

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

let rec check_outermost_lambdas env evdref linear_refs num_innermost_locals term =
  match EConstr.kind !evdref term with
  | Lambda (name, ty, body) ->
      (check_no_linear_var env evdref linear_refs ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      if is_linear_type env !evdref ty then
        check_outermost_lambdas env evdref (Some (ref 0) :: linear_refs) (num_innermost_locals+1) body
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
        check_linear_var env evdref (Some (ref 0) :: linear_refs) (num_innermost_locals+1) body
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


