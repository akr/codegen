(*
Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*)

open Names
open Globnames
open Pp
open CErrors

open Cgenutil

open Term
open EConstr

let rec copy_term sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel i -> mkRel i
  | Var name -> mkVar name
  | Meta i -> mkMeta i
  | Evar (ekey, termary) -> mkEvar (ekey, (Array.map (copy_term sigma) termary))
  | Sort s -> mkSort (ESorts.kind sigma s)
  | Cast (expr, kind, ty) -> mkCast (copy_term sigma expr, kind, copy_term sigma ty)
  | Prod (name, ty, body) -> mkProd (name, copy_term sigma ty, copy_term sigma body)
  | Lambda (name, ty, body) -> mkLambda (name, copy_term sigma ty, copy_term sigma body)
  | LetIn (name, expr, ty, body) -> mkLetIn (name, copy_term sigma expr, copy_term sigma ty, copy_term sigma body)
  | App (f, argsary) -> mkApp (copy_term sigma f, Array.map (copy_term sigma) argsary)
  | Const cu -> mkConstU cu
  | Ind iu -> mkIndU iu
  | Construct cu -> mkConstructU cu
  | Case (ci, tyf, expr, brs) -> mkCase (ci, copy_term sigma tyf, copy_term sigma expr, Array.map (copy_term sigma) brs)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      mkFix ((ia, i), (nameary, Array.map (copy_term sigma) tyary, Array.map (copy_term sigma) funary))
  | CoFix (i, (nameary, tyary, funary)) ->
      mkCoFix (i, (nameary, Array.map (copy_term sigma) tyary, Array.map (copy_term sigma) funary))
  | Proj (proj, expr) ->
      mkProj (proj, copy_term sigma expr)

let rec subst_term sigma context term =
  match EConstr.kind sigma term with
  | Constr.Rel i ->
      (if List.length context <= i-1 then
        mkRel i
      else
        match List.nth context (i-1) with
        | None -> mkRel i
        | Some tm -> tm) (* assume tm has no Rel. *)
  | Var name -> mkVar name
  | Meta i -> mkMeta i
  | Evar (ekey, termary) -> mkEvar (ekey, (Array.map (subst_term sigma context) termary))
  | Sort s -> mkSort (ESorts.kind sigma s)
  | Cast (expr, kind, ty) -> mkCast (subst_term sigma context expr, kind, subst_term sigma context ty)
  | Prod (name, ty, body) -> mkProd (name, subst_term sigma context ty, subst_term sigma (None :: context) body)
  | Lambda (name, ty, body) -> mkLambda (name, subst_term sigma context ty, subst_term sigma (None :: context) body)
  | LetIn (name, expr, ty, body) -> mkLetIn (name, subst_term sigma context expr, subst_term sigma context ty, subst_term sigma (None :: context) body)
  | App (f, argsary) -> mkApp (subst_term sigma context f, Array.map (subst_term sigma context) argsary)
  | Const cu -> mkConstU cu
  | Ind iu -> mkIndU iu
  | Construct cu -> mkConstructU cu
  | Case (ci, tyf, expr, brs) -> mkCase (ci, subst_term sigma context tyf, subst_term sigma context expr, Array.map (subst_term sigma context) brs)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let context2 = Array.fold_right (fun _ ctx -> None :: ctx) funary context in
      mkFix ((ia, i), (nameary, Array.map (subst_term sigma context) tyary, Array.map (subst_term sigma context2) funary))
  | CoFix (i, (nameary, tyary, funary)) ->
      let context2 = Array.fold_right (fun _ ctx -> None :: ctx) funary context in
      mkCoFix (i, (nameary, Array.map (subst_term sigma context) tyary, Array.map (subst_term sigma context2) funary))
  | Proj (proj, expr) ->
      mkProj (proj, subst_term sigma context expr)

(*let rec has_rel term =
  match Term.kind_of_term term with
  | Term.Rel i -> true
  | Var name -> false
  | Meta i -> false
  | Evar (ekey, termary) -> false
  | Sort s -> false
  | Cast (expr, kind, ty) -> has_rel expr || has_rel ty
  | Prod (name, ty, body) -> has_rel ty || has_rel body
  | Lambda (name, ty, body) -> has_rel ty || has_rel body
  | LetIn (name, expr, ty, body) -> has_rel expr || has_rel ty || has_rel body
  | App (f, argsary) -> has_rel f || array_exists has_rel argsary
  | Const cu -> false
  | Ind iu -> false
  | Construct cu -> false
  | Case (ci, tyf, expr, brs) -> has_rel tyf || has_rel expr || array_exists has_rel brs
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      array_exists has_rel tyary || array_exists has_rel funary
  | CoFix (i, (nameary, tyary, funary)) ->
      array_exists has_rel tyary || array_exists has_rel funary
  | Proj (proj, expr) ->
      has_rel expr*)

let is_sort sigma term =
  match EConstr.kind sigma term with
  | Constr.Sort s -> true
  | _ -> false

let rec has_sort sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel i -> false
  | Var name -> false
  | Meta i -> false
  | Evar (ekey, termary) -> false
  | Sort s -> true
  | Cast (expr, kind, ty) -> has_sort sigma expr || has_sort sigma ty
  | Prod (name, ty, body) -> has_sort sigma ty || has_sort sigma body
  | Lambda (name, ty, body) -> has_sort sigma ty || has_sort sigma body
  | LetIn (name, expr, ty, body) -> has_sort sigma expr || has_sort sigma ty || has_sort sigma body
  | App (f, argsary) -> has_sort sigma f || array_exists (has_sort sigma) argsary
  | Const cu -> false
  | Ind iu -> false
  | Construct cu -> false
  | Case (ci, tyf, expr, brs) -> has_sort sigma tyf || has_sort sigma expr || array_exists (has_sort sigma) brs
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      array_exists (has_sort sigma) tyary || array_exists (has_sort sigma) funary
  | CoFix (i, (nameary, tyary, funary)) ->
      array_exists (has_sort sigma) tyary || array_exists (has_sort sigma) funary
  | Proj (proj, expr) ->
      has_sort sigma expr

let deanonymize_term env sigma term =
  let rec r env term =
    match kind sigma term with
    | Constr.Rel i -> term
    | Var name -> term
    | Meta i -> term
    | Evar (ekey, termary) -> mkEvar (ekey, Array.map (r env) termary)
    | Sort s -> term
    | Cast (expr, kind, ty) -> mkCast (r env expr, kind, r env ty)
    | Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        Namegen.mkProd_name env sigma (name, r env ty, r env2 body)
    | Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        Namegen.mkLambda_name env sigma (name, r env ty, r env2 body)
    | LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = EConstr.push_rel decl env in
        mkLetIn (Namegen.named_hd env sigma ty name, r env expr, r env ty, r env2 body)
    | App (f, argsary) -> mkApp (r env f, Array.map (r env) argsary)
    | Const (cnst, u) -> term
    | Ind (ind, u) -> term
    | Construct (cstr, u) -> term
    | Case (ci, tyf, expr, brs) -> mkCase (ci, r env tyf, r env expr, Array.map (r env) brs)
    | Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, Array.map (EConstr.to_constr sigma) tyary, Array.map (EConstr.to_constr sigma) funary) env in
        let nameary2 = array_map2 (Namegen.named_hd env sigma) tyary nameary in
        mkFix ((ia, i), (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | CoFix (i, (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, Array.map (EConstr.to_constr sigma) tyary, Array.map (EConstr.to_constr sigma) funary) env in
        let nameary2 = array_map2 (Namegen.named_hd env sigma) tyary nameary in
        mkCoFix (i, (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | Proj (proj, expr) ->
        mkProj (proj, r env expr)
  in
  r env term

let expand_type env sigmaref term =
  let rec r env term =
    if EConstr.isProd !sigmaref term then
      r2 env term
    else
      let termty = Typing.e_type_of env sigmaref term in
      if EConstr.isSort !sigmaref termty then
        let term' = Reduction.whd_all env (EConstr.to_constr !sigmaref term )in
        r2 env (EConstr.of_constr term')
      else
        r2 env term
  and r2 env term =
    match EConstr.kind !sigmaref term with
    | Constr.Rel i -> term
    | Var name -> term
    | Meta i -> term
    | Evar (ekey, termary) -> mkEvar (ekey, (Array.map (r env) termary))
    | Sort s -> term
    | Cast (expr, kind, ty) -> mkCast (r env expr, kind, r env ty)
    | Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        mkProd (name, r env ty, r env2 body)
    | Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = EConstr.push_rel decl env in
        mkLambda (name, r env ty, r env2 body)
    | LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = EConstr.push_rel decl env in
        mkLetIn (name, r env expr, r env ty, r env2 body)
    | App (f, argsary) -> mkApp (r env f, Array.map (r env) argsary)
    | Const (cnst, u) -> term
    | Ind (ind, u) -> term
    | Construct (cstr, u) -> term
    | Case (ci, tyf, expr, brs) -> mkCase (ci, r env tyf, r env expr, Array.map (r env) brs)
    | Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, Array.map (EConstr.to_constr !sigmaref) tyary, Array.map (EConstr.to_constr !sigmaref) funary) env in
        mkFix ((ia, i), (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | CoFix (i, (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, Array.map (EConstr.to_constr !sigmaref) tyary, Array.map (EConstr.to_constr !sigmaref) funary) env in
        mkCoFix (i, (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | Proj (proj, expr) ->
        mkProj (proj, r env expr)
  in
  r env term

let type_of env evdref term =
  let ty = Typing.e_type_of env evdref term in
  expand_type env evdref ty

let constant_type env evdref cu =
  let (ty, uconstraints) = Environ.constant_type env cu in
  expand_type env evdref (EConstr.of_constr ty)

let rec count_type_args sigma fty =
  match EConstr.kind sigma fty with
  | Constr.Prod (name, ty, body) ->
    if is_sort sigma ty then
      1 + count_type_args sigma body
    else
      0
  | _ -> 0

(*
let rec type_arg_flaglist fty =
  match Term.kind_of_term fty with
  | Term.Prod (name, ty, body) ->
    if is_sort ty then
      true :: type_arg_flaglist body
    else
      false :: type_arg_flaglist body
  | _ -> []
*)

let rec eq_typeary_rec sigma types1 types2 i =
  if i = 0 then
    true
  else
  let j = i - 1 in
  if EConstr.eq_constr sigma (Array.get types1 j) (Array.get types2 j) then
    eq_typeary_rec sigma types1 types2 j
  else
    false

let eq_typeary sigma types1 types2 =
  let n1 = Array.length types1 in
  let n2 = Array.length types2 in
  if n1 <> n2 then
    false
  else
    eq_typeary_rec sigma types1 types2 n1

let beta_lambda_list sigma expr args =
  let n = List.length args in
  let body =
    List.fold_left
      (fun e _ ->
        match EConstr.kind sigma e with
        | Constr.Lambda (name, ty, body) -> body
        | _ -> raise (Invalid_argument "beta_lambda_list"))
      expr args
  in
  Vars.lift (-n) (subst_term sigma args body)

let beta_lambda_ary sigma expr args =
  beta_lambda_list sigma expr (Array.to_list (Array.map (fun arg -> Some arg) args))

let beta_prod_list sigma expr args =
  let n = List.length args in
  let body =
    List.fold_left
      (fun e _ ->
        match EConstr.kind sigma e with
        | Constr.Prod (name, ty, body) -> body
        | _ -> raise (Invalid_argument "beta_prod_list"))
      expr args
  in
  Vars.lift (-n) (subst_term sigma args body)

let beta_prod_ary sigma ty args =
  beta_prod_list sigma ty (Array.to_list (Array.map (fun arg -> Some arg) args))

let rec mono_local_rec sigma context term =
(*Feedback.msg_info (str "mono_local_rec:start");*)
  match EConstr.kind sigma term with
  | Constr.Rel i ->
(*Feedback.msg_info (str "mono_local_rec:rel:i=" ++ int i);*)
      (match List.nth context (i-1) with
      | None ->
(*Feedback.msg_info (str "mono_local_rec:rel:none");*)
          fun acc -> mkRel (List.hd acc - List.nth acc (i-1) + 1)
      | Some (num_type_args, refs) ->
(*Feedback.msg_info (str "mono_local_rec:rel:some");*)
          if num_type_args = 0 then
            (if !refs = [] then
              refs := [| |] :: !refs;
            fun acc ->
            mkRel (List.hd acc - List.nth acc (i-1) + 1))
          else
            raise (CodeGenError "mono_local_rec:rel"))
  | Var name -> fun acc -> mkVar name
  | Meta i -> fun acc -> mkMeta i
  | Evar (ekey, termary) ->
      let ary = Array.map (mono_local_rec sigma context) termary in
      fun acc -> mkEvar (ekey, Array.map (fun f -> f acc) ary)
  | Sort s -> fun acc -> mkSort (ESorts.kind sigma s)
  | Cast (expr, kind, ty) ->
      let expr' = mono_local_rec sigma context expr in
      let ty' = mono_local_rec sigma context ty in
      fun acc -> mkCast (expr' acc, kind, ty' acc)
  | Prod (name, ty, body) ->
      let ty' = mono_local_rec sigma context ty in
      let body' = mono_local_rec sigma (None :: context) body in
      fun acc -> mkProd (name, ty' acc, body' ((1 + List.hd acc) :: acc))
  | Lambda (name, ty, body) ->
(*Feedback.msg_info (str "mono_local_rec:lambda");*)
      let ty' = mono_local_rec sigma context ty in
      let body' = mono_local_rec sigma (None :: context) body in
      fun acc -> mkLambda (name, ty' acc, body' ((1 + List.hd acc) :: acc))
  | LetIn (name, expr, ty, body) ->
(*Feedback.msg_info (str "mono_local_rec:let");*)
      let num_type_args = count_type_args sigma ty in
(*Feedback.msg_info (str "mono_local_rec:let:1:num_type_args=" ++ int num_type_args);*)
      let refs : constr array list ref = ref [] in
(*Feedback.msg_info (str "mono_local_rec:let:2");*)
      let body' = mono_local_rec sigma (Some (num_type_args, refs) :: context) body in
(*Feedback.msg_info (str "mono_local_rec:let:3");*)
      let exprs = List.map (fun type_args -> mono_local_rec sigma context (beta_lambda_ary sigma expr type_args)) !refs in
(*Feedback.msg_info (str "mono_local_rec:let:4");*)
      let tys = List.map (fun type_args -> mono_local_rec sigma context (beta_prod_ary sigma ty type_args)) !refs in
(*Feedback.msg_info (str "mono_local_rec:let:5");*)
      fun acc ->
      List.fold_left2
        (fun b e t -> mkLetIn (name, e acc, t acc, b))
        (body' ((List.length exprs + List.hd acc) :: acc))
        exprs tys
  | App (f, argsary) ->
      (match kind sigma f with
      | Rel i ->
          (match List.nth context (i-1) with
          | None ->
              let argsary' = Array.map (mono_local_rec sigma context) argsary in
              fun acc -> mkApp (mkRel (List.hd acc - List.nth acc (i-1) + 1), Array.map (fun arg -> arg acc) argsary')
          | Some (num_type_args, refs) ->
              (if Array.length argsary < num_type_args then
                raise (CodeGenError "mono_local_rec:app");
              let type_args = Array.sub argsary 0 num_type_args in
              (* xxx: check no Rel in type_args *)
              if not (List.exists (eq_typeary sigma type_args) !refs) then
                refs := type_args :: !refs;
              let argsary' = Array.map (mono_local_rec sigma context) (Array.sub argsary num_type_args (Array.length argsary - num_type_args)) in
              fun acc ->
              mkApp
                (mkRel (List.hd acc - List.nth acc (i-1) + 1 + list_find_index (eq_typeary sigma type_args) !refs),
                (Array.map (fun arg -> arg acc)) argsary')))
      | _ ->
          let f' = mono_local_rec sigma context f in
          let argsary' = Array.map (mono_local_rec sigma context) argsary in
          fun acc -> mkApp (f' acc, Array.map (fun arg -> arg acc) argsary'))
  | Const cu -> fun acc -> mkConstU cu
  | Ind iu ->
(*Feedback.msg_info (str "mono_local_rec:ind");*)
      fun acc -> mkIndU iu
  | Construct cu ->
(*Feedback.msg_info (str "mono_local_rec:construct");*)
      fun acc -> mkConstructU cu
  | Case (ci, tyf, expr, brs) ->
      let tyf' = mono_local_rec sigma context tyf in
      let expr' = mono_local_rec sigma context expr in
      let brs' = Array.map (mono_local_rec sigma context) brs in
      fun acc ->
      mkCase (ci, tyf' acc, expr' acc, Array.map (fun br -> br acc) brs')
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let n = Array.length funary in
      let tyary' = Array.map (mono_local_rec sigma context) tyary in
      let funary' = Array.map (mono_local_rec sigma (ncons n None context)) funary in
      fun acc ->
      let acc' = List.rev (iota_list (List.hd acc + 1) n) @ acc in
      mkFix ((ia, i), (nameary, Array.map (fun ty -> ty acc) tyary', Array.map (fun f -> f acc') funary'))
  | CoFix (i, (nameary, tyary, funary)) ->
      let n = Array.length funary in
      let tyary' = Array.map (mono_local_rec sigma context) tyary in
      let funary' = Array.map (mono_local_rec sigma (ncons n None context)) funary in
      fun acc ->
      let acc' = List.rev (iota_list (List.hd acc + 1) n) @ acc in
      mkCoFix (i, (nameary, Array.map (fun ty -> ty acc) tyary', Array.map (fun f -> f acc') funary'))
  | Proj (proj, expr) ->
      let expr' = mono_local_rec sigma context expr in
      fun acc ->
      mkProj (proj, expr' acc)

let mono_local sigma term = mono_local_rec sigma [] term [0]

let simple_fun_p sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel _ | Const _ | Construct _ -> true
  | _ -> false

let simple_arg_p sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel _ -> true
  | _ -> false

let rec hoist_terms env evdref simple_p terms bodyfun =
  match terms with
  | [] ->
      bodyfun env [] (fun t : constr -> t)
  | term :: rest ->
      if simple_p term then
        hoist_terms env evdref simple_p rest
          (fun env rest' shifter ->
            bodyfun env (shifter term :: rest') shifter)
      else
        let ty = type_of env evdref term in
        let name = Names.Name.Anonymous in
        let expr = stmt_rec env evdref term in
        let env1 = EConstr.push_rel (Context.Rel.Declaration.LocalDef (name, expr, ty)) env in
        EConstr.mkLetIn (name, expr, ty,
          (hoist_terms env1 evdref simple_p (List.map (Vars.lift 1) rest)
            (fun env2 rest' shifter ->
              bodyfun
                env2
                ((shifter (EConstr.mkRel 1)) :: rest')
                (fun t -> (Vars.lift 1 (shifter t))))))

and hoist_term1 env evdref simple_p term bodyfun =
  hoist_terms env evdref simple_p [term]
    (fun env' terms' shifter -> bodyfun env' (List.hd terms') shifter)

and stmt_rec env evdref term =
  match EConstr.kind !evdref term with
  | Constr.Rel i -> term
  | Var name -> term
  | Meta i -> term
  | Evar (ekey, termary) -> term
  | Sort s -> term
  | Cast (expr, kind, ty) ->
      hoist_term1 env evdref (simple_arg_p !evdref) expr
        (fun env' expr' shifter -> mkCast (expr', kind, shifter ty))
  | Prod (name, ty, body) -> term
  | Lambda (name, ty, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (name, ty, stmt_rec env2 evdref body)
  | LetIn (name, expr, ty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLetIn (name, stmt_rec env evdref expr, ty, stmt_rec env2 evdref body)
  | App (f, argsary) ->
      let fty = type_of env evdref f in
      let num_type_args = count_type_args !evdref fty in
      let targs = Array.sub argsary 0 num_type_args in
      let vargs = Array.sub argsary num_type_args (Array.length argsary - num_type_args) in
      hoist_term1 env evdref (simple_fun_p !evdref) f
        (fun env1 f1 shifter1 ->
          let targs1 = Array.map shifter1 targs in
          let vargs1 = Array.map shifter1 vargs in
          hoist_terms env1 evdref (simple_arg_p !evdref) (Array.to_list vargs1)
            (fun env2 fargs2 shifter2 ->
              mkApp (shifter2 f1, (Array.append (Array.map shifter2 targs1) (Array.of_list fargs2)))))
  | Const cu -> term
  | Ind iu -> term
  | Construct cu -> term
  | Case (ci, tyf, expr, branches) ->
      hoist_term1 env evdref (simple_arg_p !evdref) expr
        (fun env' expr' shifter ->
          mkCase (ci, (shifter tyf), expr', Array.map (fun branch -> stmt_rec env' evdref (shifter branch)) branches))
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let decls = array_map2 (fun n ty -> Context.Rel.Declaration.LocalAssum (n, ty)) nameary tyary in
      let env2 = Array.fold_left (fun e d -> EConstr.push_rel d e) env decls in
      mkFix ((ia, i), (nameary, tyary, Array.map (stmt_rec env2 evdref) funary))
  | CoFix (i, (nameary, tyary, funary)) ->
      let decls = array_map2 (fun n ty -> Context.Rel.Declaration.LocalAssum (n, ty)) nameary tyary in
      let env2 = Array.fold_left (fun e d -> EConstr.push_rel d e) env decls in
      mkCoFix (i, (nameary, tyary, Array.map (stmt_rec env2 evdref) funary))
  | Proj (proj, expr) ->
      hoist_term1 env evdref (simple_arg_p !evdref) expr
        (fun env' expr' shifter -> mkProj (proj, expr'))

let stmt term =
  let (evd, env) = Pfedit.get_current_context () in
  let evdref = ref evd in
  stmt_rec env evdref term

let rec seq_let sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel i -> term
  | Var name -> term
  | Meta i -> term
  | Evar (ekey, termary) -> term
  | Sort s -> term
  | Cast (expr, kind, ty) ->
      mkCast (seq_let sigma expr, kind, ty)
  | Prod (name, ty, body) -> term
  | Lambda (name, ty, body) ->
      mkLambda (name, ty, seq_let sigma body)
  | LetIn (name, expr, ty, body) ->
      (match kind sigma expr with
      | LetIn (name1, expr1, ty1, body1) ->
          seq_let sigma
            (mkLetIn (name1, expr1, ty1,
              mkLetIn (name, body1, Vars.lift 1 ty, Vars.liftn 1 2 body)))
      | _ -> mkLetIn (name, seq_let sigma expr, ty, seq_let sigma body))
  | App (f, argsary) -> term
  | Const cu -> term
  | Ind iu -> term
  | Construct cu -> term
  | Case (ci, tyf, expr, branches) ->
      mkCase (ci, tyf, expr, Array.map (seq_let sigma) branches)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      mkFix ((ia, i), (nameary, tyary, Array.map (seq_let sigma) funary))
  | CoFix (i, (nameary, tyary, funary)) ->
      mkCoFix (i, (nameary, tyary, Array.map (seq_let sigma) funary))
  | Proj (proj, expr) -> term

let mangle_function_short ctnt type_args =
  let label = Constant.label ctnt in
  let buf = Buffer.create 0 in
  Buffer.add_char buf '_';
  Buffer.add_string buf (Label.to_string label);
  Array.iter (fun arg -> Buffer.add_char buf '_'; mangle_type_buf_short buf arg) type_args;
  Id.of_string (Buffer.contents buf)

let mangle_function ctnt type_args =
  mangle_function_short ctnt type_args

let mangle_constructor_short cstr param_args =
  let (evd, env) = Pfedit.get_current_context () in
  let ((mutind, i), j) = cstr in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  let buf = Buffer.create 0 in
  Buffer.add_char buf '_';
  Buffer.add_string buf (Id.to_string oneind_body.Declarations.mind_consnames.(j-1));
  Array.iter (fun arg -> Buffer.add_char buf '_'; mangle_type_buf_short buf arg) param_args;
  Buffer.contents buf

let mangle_constructor cstr param_args =
  mangle_constructor_short cstr param_args

let eq_monofunc ((c1, uc1), args1) ((c2, uc2), args2) =
  Names.Constant.CanOrd.equal c1 c2 &&
  Univ.Instance.equal uc1 uc2 &&
  Array.length args1 = Array.length args2 &&
  let rec loop i =
    if i = 0 then
      true
    else if Constr.equal args1.(i-1) args2.(i-1) then
      loop (i-1)
    else
      false
  in
  loop (Array.length args1)

let mono_global_visited_empty : ((global_reference * constr array) * Constant.t) list = []

let mono_global_visited = Summary.ref mono_global_visited_empty ~name:"MonomorphizationVisited"

let mono_check_const env evdref ctntu =
  let fty = constant_type env evdref ctntu in
  if has_sort !evdref fty then
    raise (CodeGenError "mono_check_const")
  else
    ()

let find_unused_name id =
  if not (Declare.exists_name id) then
    id
  else
    let rec loop i =
      let id' = (Id.of_string (Id.to_string id ^ "_" ^ string_of_int i)) in
      if not (Declare.exists_name id') then
        id'
      else loop (i+1)
    in
    loop 0

let rec mono_global_def env (evdref : Evd.evar_map ref) fctntu type_args =
  let (fctnt, u) = fctntu in
  if List.mem_assoc (ConstRef fctnt, type_args) !mono_global_visited then
    List.assoc (ConstRef fctnt, type_args) !mono_global_visited
  else
    let id_term (*unused?*)= mkApp (mkConst fctnt, type_args) in
    Feedback.msg_info (str "monomorphization start:" ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref id_term));
    let value_and_type = Environ.constant_value_and_type env fctntu in
    match value_and_type with
    | (Some term, termty, uconstraints) ->
      let term = expand_type env evdref (EConstr.of_constr term) in
      Feedback.msg_info (str "monomorphization 1:" ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref id_term));
      let term = beta_lambda_ary !evdref term type_args in
      Feedback.msg_info (str "monomorphization 2:" ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref id_term));
      let term = mono_local !evdref term in
      Feedback.msg_info (str "monomorphization 3:" ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref id_term));
      let term = mono_global env evdref term in
      Feedback.msg_info (str "monomorphization 4:" ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref id_term));
      let term = stmt term in
      let term = seq_let !evdref term in
      Feedback.msg_info (str "monomorphization 5:" ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref id_term));
      let term = deanonymize_term env !evdref term in
      (* Feedback.msg_info (Printer.pr_constr_env env !evdref id_term ++ spc () ++ str ":=" ++ spc() ++ Printer.pr_constr term);*)
      let id = find_unused_name (mangle_function fctnt (Array.map (EConstr.to_constr !evdref) type_args)) in
      let constant = Declare.declare_definition id
        (EConstr.to_constr !evdref term,
         Entries.Monomorphic_const_entry (Univ.ContextSet.add_constraints uconstraints Univ.ContextSet.empty)) in
      Feedback.msg_info (Id.print id ++ spc () ++ str ":=" ++ spc() ++
        Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref (mkApp ((mkConstU ((fun (a, b) -> (a, EInstance.make b)) fctntu)), type_args))));
      mono_global_visited := ((ConstRef fctnt, type_args), constant) :: !mono_global_visited;
      Feedback.msg_info (str "monomorphization end:" ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref id_term));
      constant
    | _ -> user_err (Pp.str "constant value couldn't obtained:" ++ Printer.pr_constant env fctnt)

and mono_global_const_app env evdref fctntu argsary =
  let fty = constant_type env evdref fctntu in
  let num_type_args = count_type_args !evdref fty in
  (if Array.length argsary < num_type_args then
    raise (CodeGenError "mono_global_const_app"));
  let type_args = Array.sub argsary 0 num_type_args in
  let rest_args = Array.sub argsary num_type_args (Array.length argsary - num_type_args) in
  let constant = mono_global_def env evdref fctntu type_args in
  mkApp (mkConst constant, rest_args)

and mono_constr_def env sigma fcstr mutind i j param_args =
  if List.mem_assoc (ConstructRef fcstr, param_args) !mono_global_visited then
    List.assoc (ConstructRef fcstr, param_args) !mono_global_visited
  else
    let term = mkApp (mkConstruct fcstr, param_args) in
    let term = deanonymize_term env sigma term in
    let id = find_unused_name (Id.of_string (mangle_constructor fcstr (Array.map (EConstr.to_constr sigma) param_args))) in
    let constant = Declare.declare_definition id
      (EConstr.to_constr sigma term,
       Entries.Monomorphic_const_entry Univ.ContextSet.empty) in
    mono_global_visited := ((ConstructRef fcstr, param_args), constant) :: !mono_global_visited;
    constant

and mono_global_cstr_app env sigma fcstru argsary =
  let fcstr = Univ.out_punivs fcstru in
  let ((mutind, i), j) = fcstr in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  let num_indparams = List.length oneind_body.Declarations.mind_arity_ctxt in
  let param_args = Array.sub argsary 0 num_indparams in
  let rest_args = Array.sub argsary num_indparams (Array.length argsary - num_indparams) in
  let constant = mono_constr_def env sigma fcstr mutind i j param_args in
  mkApp (mkConst constant, rest_args);

and mono_global env evdref term =
Feedback.msg_info (str "mono_global:start " ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref term));
  match EConstr.kind !evdref term with
  | Constr.Rel i -> mkRel i
  | Var name -> mkVar name
  | Meta i -> mkMeta i
  | Evar (ekey, termary) -> mkEvar (ekey, (Array.map (mono_global env evdref) termary))
  | Sort s -> mkSort (ESorts.kind !evdref s)
  | Cast (expr, kind, ty) -> mkCast (mono_global env evdref expr, kind, mono_global env evdref ty)
  | Prod (name, ty, body) -> mkProd (name, mono_global env evdref ty, mono_global env evdref body)
  | Lambda (name, ty, body) -> mkLambda (name, mono_global env evdref ty, mono_global env evdref body)
  | LetIn (name, expr, ty, body) -> mkLetIn (name, mono_global env evdref expr, mono_global env evdref ty, mono_global env evdref body)
  | App (f, argsary) ->
      (match kind !evdref f with
      | Const (fctnt,u) -> mono_global_const_app env evdref (fctnt,EInstance.kind !evdref u) (Array.map (mono_global env evdref) argsary)
      | Construct (fcstr,u) -> mono_global_cstr_app env !evdref (fcstr,EInstance.kind !evdref u) (Array.map (mono_global env evdref) argsary)
      | _ -> mkApp (mono_global env evdref f, Array.map (mono_global env evdref) argsary))
  | Const (ctnt,u) -> mono_check_const env evdref (ctnt,EInstance.kind !evdref u); mono_global_const_app env evdref (ctnt,EInstance.kind !evdref u) [| |]
  | Ind iu -> mkIndU iu
  | Construct (cstr,u) -> mono_global_cstr_app env !evdref (cstr,EInstance.kind !evdref u) [| |]
  | Case (ci, tyf, expr, brs) -> mkCase (ci, mono_global env evdref tyf, mono_global env evdref expr, Array.map (mono_global env evdref) brs)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      mkFix ((ia, i), (nameary, Array.map (mono_global env evdref) tyary, Array.map (mono_global env evdref) funary))
  | CoFix (i, (nameary, tyary, funary)) ->
      mkCoFix (i, (nameary, Array.map (mono_global env evdref) tyary, Array.map (mono_global env evdref) funary))
  | Proj (proj, expr) ->
      mkProj (proj, mono_global env evdref expr)

let mono env evdref term = mono_global env evdref (mono_local !evdref term)

let monomorphization_single libref =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  match gref with
  | ConstRef cnst ->
      let _ = mono_global_def env evdref (Univ.in_punivs cnst) [| |] in
      ()
  | _ -> user_err (Pp.str "not constant")

let monomorphization libref_list =
  List.iter monomorphization_single libref_list

let terminate_mono_global_def env evdref gref type_args =
  if List.mem_assoc (gref, type_args) !mono_global_visited then
    user_err (Pp.str "already defined")
  else
    let fctnt = destConstRef gref in
    let id_term = mkApp ((mkConst fctnt), type_args) in
    let term = id_term in
    let term = deanonymize_term env !evdref term in
    let id = find_unused_name (mangle_function fctnt (Array.map (EConstr.to_constr !evdref) type_args)) in
    let constant = Declare.declare_definition id
      (EConstr.to_constr !evdref term,
       Entries.Monomorphic_const_entry Univ.ContextSet.empty) in
    Feedback.msg_info (Id.print id ++ spc () ++ str ":=" ++ spc() ++ Printer.pr_constr_env env !evdref (EConstr.to_constr !evdref term));
    mono_global_visited := ((gref, type_args), constant) :: !mono_global_visited

let terminate_mono env evdref term =
  match EConstr.kind !evdref term with
  | Constr.Const (ctnt, u) -> mono_check_const env evdref (ctnt, EInstance.kind !evdref u); terminate_mono_global_def env evdref (ConstRef ctnt) [| |]
  | App (f, args) ->
      (match kind !evdref f with
      | Const (fctnt, u) ->
          let fty = constant_type env evdref (fctnt, EInstance.kind !evdref u) in
          let num_type_args = count_type_args !evdref fty in
          (if Array.length args <> num_type_args then
            raise (CodeGenError "terminate_mono"));
          terminate_mono_global_def env evdref (ConstRef fctnt) args
      | _ -> user_err (Pp.str "not constant application"))
  | _ -> user_err (Pp.str "must be constant application")

let terminate_monomorphization (term : Constrexpr.constr_expr) =
  let (evd, env) = Pfedit.get_current_context () in
  let evdref = ref evd in
  let (term2, euc) = Constrintern.interp_constr env evd term in
  terminate_mono env evdref term2

