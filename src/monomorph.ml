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
open Goptions

open Monoutil

let rec copy_term term =
  match Term.kind_of_term term with
  | Term.Rel i -> Term.mkRel i
  | Term.Var name -> Term.mkVar name
  | Term.Meta i -> Term.mkMeta i
  | Term.Evar (ekey, termary) -> Term.mkEvar (ekey, (Array.map copy_term termary))
  | Term.Sort s -> Term.mkSort s
  | Term.Cast (expr, kind, ty) -> Term.mkCast (copy_term expr, kind, copy_term ty)
  | Term.Prod (name, ty, body) -> Term.mkProd (name, copy_term ty, copy_term body)
  | Term.Lambda (name, ty, body) -> Term.mkLambda (name, copy_term ty, copy_term body)
  | Term.LetIn (name, expr, ty, body) -> Term.mkLetIn (name, copy_term expr, copy_term ty, copy_term body)
  | Term.App (f, argsary) -> Term.mkApp (copy_term f, Array.map copy_term argsary)
  | Term.Const cu -> Term.mkConstU cu
  | Term.Ind iu -> Term.mkIndU iu
  | Term.Construct cu -> Term.mkConstructU cu
  | Term.Case (ci, tyf, expr, brs) -> Term.mkCase (ci, copy_term tyf, copy_term expr, Array.map copy_term brs)
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      Term.mkFix ((ia, i), (nameary, Array.map copy_term tyary, Array.map copy_term funary))
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      Term.mkCoFix (i, (nameary, Array.map copy_term tyary, Array.map copy_term funary))
  | Term.Proj (proj, expr) ->
      Term.mkProj (proj, copy_term expr)

let rec subst_term context term =
  match Term.kind_of_term term with
  | Term.Rel i ->
      (if List.length context <= i-1 then
        Term.mkRel i
      else
        match List.nth context (i-1) with
        | None -> Term.mkRel i
        | Some tm -> tm) (* assume tm has no Rel. *)
  | Term.Var name -> Term.mkVar name
  | Term.Meta i -> Term.mkMeta i
  | Term.Evar (ekey, termary) -> Term.mkEvar (ekey, (Array.map (subst_term context) termary))
  | Term.Sort s -> Term.mkSort s
  | Term.Cast (expr, kind, ty) -> Term.mkCast (subst_term context expr, kind, subst_term context ty)
  | Term.Prod (name, ty, body) -> Term.mkProd (name, subst_term context ty, subst_term (None :: context) body)
  | Term.Lambda (name, ty, body) -> Term.mkLambda (name, subst_term context ty, subst_term (None :: context) body)
  | Term.LetIn (name, expr, ty, body) -> Term.mkLetIn (name, subst_term context expr, subst_term context ty, subst_term (None :: context) body)
  | Term.App (f, argsary) -> Term.mkApp (subst_term context f, Array.map (subst_term context) argsary)
  | Term.Const cu -> Term.mkConstU cu
  | Term.Ind iu -> Term.mkIndU iu
  | Term.Construct cu -> Term.mkConstructU cu
  | Term.Case (ci, tyf, expr, brs) -> Term.mkCase (ci, subst_term context tyf, subst_term context expr, Array.map (subst_term context) brs)
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      let context2 = Array.fold_right (fun _ ctx -> None :: ctx) funary context in
      Term.mkFix ((ia, i), (nameary, Array.map (subst_term context) tyary, Array.map (subst_term context2) funary))
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      let context2 = Array.fold_right (fun _ ctx -> None :: ctx) funary context in
      Term.mkCoFix (i, (nameary, Array.map (subst_term context) tyary, Array.map (subst_term context2) funary))
  | Term.Proj (proj, expr) ->
      Term.mkProj (proj, subst_term context expr)

let rec has_rel term =
  match Term.kind_of_term term with
  | Term.Rel i -> true
  | Term.Var name -> false
  | Term.Meta i -> false
  | Term.Evar (ekey, termary) -> false
  | Term.Sort s -> false
  | Term.Cast (expr, kind, ty) -> has_rel expr || has_rel ty
  | Term.Prod (name, ty, body) -> has_rel ty || has_rel body
  | Term.Lambda (name, ty, body) -> has_rel ty || has_rel body
  | Term.LetIn (name, expr, ty, body) -> has_rel expr || has_rel ty || has_rel body
  | Term.App (f, argsary) -> has_rel f || array_exists has_rel argsary
  | Term.Const cu -> false
  | Term.Ind iu -> false
  | Term.Construct cu -> false
  | Term.Case (ci, tyf, expr, brs) -> has_rel tyf || has_rel expr || array_exists has_rel brs
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      array_exists has_rel tyary || array_exists has_rel funary
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      array_exists has_rel tyary || array_exists has_rel funary
  | Term.Proj (proj, expr) ->
      has_rel expr

let is_sort term =
  match Term.kind_of_term term with
  | Term.Sort s -> true
  | _ -> false

let rec has_sort term =
  match Term.kind_of_term term with
  | Term.Rel i -> false
  | Term.Var name -> false
  | Term.Meta i -> false
  | Term.Evar (ekey, termary) -> false
  | Term.Sort s -> true
  | Term.Cast (expr, kind, ty) -> has_sort expr || has_sort ty
  | Term.Prod (name, ty, body) -> has_sort ty || has_sort body
  | Term.Lambda (name, ty, body) -> has_sort ty || has_sort body
  | Term.LetIn (name, expr, ty, body) -> has_sort expr || has_sort ty || has_sort body
  | Term.App (f, argsary) -> has_sort f || array_exists has_sort argsary
  | Term.Const cu -> false
  | Term.Ind iu -> false
  | Term.Construct cu -> false
  | Term.Case (ci, tyf, expr, brs) -> has_sort tyf || has_sort expr || array_exists has_sort brs
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      array_exists has_sort tyary || array_exists has_sort funary
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      array_exists has_sort tyary || array_exists has_sort funary
  | Term.Proj (proj, expr) ->
      has_sort expr

let deanonymize_term env term =
  let rec r env term =
    match Term.kind_of_term term with
    | Term.Rel i -> term
    | Term.Var name -> term
    | Term.Meta i -> term
    | Term.Evar (ekey, termary) -> Term.mkEvar (ekey, (Array.map (r env) termary))
    | Term.Sort s -> term
    | Term.Cast (expr, kind, ty) -> Term.mkCast (r env expr, kind, r env ty)
    | Term.Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = Environ.push_rel decl env in
        Namegen.mkProd_name env (name, r env ty, r env2 body)
    | Term.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = Environ.push_rel decl env in
        Namegen.mkLambda_name env (name, r env ty, r env2 body)
    | Term.LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = Environ.push_rel decl env in
        Term.mkLetIn (Namegen.named_hd env ty name, r env expr, r env ty, r env2 body)
    | Term.App (f, argsary) -> Term.mkApp (r env f, Array.map (r env) argsary)
    | Term.Const (cnst, u) -> term
    | Term.Ind (ind, u) -> term
    | Term.Construct (cstr, u) -> term
    | Term.Case (ci, tyf, expr, brs) -> Term.mkCase (ci, r env tyf, r env expr, Array.map (r env) brs)
    | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, tyary, funary) env in
        let nameary2 = array_map2 (Namegen.named_hd env) tyary nameary in
        Term.mkFix ((ia, i), (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, tyary, funary) env in
        let nameary2 = array_map2 (Namegen.named_hd env) tyary nameary in
        Term.mkCoFix (i, (nameary2, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.Proj (proj, expr) ->
        Term.mkProj (proj, r env expr)
  in
  r env term

let expand_type env evdref term =
  let rec r env term =
    if Term.isProd term then
      r2 env term
    else
      let termty = Typing.e_type_of env evdref term in
      if Term.isSort termty then
        let term' = Reduction.whd_all env term in
        r2 env term'
      else
        r2 env term
  and r2 env term =
    match Term.kind_of_term term with
    | Term.Rel i -> term
    | Term.Var name -> term
    | Term.Meta i -> term
    | Term.Evar (ekey, termary) -> Term.mkEvar (ekey, (Array.map (r env) termary))
    | Term.Sort s -> term
    | Term.Cast (expr, kind, ty) -> Term.mkCast (r env expr, kind, r env ty)
    | Term.Prod (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = Environ.push_rel decl env in
        Term.mkProd (name, r env ty, r env2 body)
    | Term.Lambda (name, ty, body) ->
        let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
        let env2 = Environ.push_rel decl env in
        Term.mkLambda (name, r env ty, r env2 body)
    | Term.LetIn (name, expr, ty, body) ->
        let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
        let env2 = Environ.push_rel decl env in
        Term.mkLetIn (name, r env expr, r env ty, r env2 body)
    | Term.App (f, argsary) -> Term.mkApp (r env f, Array.map (r env) argsary)
    | Term.Const (cnst, u) -> term
    | Term.Ind (ind, u) -> term
    | Term.Construct (cstr, u) -> term
    | Term.Case (ci, tyf, expr, brs) -> Term.mkCase (ci, r env tyf, r env expr, Array.map (r env) brs)
    | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, tyary, funary) env in
        Term.mkFix ((ia, i), (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.CoFix (i, (nameary, tyary, funary)) ->
        let env2 = Environ.push_rec_types (nameary, tyary, funary) env in
        Term.mkCoFix (i, (nameary, Array.map (r env) tyary, Array.map (r env2) funary))
    | Term.Proj (proj, expr) ->
        Term.mkProj (proj, r env expr)
  in
  r env term

let type_of env evdref term =
  let ty = Typing.e_type_of env evdref term in
  expand_type env evdref ty

let constant_type env evdref cu =
  let ft = Environ.constant_type env cu in
  match ft with
  | Declarations.RegularArity ty, _ -> expand_type env evdref ty (* xxx: handle univ *)
  | Declarations.TemplateArity _, _ -> assert false

let rec count_type_args fty =
  match Term.kind_of_term fty with
  | Term.Prod (name, ty, body) ->
    if is_sort ty then
      1 + count_type_args body
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

let rec eq_typeary_rec types1 types2 i =
  if i = 0 then
    true
  else
  let j = i - 1 in
  if Term.eq_constr (Array.get types1 j) (Array.get types2 j) then
    eq_typeary_rec types1 types2 j
  else
    false

let eq_typeary types1 types2 =
  let n1 = Array.length types1 in
  let n2 = Array.length types2 in
  if n1 <> n2 then
    false
  else
    eq_typeary_rec types1 types2 n1

let beta_lambda_list expr args =
  let n = List.length args in
  let body =
    List.fold_left
      (fun e _ ->
        match Term.kind_of_term e with
        | Term.Lambda (name, ty, body) -> body
        | _ -> raise (Invalid_argument "beta_lambda_list"))
      expr args
  in
  Vars.lift (-n) (subst_term args body)

let beta_lambda_ary expr args =
  beta_lambda_list expr (Array.to_list (Array.map (fun arg -> Some arg) args))

let beta_prod_list expr args =
  let n = List.length args in
  let body =
    List.fold_left
      (fun e _ ->
        match Term.kind_of_term e with
        | Term.Prod (name, ty, body) -> body
        | _ -> raise (Invalid_argument "beta_prod_list"))
      expr args
  in
  Vars.lift (-n) (subst_term args body)

let beta_prod_ary ty args =
  beta_prod_list ty (Array.to_list (Array.map (fun arg -> Some arg) args))

let rec mono_local_rec context term =
(*Feedback.msg_info (str "mono_local_rec:start");*)
  match Term.kind_of_term term with
  | Term.Rel i ->
(*Feedback.msg_info (str "mono_local_rec:rel:i=" ++ int i);*)
      (match List.nth context (i-1) with
      | None ->
(*Feedback.msg_info (str "mono_local_rec:rel:none");*)
          fun acc -> Term.mkRel (List.hd acc - List.nth acc (i-1) + 1)
      | Some (num_type_args, refs) ->
(*Feedback.msg_info (str "mono_local_rec:rel:some");*)
          if num_type_args = 0 then
            (if !refs = [] then
              refs := [| |] :: !refs;
            fun acc ->
            Term.mkRel (List.hd acc - List.nth acc (i-1) + 1))
          else
            raise (MonomorphizationError "mono_local_rec:rel"))
  | Term.Var name -> fun acc -> Term.mkVar name
  | Term.Meta i -> fun acc -> Term.mkMeta i
  | Term.Evar (ekey, termary) ->
      let ary = Array.map (mono_local_rec context) termary in
      fun acc -> Term.mkEvar (ekey, Array.map (fun f -> f acc) ary)
  | Term.Sort s -> fun acc -> Term.mkSort s
  | Term.Cast (expr, kind, ty) ->
      let expr' = mono_local_rec context expr in
      let ty' = mono_local_rec context ty in
      fun acc -> Term.mkCast (expr' acc, kind, ty' acc)
  | Term.Prod (name, ty, body) ->
      let ty' = mono_local_rec context ty in
      let body' = mono_local_rec (None :: context) body in
      fun acc -> Term.mkProd (name, ty' acc, body' ((1 + List.hd acc) :: acc))
  | Term.Lambda (name, ty, body) ->
(*Feedback.msg_info (str "mono_local_rec:lambda");*)
      let ty' = mono_local_rec context ty in
      let body' = mono_local_rec (None :: context) body in
      fun acc -> Term.mkLambda (name, ty' acc, body' ((1 + List.hd acc) :: acc))
  | Term.LetIn (name, expr, ty, body) ->
(*Feedback.msg_info (str "mono_local_rec:let");*)
      let num_type_args = count_type_args ty in
(*Feedback.msg_info (str "mono_local_rec:let:1:num_type_args=" ++ int num_type_args);*)
      let refs : Term.constr array list ref = ref [] in
(*Feedback.msg_info (str "mono_local_rec:let:2");*)
      let body' = mono_local_rec (Some (num_type_args, refs) :: context) body in
(*Feedback.msg_info (str "mono_local_rec:let:3");*)
      let exprs = List.map (fun type_args -> mono_local_rec context (beta_lambda_ary expr type_args)) !refs in
(*Feedback.msg_info (str "mono_local_rec:let:4");*)
      let tys = List.map (fun type_args -> mono_local_rec context (beta_prod_ary ty type_args)) !refs in
(*Feedback.msg_info (str "mono_local_rec:let:5");*)
      fun acc ->
      List.fold_left2
        (fun b e t -> Term.mkLetIn (name, e acc, t acc, b))
        (body' ((List.length exprs + List.hd acc) :: acc))
        exprs tys
  | Term.App (f, argsary) ->
      (match (Term.kind_of_term f) with
      | Term.Rel i ->
          (match List.nth context (i-1) with
          | None ->
              let argsary' = Array.map (mono_local_rec context) argsary in
              fun acc -> Term.mkApp (Term.mkRel (List.hd acc - List.nth acc (i-1) + 1), Array.map (fun arg -> arg acc) argsary')
          | Some (num_type_args, refs) ->
              (if Array.length argsary < num_type_args then
                raise (MonomorphizationError "mono_local_rec:app");
              let type_args = Array.sub argsary 0 num_type_args in
              (* xxx: check no Rel in type_args *)
              if not (List.exists (eq_typeary type_args) !refs) then
                refs := type_args :: !refs;
              let argsary' = Array.map (mono_local_rec context) (Array.sub argsary num_type_args (Array.length argsary - num_type_args)) in
              fun acc ->
              Term.mkApp
                (Term.mkRel (List.hd acc - List.nth acc (i-1) + 1 + list_find_index (eq_typeary type_args) !refs),
                (Array.map (fun arg -> arg acc)) argsary')))
      | _ ->
          let f' = mono_local_rec context f in
          let argsary' = Array.map (mono_local_rec context) argsary in
          fun acc -> Term.mkApp (f' acc, Array.map (fun arg -> arg acc) argsary'))
  | Term.Const cu -> fun acc -> Term.mkConstU cu
  | Term.Ind iu ->
(*Feedback.msg_info (str "mono_local_rec:ind");*)
      fun acc -> Term.mkIndU iu
  | Term.Construct cu ->
(*Feedback.msg_info (str "mono_local_rec:construct");*)
      fun acc -> Term.mkConstructU cu
  | Term.Case (ci, tyf, expr, brs) ->
      let tyf' = mono_local_rec context tyf in
      let expr' = mono_local_rec context expr in
      let brs' = Array.map (mono_local_rec context) brs in
      fun acc ->
      Term.mkCase (ci, tyf' acc, expr' acc, Array.map (fun br -> br acc) brs')
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      let n = Array.length funary in
      let tyary' = Array.map (mono_local_rec context) tyary in
      let funary' = Array.map (mono_local_rec (ncons n None context)) funary in
      fun acc ->
      let acc' = List.rev (iota_list (List.hd acc + 1) n) @ acc in
      Term.mkFix ((ia, i), (nameary, Array.map (fun ty -> ty acc) tyary', Array.map (fun f -> f acc') funary'))
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      let n = Array.length funary in
      let tyary' = Array.map (mono_local_rec context) tyary in
      let funary' = Array.map (mono_local_rec (ncons n None context)) funary in
      fun acc ->
      let acc' = List.rev (iota_list (List.hd acc + 1) n) @ acc in
      Term.mkCoFix (i, (nameary, Array.map (fun ty -> ty acc) tyary', Array.map (fun f -> f acc') funary'))
  | Term.Proj (proj, expr) ->
      let expr' = mono_local_rec context expr in
      fun acc ->
      Term.mkProj (proj, expr' acc)

let mono_local term = mono_local_rec [] term [0]

let simple_fun_p term =
  match Term.kind_of_term term with
  | Term.Rel _ | Term.Const _ | Term.Construct _ -> true
  | _ -> false

let simple_arg_p term =
  match Term.kind_of_term term with
  | Term.Rel _ -> true
  | _ -> false

let rec hoist_terms simple_p env evdref terms bodyfun =
  match terms with
  | [] ->
      bodyfun env [] (fun (t : Term.constr) -> t)
  | term :: rest ->
      if simple_p term then
        hoist_terms simple_p env evdref rest
          (fun env rest' shifter ->
            bodyfun env (shifter term :: rest') shifter)
      else
        let ty = type_of env evdref term in
        let name = Names.Name.Anonymous in
        let expr = stmt_rec env evdref term in
        let env1 = Environ.push_rel (Context.Rel.Declaration.LocalDef (name, expr, ty)) env in
        Term.mkLetIn (name, expr, ty,
          (hoist_terms simple_p env1 evdref (List.map (Vars.lift 1) rest)
            (fun env2 rest' shifter ->
              bodyfun
                env2
                ((shifter (Term.mkRel 1)) :: rest')
                (fun t -> (Vars.lift 1 (shifter t))))))

and hoist_term1 simple_p env evdref term bodyfun =
  hoist_terms simple_p env evdref [term]
    (fun env' terms' shifter -> bodyfun env' (List.hd terms') shifter)

and stmt_rec env evdref term =
  match Term.kind_of_term term with
  | Term.Rel i -> term
  | Term.Var name -> term
  | Term.Meta i -> term
  | Term.Evar (ekey, termary) -> term
  | Term.Sort s -> term
  | Term.Cast (expr, kind, ty) ->
      hoist_term1 simple_arg_p env evdref expr
        (fun env' expr' shifter -> Term.mkCast (expr', kind, shifter ty))
  | Term.Prod (name, ty, body) -> term
  | Term.Lambda (name, ty, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = Environ.push_rel decl env in
      Term.mkLambda (name, ty, stmt_rec env2 evdref body)
  | Term.LetIn (name, expr, ty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = Environ.push_rel decl env in
      Term.mkLetIn (name, stmt_rec env evdref expr, ty, stmt_rec env2 evdref body)
  | Term.App (f, argsary) ->
      let fty = type_of env evdref f in
      let num_type_args = count_type_args fty in
      let targs = Array.sub argsary 0 num_type_args in
      let vargs = Array.sub argsary num_type_args (Array.length argsary - num_type_args) in
      hoist_term1 simple_fun_p env evdref f
        (fun env1 f1 shifter1 ->
          let targs1 = Array.map shifter1 targs in
          let vargs1 = Array.map shifter1 vargs in
          hoist_terms simple_arg_p env1 evdref (Array.to_list vargs1)
            (fun env2 fargs2 shifter2 ->
              Term.mkApp (shifter2 f1, (Array.append (Array.map shifter2 targs1) (Array.of_list fargs2)))))
  | Term.Const cu -> term
  | Term.Ind iu -> term
  | Term.Construct cu -> term
  | Term.Case (ci, tyf, expr, branches) ->
      hoist_term1 simple_arg_p env evdref expr
        (fun env' expr' shifter ->
          Term.mkCase (ci, (shifter tyf), expr', Array.map (fun branch -> stmt_rec env' evdref (shifter branch)) branches))
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      let decls = array_map2 (fun n ty -> Context.Rel.Declaration.LocalAssum (n, ty)) nameary tyary in
      let env2 = Array.fold_left (fun e d -> Environ.push_rel d e) env decls in
      Term.mkFix ((ia, i), (nameary, tyary, Array.map (stmt_rec env2 evdref) funary))
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      let decls = array_map2 (fun n ty -> Context.Rel.Declaration.LocalAssum (n, ty)) nameary tyary in
      let env2 = Array.fold_left (fun e d -> Environ.push_rel d e) env decls in
      Term.mkCoFix (i, (nameary, tyary, Array.map (stmt_rec env2 evdref) funary))
  | Term.Proj (proj, expr) ->
      hoist_term1 simple_arg_p env evdref expr
        (fun env' expr' shifter -> Term.mkProj (proj, expr'))

let stmt term =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let evdref = ref evd in
  stmt_rec env evdref term

let rec seq_let term =
  match Term.kind_of_term term with
  | Term.Rel i -> term
  | Term.Var name -> term
  | Term.Meta i -> term
  | Term.Evar (ekey, termary) -> term
  | Term.Sort s -> term
  | Term.Cast (expr, kind, ty) ->
      Term.mkCast ((seq_let expr), kind, ty)
  | Term.Prod (name, ty, body) -> term
  | Term.Lambda (name, ty, body) ->
      Term.mkLambda (name, ty, seq_let body)
  | Term.LetIn (name, expr, ty, body) ->
      (match Term.kind_of_term expr with
      | Term.LetIn (name1, expr1, ty1, body1) ->
          seq_let
            (Term.mkLetIn (name1, expr1, ty1,
              Term.mkLetIn (name, body1, Vars.lift 1 ty, Vars.liftn 1 2 body)))
      | _ -> Term.mkLetIn (name, seq_let expr, ty, seq_let body))
  | Term.App (f, argsary) -> term
  | Term.Const cu -> term
  | Term.Ind iu -> term
  | Term.Construct cu -> term
  | Term.Case (ci, tyf, expr, branches) ->
      Term.mkCase (ci, tyf, expr, Array.map seq_let branches)
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      Term.mkFix ((ia, i), (nameary, tyary, Array.map seq_let funary))
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      Term.mkCoFix (i, (nameary, tyary, Array.map seq_let funary))
  | Term.Proj (proj, expr) -> term

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
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
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
    else if Term.eq_constr args1.(i-1) args2.(i-1) then
      loop (i-1)
    else
      false
  in
  loop (Array.length args1)

let mono_global_visited_empty : ((global_reference * Term.constr array) * constant) list = []

let mono_global_visited = Summary.ref mono_global_visited_empty ~name:"MonomorphizationVisited"

let mono_check_const env evdref ctntu =
  let fty = constant_type env evdref ctntu in
  if has_sort fty then
    raise (MonomorphizationError "mono_check_const")
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

let rec mono_global_def env evdref fctntu type_args =
  let (fctnt, u) = fctntu in
  if List.mem_assoc (ConstRef fctnt, type_args) !mono_global_visited then
    List.assoc (ConstRef fctnt, type_args) !mono_global_visited
  else
    let id_term = Term.mkApp (Term.mkConst fctnt, type_args) in
    Feedback.msg_info (str "monomorphization start:" ++ Printer.pr_constr_env env !evdref id_term);
    let (term, uconstraints) = Environ.constant_value env fctntu in
    let term = expand_type env evdref term in
    Feedback.msg_info (str "monomorphization 1:" ++ Printer.pr_constr_env env !evdref id_term);
    let term = beta_lambda_ary term type_args in
    Feedback.msg_info (str "monomorphization 2:" ++ Printer.pr_constr_env env !evdref id_term);
    let term = mono_local term in
    Feedback.msg_info (str "monomorphization 3:" ++ Printer.pr_constr_env env !evdref id_term);
    let term = mono_global env evdref term in
    Feedback.msg_info (str "monomorphization 4:" ++ Printer.pr_constr_env env !evdref id_term);
    let term = stmt term in
    let term = seq_let term in
    Feedback.msg_info (str "monomorphization 5:" ++ Printer.pr_constr_env env !evdref id_term);
    let term = deanonymize_term env term in
    (* Feedback.msg_info (Printer.pr_constr_env env !evdref id_term ++ spc () ++ str ":=" ++ spc() ++ Printer.pr_constr term);*)
    let id = find_unused_name (mangle_function fctnt type_args) in
    let constant = Declare.declare_definition id (term, (Univ.ContextSet.add_constraints uconstraints Univ.ContextSet.empty)) in
    Feedback.msg_info (Id.print id ++ spc () ++ str ":=" ++ spc() ++ Printer.pr_constr (Term.mkApp ((Term.mkConstU fctntu), type_args)));
    mono_global_visited := ((ConstRef fctnt, type_args), constant) :: !mono_global_visited;
    Feedback.msg_info (str "monomorphization end:" ++ Printer.pr_constr_env env !evdref id_term);
    constant

and mono_global_const_app env evdref fctntu argsary =
  let fty = constant_type env evdref fctntu in
  let num_type_args = count_type_args fty in
  (if Array.length argsary < num_type_args then
    raise (MonomorphizationError "mono_global_const_app"));
  let type_args = Array.sub argsary 0 num_type_args in
  let rest_args = Array.sub argsary num_type_args (Array.length argsary - num_type_args) in
  let constant = mono_global_def env evdref fctntu type_args in
  Term.mkApp (Term.mkConst constant, rest_args)

and mono_constr_def env fcstr mutind i j param_args =
  if List.mem_assoc (ConstructRef fcstr, param_args) !mono_global_visited then
    List.assoc (ConstructRef fcstr, param_args) !mono_global_visited
  else
    let term = Term.mkApp (Term.mkConstruct fcstr, param_args) in
    let term = deanonymize_term env term in
    let id = find_unused_name (Id.of_string (mangle_constructor fcstr param_args)) in
    let constant = Declare.declare_definition id (term, Univ.ContextSet.empty) in
    mono_global_visited := ((ConstructRef fcstr, param_args), constant) :: !mono_global_visited;
    constant

and mono_global_cstr_app env fcstru argsary =
  let fcstr = Univ.out_punivs fcstru in
  let ((mutind, i), j) = fcstr in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  let num_indparams = List.length oneind_body.Declarations.mind_arity_ctxt in
  let param_args = Array.sub argsary 0 num_indparams in
  let rest_args = Array.sub argsary num_indparams (Array.length argsary - num_indparams) in
  let constant = mono_constr_def env fcstr mutind i j param_args in
  Term.mkApp (Term.mkConst constant, rest_args);

and mono_global env evdref term =
Feedback.msg_info (str "mono_global:start " ++ Printer.pr_constr term);
  match Term.kind_of_term term with
  | Term.Rel i -> Term.mkRel i
  | Term.Var name -> Term.mkVar name
  | Term.Meta i -> Term.mkMeta i
  | Term.Evar (ekey, termary) -> Term.mkEvar (ekey, (Array.map (mono_global env evdref) termary))
  | Term.Sort s -> Term.mkSort s
  | Term.Cast (expr, kind, ty) -> Term.mkCast (mono_global env evdref expr, kind, mono_global env evdref ty)
  | Term.Prod (name, ty, body) -> Term.mkProd (name, mono_global env evdref ty, mono_global env evdref body)
  | Term.Lambda (name, ty, body) -> Term.mkLambda (name, mono_global env evdref ty, mono_global env evdref body)
  | Term.LetIn (name, expr, ty, body) -> Term.mkLetIn (name, mono_global env evdref expr, mono_global env evdref ty, mono_global env evdref body)
  | Term.App (f, argsary) ->
      (match (Term.kind_of_term f) with
      | Term.Const fctntu -> mono_global_const_app env evdref fctntu (Array.map (mono_global env evdref) argsary)
      | Term.Construct fcstru -> mono_global_cstr_app env fcstru (Array.map (mono_global env evdref) argsary)
      | _ -> Term.mkApp (mono_global env evdref f, Array.map (mono_global env evdref) argsary))
  | Term.Const ctntu -> mono_check_const env evdref ctntu; mono_global_const_app env evdref ctntu [| |]
  | Term.Ind iu -> Term.mkIndU iu
  | Term.Construct cstru -> mono_global_cstr_app env cstru [| |]
  | Term.Case (ci, tyf, expr, brs) -> Term.mkCase (ci, mono_global env evdref tyf, mono_global env evdref expr, Array.map (mono_global env evdref) brs)
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      Term.mkFix ((ia, i), (nameary, Array.map (mono_global env evdref) tyary, Array.map (mono_global env evdref) funary))
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      Term.mkCoFix (i, (nameary, Array.map (mono_global env evdref) tyary, Array.map (mono_global env evdref) funary))
  | Term.Proj (proj, expr) ->
      Term.mkProj (proj, mono_global env evdref expr)

let mono env evdref term = mono_global env evdref (mono_local term)

let monomorphization_single libref =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  match gref with
  | ConstRef cnst ->
      let _ = mono_global_def env evdref (Univ.in_punivs cnst) [| |] in
      ()
  | _ -> error "not constant"

let monomorphization libref_list =
  List.iter monomorphization_single libref_list

let rec terminate_mono_global_def env evdref gref type_args =
  if List.mem_assoc (gref, type_args) !mono_global_visited then
    error "already defined"
  else
    let fctnt = destConstRef gref in
    let id_term = Term.mkApp ((Term.mkConst fctnt), type_args) in
    let term = id_term in
    let term = deanonymize_term env term in
    let id = find_unused_name (mangle_function fctnt type_args) in
    let constant = Declare.declare_definition id (term, Univ.ContextSet.empty) in
    Feedback.msg_info (Id.print id ++ spc () ++ str ":=" ++ spc() ++ Printer.pr_constr term);
    mono_global_visited := ((gref, type_args), constant) :: !mono_global_visited

let terminate_mono env evdref term =
  match Term.kind_of_term term with
  | Term.Const (ctnt, u) -> mono_check_const env evdref (ctnt, u); terminate_mono_global_def env evdref (ConstRef ctnt) [| |]
  | Term.App (f, args) ->
      (match Term.kind_of_term f with
      | Term.Const (fctnt, u) ->
          let fty = constant_type env evdref (fctnt, u) in
          let num_type_args = count_type_args fty in
          (if Array.length args <> num_type_args then
            raise (MonomorphizationError "terminate_mono"));
          terminate_mono_global_def env evdref (ConstRef fctnt) args
      | _ -> error "not constant application")
  | _ -> error "must be constant application"

let terminate_monomorphization (term : Constrexpr.constr_expr) =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let evdref = ref evd in
  let ((term2 : Term.constr), (euc : Evd.evar_universe_context)) = Constrintern.interp_constr env evd term in
  terminate_mono env evdref term2

