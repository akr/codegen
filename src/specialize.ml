(*
Copyright (C) 2019- National Institute of Advanced Industrial Science and Technology (AIST)

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

(* open Term *)
open Constr
open EConstr

open CErrors

open Cgenutil

module ConstrMap = HMap.Make(Constr)

type specialization_instance_name_status =
  SpNoName | SpExpectedId of Id.t | SpDefinedCtnt of Constant.t

type specialization_instance = {
  sp_static_arguments : Constr.t list; (* The length should be equal to number of "s" *)
  sp_partapp_ctnt : Constant.t;
  sp_specialization_name : specialization_instance_name_status;
  sp_cfunc_name : string option;
}

type specialization_config = {
  (* sp_func : Constant.t; *)
  sp_sd_list : s_or_d list;
  sp_instance_map : specialization_instance ConstrMap.t;
}

let specialize_config_map = Summary.ref (Cmap.empty : specialization_config Cmap.t) ~name:"CodegenSpecialize"

let codegen_print_specialization funcs =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pr_inst sp_inst =
    let pr_names =
      Pp.str "=>" ++ spc () ++
      Printer.pr_constant env sp_inst.sp_partapp_ctnt ++ spc () ++
      (match sp_inst.sp_specialization_name with
      | SpNoName -> Pp.str "_"
      | SpExpectedId id -> Pp.str "(" ++ Id.print id ++ Pp.str ")"
      | SpDefinedCtnt ctnt -> Printer.pr_constant env ctnt)
    in
    let pr_inst_list = List.map (Printer.pr_constr_env env sigma)
                                sp_inst.sp_static_arguments in
    pp_prejoin_list (spc ()) pr_inst_list ++ spc () ++
    pr_names
  in
  let pr_cfg (func, sp_cfg) =
    Feedback.msg_info (Pp.str "Specialization Arguments" ++ spc () ++
      Printer.pr_constant env func ++
      pp_prejoin_list (spc ()) (List.map pr_s_or_d sp_cfg.sp_sd_list) ++
      Pp.str ".");
    let feedback_instance sp_inst =
      Feedback.msg_info (Pp.str "Specialization Instance" ++ spc () ++
        Printer.pr_constant env func ++
        pr_inst sp_inst ++ Pp.str ".")
    in
    ConstrMap.iter (fun _ -> feedback_instance) sp_cfg.sp_instance_map
  in
  let l = if funcs = [] then
            Cmap.bindings !specialize_config_map |>
            (List.sort @@ fun (x,_) (y,_) -> Constant.CanOrd.compare x y)
          else
            funcs |> List.map @@ fun func ->
              let gref = Smartlocate.global_with_alias func in
              let ctnt = match gref with
                | ConstRef ctnt -> ctnt
                | _ -> user_err (Pp.str "not a constant:" ++ spc () ++
                                 Printer.pr_global gref)
              in
              (ctnt, Cmap.get ctnt !specialize_config_map)
  in
  Feedback.msg_info (Pp.str "Number of generic functions:" ++ spc () ++ Pp.int (Cmap.cardinal !specialize_config_map));
  List.iter pr_cfg l

let ctnt_of_qualid env qualid =
  let gref = Smartlocate.global_with_alias qualid in
  match gref with
    | ConstRef ctnt -> ctnt
    | _ -> user_err (Pp.str "not a constant:" ++ spc () ++ Printer.pr_global gref)

let codegen_specialization_define_arguments ctnt sd_list =
  let sp_cfg = { sp_sd_list=sd_list; sp_instance_map = ConstrMap.empty } in
  specialize_config_map := Cmap.add ctnt sp_cfg !specialize_config_map;
  sp_cfg

let codegen_specialization_arguments (func : Libnames.qualid) (sd_list : s_or_d list) =
  let env = Global.env () in
  let ctnt = ctnt_of_qualid env func in
  (if Cmap.mem ctnt !specialize_config_map then
    user_err (Pp.str "specialization already configured:" ++ spc () ++ Printer.pr_constant env ctnt));
  ignore (codegen_specialization_define_arguments ctnt sd_list);
  Feedback.msg_info (Pp.str "Specialization arguments defined:" ++ spc () ++ Printer.pr_constant env ctnt)

let rec determine_sd_list env sigma ty =
  (* Feedback.msg_info (Printer.pr_econstr_env env sigma ty); *)
  let ty = Reductionops.whd_all env sigma ty in
  match EConstr.kind sigma ty with
  | Prod (x,t,c) ->
      let t = Reductionops.whd_all env sigma t in
      let sd =
        if EConstr.isSort sigma t then
          SorD_S
        else
          SorD_D
      in
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env = EConstr.push_rel decl env in
      sd :: determine_sd_list env sigma c
  | _ -> []

let codegen_specialization_auto_arguments_internal
    (env : Environ.env) (sigma : Evd.evar_map)
    (ctnt : Constant.t) : specialization_config =
  match Cmap.find_opt ctnt !specialize_config_map with
  | Some sp_cfg -> sp_cfg (* already defined *)
  | None ->
      let (ty, _) = Environ.constant_type env (Univ.in_punivs ctnt) in
      let ty = EConstr.of_constr ty in
      let sd_list = (determine_sd_list env sigma ty) in
      codegen_specialization_define_arguments ctnt sd_list

let codegen_specialization_auto_arguments_1 (env : Environ.env) (sigma : Evd.evar_map)
    (func : Libnames.qualid) =
  let ctnt = ctnt_of_qualid env func in
  ignore (codegen_specialization_auto_arguments_internal env sigma ctnt)

let codegen_specialization_auto_arguments (func_list : Libnames.qualid list) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  List.iter (codegen_specialization_auto_arguments_1 env sigma) func_list

let drop_trailing_d sd_list =
  List.fold_right (fun sd l -> match (sd,l) with (SorD_D,[]) -> [] | _ -> sd :: l) sd_list []

let build_partapp (env : Environ.env) (sigma : Evd.evar_map)
    (ctnt : Constant.t) (sd_list : s_or_d list)
    (static_args : Constr.t list) : (Evd.evar_map * Constr.t) =
  let rec aux env f f_type sd_list static_args =
    match sd_list with
    | [] -> f
    | sd :: sd_list' ->
        let f_type = Reductionops.whd_all env sigma f_type in
        (match EConstr.kind sigma f_type with
        | Prod (x,t,c) ->
            (match sd with
            | SorD_S ->
                (match static_args with
                | [] -> user_err (Pp.str "needs more argument")
                | arg :: static_args' ->
                    let f' = mkApp (f, [| arg |]) in
                    let f_type' = Termops.prod_applist sigma f_type [arg] in
                    aux env f' f_type' sd_list' static_args')
            | SorD_D ->
                (let f1 = EConstr.Vars.lift 1 f in
                let f1app = mkApp (f1, [| mkRel 1 |]) in
                let decl = Context.Rel.Declaration.LocalAssum (x, t) in
                let env = EConstr.push_rel decl env in
                mkLambda (x, t, aux env f1app c sd_list' static_args)))
        | _ -> user_err (Pp.str "needs a function type"))
  in
  let sigma0 = sigma in
  let sd_list = drop_trailing_d sd_list in
  let (f_type, _) = Environ.constant_type env (Univ.in_punivs ctnt) in
  let f_type = EConstr.of_constr f_type in
  let f = mkConst ctnt in
  let t = aux env f f_type sd_list (List.map EConstr.of_constr static_args) in
  let (sigma, ty) = Typing.type_of env sigma t in
  Pretyping.check_evars env sigma0 sigma t;
  let t = Evarutil.flush_and_check_evars sigma t in
  (sigma, t)

let gensym_partapp_num = Summary.ref 0 ~name:"CodegenPartAppNum"
let gensym_partapp suffix =
  let n = !gensym_partapp_num in
  gensym_partapp_num := n + 1;
  let s = "codegen_p" ^ string_of_int n in
  let s = if suffix = "" then
            s
          else
            s ^ "_" ^ suffix
  in
  Id.of_string s

let interp_args (env : Environ.env) (sigma : Evd.evar_map)
    (user_args : Constrexpr.constr_expr list) : Evd.evar_map * Constr.t list =
  let interp_arg sigma user_arg =
    let sigma0 = sigma in
    let (sigma, arg) = Constrintern.interp_constr_evars env sigma user_arg in
    (* Feedback.msg_info (Printer.pr_econstr_env env sigma arg); *)
    Pretyping.check_evars env sigma0 sigma arg;
    let arg = Evarutil.flush_and_check_evars sigma arg in
    (sigma, arg)
  in
  CList.fold_left_map interp_arg sigma user_args

let specialization_instance_internal env sigma ctnt static_args names_opt =
  let sp_cfg = match Cmap.find_opt ctnt !specialize_config_map with
    | None -> user_err (Pp.str "specialization arguments not configured")
    | Some sp_cfg -> sp_cfg
  in
  let (sigma, partapp) = build_partapp env sigma ctnt sp_cfg.sp_sd_list static_args in
  (if ConstrMap.mem partapp sp_cfg.sp_instance_map then
    user_err (Pp.str "specialization instance already configured"));
  let specialization_name = (match names_opt with
      | Some { spi_specialized_id = Some id } -> SpExpectedId id | _ -> SpNoName) in
  let cfunc_name = (match names_opt with
      | Some { spi_cfunc_name = Some name } -> Some name | _ -> None) in
  let sp_inst =
    if List.for_all (fun sd -> sd = SorD_D) sp_cfg.sp_sd_list then
      {
        sp_static_arguments = [];
        sp_partapp_ctnt = ctnt; (* use the original function for fully dynamic function *)
        sp_specialization_name = specialization_name;
        sp_cfunc_name = cfunc_name;
      }
    else
      let partapp_id = match names_opt with
        | Some { spi_partapp_id = Some id } -> id | _ -> gensym_partapp (Label.to_string (Constant.label ctnt)) in
      let univs = Evd.univ_entry ~poly:false sigma in
      let defent = Entries.DefinitionEntry (Declare.definition_entry ~univs:univs partapp) in
      let kind = Decl_kinds.IsDefinition Decl_kinds.Definition in
      let declared_ctnt = Declare.declare_constant partapp_id (defent, kind) in
      {
        sp_static_arguments = static_args;
        sp_partapp_ctnt = declared_ctnt;
        sp_specialization_name = specialization_name;
        sp_cfunc_name = (match names_opt with
          | Some { spi_cfunc_name = Some name } -> Some name | _ -> None);
      }
  in
  let inst_map = ConstrMap.add partapp sp_inst sp_cfg.sp_instance_map in
  specialize_config_map := !specialize_config_map |>
    Cmap.add ctnt { sp_cfg with sp_instance_map = inst_map };
  sp_inst

let codegen_specialization_instance
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr list)
    (names : sp_instance_names) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, args) = interp_args env sigma user_args in
  let ctnt = ctnt_of_qualid env func in
  ignore (specialization_instance_internal env sigma ctnt args (Some names));
  Feedback.msg_info (Pp.str "Specialization instance defined:" ++ spc () ++ Printer.pr_constant env ctnt)

let check_convertible phase env sigma t1 t2 =
  if Reductionops.is_conv env sigma t1 t2 then
    ()
  else
    user_err (Pp.str "translation inconvertible:" ++ spc () ++ Pp.str phase)

let specialize_global_inline = Summary.ref (Cpred.empty : Cpred.t) ~name:"CodegenGlobalInline"
let specialize_local_inline = Summary.ref (Cmap.empty : Cpred.t Cmap.t) ~name:"CodegenLocalInline"

let codegen_global_inline (funcs : Libnames.qualid list) =
  let env = Global.env () in
  let ctnts = List.map (ctnt_of_qualid env) funcs in
  let f pred ctnt = Cpred.add ctnt pred in
  specialize_global_inline := List.fold_left f !specialize_global_inline ctnts

let codegen_local_inline (func : Libnames.qualid) (funcs : Libnames.qualid list) =
  let env = Global.env () in
  let ctnt = ctnt_of_qualid env func in
  let ctnts = List.map (ctnt_of_qualid env) funcs in
  let local_inline = !specialize_local_inline in
  let pred = match Cmap.find_opt ctnt local_inline with
             | None -> Cpred.empty
             | Some pred -> pred in
  let f pred ctnt = Cpred.add ctnt pred in
  let pred' = List.fold_left f pred ctnts in
  specialize_local_inline := Cmap.add ctnt pred' local_inline

let inline1 (env : Environ.env) (sigma : Evd.evar_map) (pred : Cpred.t) (term : EConstr.t) =
  let trans = {
    TransparentState.tr_var = Id.Pred.empty;
    TransparentState.tr_cst = pred
  } in
  let reds = CClosure.RedFlags.red_add_transparent CClosure.RedFlags.no_red trans in
  let term = Reductionops.clos_norm_flags reds env sigma term in
  term

let inline (env : Environ.env) (sigma : Evd.evar_map) (pred : Cpred.t) (term : EConstr.t) =
  let result = inline1 env sigma pred term in
  check_convertible "inline" env sigma term result;
  result

let rec strict_safe_beta (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (* Feedback.msg_info (Pp.str "strict_safe_beta arg: " ++ Printer.pr_econstr_env env sigma term); *)
  let result = strict_safe_beta1 env sigma term in
  (* Feedback.msg_info (Pp.str "strict_safe_beta ret: " ++ Printer.pr_econstr_env env sigma result); *)
  check_convertible "strict_safe_beta" env sigma term result;
  result
and strict_safe_beta1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _
  | Const _ | Ind _ | Int _ | Construct _ -> term
  | Cast (e, ck, ty) -> mkCast (strict_safe_beta env sigma e, ck, ty)
  | Lambda (n, ty, e) ->
      let decl = Context.Rel.Declaration.LocalAssum (n, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (n, ty, strict_safe_beta env2 sigma e)
  | LetIn (n, e, ty, b) ->
      let decl = Context.Rel.Declaration.LocalDef (n, e, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLetIn (n, strict_safe_beta env sigma e, ty, strict_safe_beta env2 sigma b)
  | App (f, args) ->
      let f = strict_safe_beta env sigma f in
      let args = Array.map (strict_safe_beta env sigma) args in
      let rec aux f i =
        match EConstr.kind sigma f with
        | Lambda (n, ty, e) when i < Array.length args ->
            let arg' = Vars.lift i args.(i) in
            mkLetIn (n, arg', ty, aux e (i+1))
        | _ ->
            let args' = Array.map (Vars.lift i)
                          (Array.sub args i (Array.length args - i)) in
            mkApp (f, args')
      in
      aux f 0
  | Case (ci, p, item, branches) ->
      mkCase (ci, p, strict_safe_beta env sigma item, Array.map (strict_safe_beta env sigma) branches)
  | Fix ((ia, i), ((nameary, tyary, funary))) ->
      let prec = (nameary, tyary, funary) in
      let env2 = push_rec_types prec env in
      mkFix ((ia, i), (nameary, tyary, Array.map (strict_safe_beta env2 sigma) funary))
  | CoFix (i, ((nameary, tyary, funary))) ->
      let prec = (nameary, tyary, funary) in
      let env2 = push_rec_types prec env in
      mkCoFix (i, (nameary, tyary, Array.map (strict_safe_beta env2 sigma) funary))
  | Proj (proj, e) -> mkProj (proj, strict_safe_beta env sigma e)

let rec normalizeK (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  Feedback.msg_info (Pp.str "normalizeK arg: " ++ Printer.pr_econstr_env env sigma term);
  let result = normalizeK1 env sigma term in
  Feedback.msg_info (Pp.str "normalizeK ret: " ++ Printer.pr_econstr_env env sigma result);
  check_convertible "normalizeK" env sigma term result;
  result
and normalizeK1 (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  let wrap_lets hoisted_exprs lifted_term =
    let hoisted_types = List.map (Retyping.get_type_of env sigma) hoisted_exprs in
    let hoisted_names = List.map (fun ty -> Context.nameR (Id.of_string (Namegen.hdchar env sigma ty))) hoisted_types in
    let rec aux i names exprs types acc_term =
      match names, exprs, types with
      | [], [], [] -> acc_term
      | x :: names', e :: exprs', ty :: types' ->
          let ty' = Vars.lift i ty in
          let e' = Vars.lift i (normalizeK env sigma e) in
          let acc_term' = aux (i+1) names' exprs' types' acc_term in
          mkLetIn (x, e', ty', acc_term')
      | _, _, _ -> user_err (Pp.str "inconsistent list length")
    in
    aux 0 hoisted_names hoisted_exprs hoisted_types lifted_term
  in
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Ind _
  | Const _ | Construct _ | Int _ | Prod _ -> term
  | Lambda (x,ty,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (x, ty, normalizeK env2 sigma b)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let prec = (nameary, tyary, funary) in
      let env2 = push_rec_types prec env in
      let funary' = Array.map (normalizeK env2 sigma) funary in
      mkFix ((ia, i), (nameary, tyary, funary'))
  | CoFix (i, (nameary, tyary, funary)) ->
      let prec = (nameary, tyary, funary) in
      let env2 = push_rec_types prec env in
      let funary' = Array.map (normalizeK env2 sigma) funary in
      mkCoFix (i, (nameary, tyary, funary'))
  | LetIn (x,e,ty,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, ty) in
      let env2 = EConstr.push_rel decl env in
      let e' = normalizeK env sigma e in
      let b' = normalizeK env2 sigma b in
      mkLetIn (x, e', ty, b')
  | Case (ci, p, item, branches) ->
      if isRel sigma item then
        mkCase (ci, p, item, Array.map (normalizeK env sigma) branches)
      else
        let term =
          mkCase (ci,
                  Vars.lift 1 p,
                  mkRel 1,
                  Array.map
                    (fun branch -> Vars.lift 1 (normalizeK env sigma branch))
                    branches)
        in
        wrap_lets [item] term
  | App (f,args) ->
      let hoist_f = not (isConst sigma f || isConstruct sigma f || isRel sigma f) in
      let hoist_args = Array.map (fun arg -> not (isRel sigma arg)) args in
      let nf = if hoist_f then 1 else 0 in
      let nargs = Array.fold_left (fun n b -> n + if b then 1 else 0) 0 hoist_args in
      let nlet = nf + nargs in
      let hoisted_args = CList.filter_with (Array.to_list hoist_args) (Array.to_list args) in
      let hoisted_exprs = if hoist_f then f :: hoisted_args else hoisted_args in
      let app =
	let f' = if hoist_f then mkRel nlet else Vars.lift nlet f in
        let (args', _) = array_fold_right_map
	  (fun arg n -> match EConstr.kind sigma arg with
			| Rel i -> (mkRel (i+nlet), n)
			| _ -> (mkRel n, n+1))
	  args 1
        in
        mkApp (f', args')
      in
      wrap_lets hoisted_exprs app
  | Cast (e,ck,ty) ->
      if isRel sigma e then term
      else wrap_lets [e] (mkCast (mkRel 1, ck, Vars.lift 1 ty))
  | Proj (proj, e) ->
      if isRel sigma e then term
      else wrap_lets [e] (mkProj (proj, mkRel 1))

let rec decompose_lets sigma term =
  match EConstr.kind sigma term with
  | LetIn (x, e, ty, b) ->
      let (defs, body) = decompose_lets sigma b in
      ((x, e, ty) :: defs, body)
  | _ -> ([], term)

let rec compose_lets defs body =
  match defs with
  | [] -> body
  | (x,e,ty) :: rest ->
      mkLetIn (x, e, ty, compose_lets rest body)

let linearize_top_let sigma x e ty b =
  let (defs, body) = decompose_lets sigma e in
  let n = List.length defs in
  compose_lets defs
    (mkLetIn (x, body, Vars.lift n ty, Vars.liftn n 2 b))

let rec linearize_lets_rec sigma term =
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Cast _ | Prod _ | App _
  | Const _ | Ind _ | Construct _ | Proj _ | Int _ -> term
  | Lambda (x, ty, b) ->
      mkLambda (x, ty, linearize_lets_rec sigma b)
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      mkFix ((ia, i), (nameary, tyary, Array.map (linearize_lets_rec sigma) funary))
  | CoFix (i, (nameary, tyary, funary)) ->
      mkCoFix (i, (nameary, tyary, Array.map (linearize_lets_rec sigma) funary))
  | Case (ci, p, item, branches) ->
      mkCase (ci, p, item, Array.map (linearize_lets_rec sigma) branches)
  | LetIn (x, e, ty, b) ->
      if isLetIn sigma e then
        linearize_lets_rec sigma (linearize_top_let sigma x e ty b)
      else
        mkLetIn (x, linearize_lets_rec sigma e, ty, linearize_lets_rec sigma b)

let linearize_lets env sigma term =
  let result = linearize_lets_rec sigma term in
  check_convertible "linearize_lets" env sigma term result;
  result

let normalizeA env sigma term =
  linearize_lets env sigma (normalizeK env sigma term)

let rec has_fv_rec sigma numrels term : bool =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _ | Int _
  | Const _ | Construct _ -> false
  | Rel i -> numrels < i
  | Evar (ev, es) ->
      Array.exists (has_fv_rec sigma numrels) es
  | Proj (proj, e) ->
      has_fv_rec sigma numrels e
  | Cast (e,ck,t) ->
      has_fv_rec sigma numrels e ||
      has_fv_rec sigma numrels t
  | App (f, args) ->
      has_fv_rec sigma numrels f ||
      Array.exists (has_fv_rec sigma numrels) args
  | LetIn (x,e,t,b) ->
      has_fv_rec sigma numrels e ||
      has_fv_rec sigma numrels t ||
      has_fv_rec sigma (numrels+1) b
  | Case (ci, p, item, branches) ->
      has_fv_rec sigma numrels p ||
      has_fv_rec sigma numrels item ||
      Array.exists (has_fv_rec sigma numrels) branches
  | Prod (x,t,b) ->
      has_fv_rec sigma numrels t ||
      has_fv_rec sigma (numrels+1) b
  | Lambda (x,t,b) ->
      has_fv_rec sigma numrels t ||
      has_fv_rec sigma (numrels+1) b
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let n = Array.length funary in
      Array.exists (has_fv_rec sigma numrels) tyary ||
      Array.exists (has_fv_rec sigma (numrels+n)) funary
  | CoFix (i, (nameary, tyary, funary)) ->
      let n = Array.length funary in
      Array.exists (has_fv_rec sigma numrels) tyary ||
      Array.exists (has_fv_rec sigma (numrels+n)) funary

let has_fv sigma term : bool =
  has_fv_rec sigma 0 term

let specialize_ctnt_app env sigma ctnt args =
  let sp_cfg = codegen_specialization_auto_arguments_internal env sigma ctnt in
  let sd_list = drop_trailing_d sp_cfg.sp_sd_list in
  (if Array.length args < List.length sd_list then
    user_err (Pp.str "Not enough arguments for" ++ spc () ++ (Printer.pr_constant env ctnt)));
  let sd_list = List.append sd_list (List.init (Array.length args - List.length sd_list) (fun _ -> SorD_D)) in
  let static_flags = List.map (fun sd -> sd = SorD_S) sd_list in
  let static_args = CArray.filter_with static_flags args in
  (Array.iter (fun arg ->
    if has_fv sigma arg then
      user_err (Pp.str "A free variable found in" ++ spc () ++ Printer.pr_econstr_env env sigma arg))
    static_args);
  let static_args = Array.map (Reductionops.nf_all env sigma) static_args in
  let static_args = CArray.map_to_list (EConstr.to_constr sigma) static_args in
  let (_, partapp) = build_partapp env sigma ctnt sd_list static_args in
  Feedback.msg_info (Pp.str "specialize partapp: " ++ Printer.pr_constr_env env sigma partapp);
  let sp_inst = match ConstrMap.find_opt partapp sp_cfg.sp_instance_map with
    | None -> specialization_instance_internal env sigma ctnt static_args None
    | Some sp_inst -> sp_inst
  in
  let sp_ctnt = sp_inst.sp_partapp_ctnt in
  let dynamic_flags = List.map (fun sd -> sd = SorD_D) sd_list in
  Some (mkApp (mkConst sp_ctnt, CArray.filter_with dynamic_flags args))

let new_env_with_rels env =
  let n = Environ.nb_rel env in
  let r = ref (Global.env ()) in
  for i = n downto 1 do
    r := Environ.push_rel (Environ.lookup_rel i env) (!r)
  done;
  !r

(* This function assumes A-normal form.  So this function doesn't traverse subterms of Proj, Cast and App. *)
let rec specialize (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  Feedback.msg_info (Pp.str "specialize arg: " ++ Printer.pr_econstr_env env sigma term);
  let result = specialize1 env sigma term in
  Feedback.msg_info (Pp.str "specialize ret: " ++ Printer.pr_econstr_env env sigma result);
  check_convertible "specialize" (new_env_with_rels env) sigma term result;
  result
and specialize1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _
  | Const _ | Ind _ | Int _ | Construct _
  | Proj _ | Cast _ -> term
  | Lambda (x, ty, e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (x, ty, specialize env2 sigma e)
  | Fix ((ia, i), ((nameary, tyary, funary) as prec)) ->
      let env2 = push_rec_types prec env in
      mkFix ((ia, i), (nameary, tyary, Array.map (specialize env2 sigma) funary))
  | CoFix (i, ((nameary, tyary, funary) as prec)) ->
      let env2 = push_rec_types prec env in
      mkCoFix (i, (nameary, tyary, Array.map (specialize env2 sigma) funary))
  | LetIn (x, e, ty, b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLetIn (x, specialize env sigma e, ty, specialize env2 sigma b)
  | Case (ci, p, item, branches) ->
      mkCase (ci, p, specialize env sigma item, Array.map (specialize env sigma) branches)
  | App (f, args) ->
      match EConstr.kind sigma f with
      | Const (ctnt, u) ->
          (match specialize_ctnt_app env sigma ctnt args with None -> term | Some e -> e)
      | _ -> term

let rec count_false_in_prefix n refs =
  if n <= 0 then
    0
  else
    match refs with
    | [] -> 0
    | r :: rest ->
        if !r then
          count_false_in_prefix (n-1) rest
        else
          1 + count_false_in_prefix (n-1) rest

let rec normalize_types (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Sort _ | Ind _ | Int _
  | Const _ | Construct _ -> term
  | Evar (ev, es) ->
      mkEvar (ev, Array.map (normalize_types env sigma) es)
  | Proj (proj, e) ->
      mkProj (proj, normalize_types env sigma e)
  | Cast (e,ck,t) ->
      let e' = normalize_types env sigma e in
      let t' = Reductionops.nf_all env sigma t in
      mkCast(e', ck, t')
  | App (f, args) ->
      let f' = normalize_types env sigma f in
      let args' = Array.map (normalize_types env sigma) args in
      mkApp (f', args')
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let e' = normalize_types env sigma e in
      let t' = Reductionops.nf_all env sigma t in
      let b' = normalize_types env2 sigma b in
      mkLetIn (x, e', t', b')
  | Case (ci, p, item, branches) ->
      let p' = Reductionops.nf_all env sigma p in
      let item' = normalize_types env sigma item in
      let branches' = Array.map (normalize_types env sigma) branches in
      mkCase (ci, p', item', branches')
  | Prod (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let t' = Reductionops.nf_all env sigma t in
      let b' = normalize_types env2 sigma b in
      mkProd (x, t', b')
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let t' = Reductionops.nf_all env sigma t in
      let e' = normalize_types env2 sigma e in
      mkLambda (x, t', e')
  | Fix ((ia, i), ((nameary, tyary, funary) as prec)) ->
      let env2 = push_rec_types prec env in
      let tyary' = Array.map (Reductionops.nf_all env sigma) tyary in
      let funary' = Array.map (normalize_types env2 sigma) funary in
      mkFix ((ia, i), (nameary, tyary', funary'))
  | CoFix (i, ((nameary, tyary, funary) as prec)) ->
      let env2 = push_rec_types prec env in
      let tyary' = Array.map (Reductionops.nf_all env sigma) tyary in
      let funary' = Array.map (normalize_types env2 sigma) funary in
      mkCoFix (i, (nameary, tyary', funary'))

(* xxx: consider linear type *)
let rec delete_unused_let_rec (env : Environ.env) (sigma : Evd.evar_map) (refs : bool ref list) (term : EConstr.t) : unit -> EConstr.t =
  Feedback.msg_info (Pp.str "delete_unused_let_rec arg: " ++ Printer.pr_econstr_env env sigma term);
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _ | Int _
  | Const _ | Construct _ -> fun () -> term
  | Rel i ->
      (List.nth refs (i-1)) := true;
      fun () -> mkRel (i - count_false_in_prefix (i-1) refs)
  | Evar (ev, es) ->
      let fs = Array.map (delete_unused_let_rec env sigma refs) es in
      fun () -> mkEvar (ev, Array.map (fun f -> f ()) fs)
  | Proj (proj, e) ->
      let f = delete_unused_let_rec env sigma refs e in
      fun () -> mkProj (proj, f ())
  | Cast (e,ck,t) ->
      let fe = delete_unused_let_rec env sigma refs e in
      let ft = delete_unused_let_rec env sigma refs t in
      fun () -> mkCast(fe (), ck, ft ())
  | App (f, args) ->
      let ff = delete_unused_let_rec env sigma refs f in
      let fargs = Array.map (delete_unused_let_rec env sigma refs) args in
      fun () -> mkApp (ff (), Array.map (fun g -> g ()) fargs)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let r = ref false in
      let refs2 = r :: refs in
      let fb = delete_unused_let_rec env2 sigma refs2 b in
      if !r then
        let fe = delete_unused_let_rec env sigma refs e in
        let ft = delete_unused_let_rec env sigma refs t in
        fun () -> mkLetIn (x, fe (), ft (), fb ())
      else
        fb
  | Case (ci, p, item, branches) ->
      let fp = delete_unused_let_rec env sigma refs p in
      let fitem = delete_unused_let_rec env sigma refs item in
      let fbranches = Array.map (delete_unused_let_rec env sigma refs) branches in
      fun () -> mkCase (ci, fp (), fitem (), Array.map (fun g -> g ()) fbranches)
  | Prod (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let refs2 = (ref true) :: refs in
      let ft = delete_unused_let_rec env sigma refs t in
      let fb = delete_unused_let_rec env2 sigma refs2 b in
      fun () -> mkProd (x, ft (), fb ())
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let refs2 = (ref true) :: refs in
      let ft = delete_unused_let_rec env sigma refs t in
      let fe = delete_unused_let_rec env2 sigma refs2 e in
      fun () -> mkLambda (x, ft (), fe ())
  | Fix ((ia, i), ((nameary, tyary, funary) as prec)) ->
      let env2 = push_rec_types prec env in
      let rs = List.init (Array.length funary) (fun _ -> ref true) in
      let refs2 = List.append rs refs in
      let ftyary = Array.map (delete_unused_let_rec env sigma refs) tyary in
      let ffunary = Array.map (delete_unused_let_rec env2 sigma refs2) funary in
      fun () -> mkFix ((ia, i), (nameary, Array.map (fun g -> g ()) ftyary, Array.map (fun g -> g ()) ffunary))
  | CoFix (i, ((nameary, tyary, funary) as prec)) ->
      let env2 = push_rec_types prec env in
      let rs = List.init (Array.length funary) (fun _ -> ref true) in
      let refs2 = List.append rs refs in
      let ftyary = Array.map (delete_unused_let_rec env sigma refs) tyary in
      let ffunary = Array.map (delete_unused_let_rec env2 sigma refs2) funary in
      fun () -> mkCoFix (i, (nameary, Array.map (fun g -> g ()) ftyary, Array.map (fun g -> g ()) ffunary))

let delete_unused_let (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  Feedback.msg_info (Pp.str "delete_unused_let arg: " ++ Printer.pr_econstr_env env sigma term);
  let f = delete_unused_let_rec env sigma [] term in
  let result = f () in
  Feedback.msg_info (Pp.str "delete_unused_let ret: " ++ Printer.pr_econstr_env env sigma result);
  check_convertible "specialize" env sigma term result;
  result

let gensym_specialized_num = Summary.ref 0 ~name:"CodegenSpecializedNum"
let gensym_specialized suffix =
  let n = !gensym_specialized_num in
  gensym_specialized_num := n + 1;
  let s = "codegen_s" ^ string_of_int n in
  let s = if suffix = "" then
            s
          else
            s ^ "_" ^ suffix
  in
  Id.of_string s

let codegen_specialization_specialize
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr list) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, args) = interp_args env sigma user_args in
  let ctnt = ctnt_of_qualid env func in
  let sp_cfg = match Cmap.find_opt ctnt !specialize_config_map with
    | None -> user_err (Pp.str "specialization arguments not configured")
    | Some sp_cfg -> sp_cfg
  in
  let (sigma, partapp) = build_partapp env sigma ctnt sp_cfg.sp_sd_list args in
  let sp_inst = match ConstrMap.find_opt partapp sp_cfg.sp_instance_map with
    | None -> user_err (Pp.str "specialization instance not configured")
    | Some sp_inst -> sp_inst
  in
  let name = (match sp_inst.sp_specialization_name with
    | SpNoName -> gensym_specialized (Label.to_string (Constant.label ctnt))
    | SpExpectedId id -> id
    | SpDefinedCtnt _ -> user_err (Pp.str "specialization already defined"))
  in
  let epartapp = EConstr.of_constr partapp in
  let pred_func = Cpred.singleton ctnt in
  let global_pred = !specialize_global_inline in
  let local_pred = (match Cmap.find_opt ctnt !specialize_local_inline with
                   | None -> Cpred.empty
                   | Some pred -> pred) in
  let pred = Cpred.union (Cpred.union pred_func global_pred) local_pred in
  let term1 = inline env sigma pred epartapp in
  (*Feedback.msg_info (Printer.pr_econstr_env env sigma term1);*)
  let term2 = strict_safe_beta env sigma term1 in
  (*Feedback.msg_info (Printer.pr_econstr_env env sigma term2);*)
  let term3 = normalizeA env sigma term2 in
  (*Feedback.msg_info (Printer.pr_econstr_env env sigma term3);*)
  let term4 = specialize env sigma term3 in
  (*Feedback.msg_info (Printer.pr_econstr_env env sigma term4);*)
  let term5 = normalize_types env sigma term4 in
  (*Feedback.msg_info (Printer.pr_econstr_env env sigma term5);*)
  let term6 = delete_unused_let env sigma term5 in
  (*Feedback.msg_info (Printer.pr_econstr_env env sigma term6);*)
  let univs = Evd.univ_entry ~poly:false sigma in
  let defent = Entries.DefinitionEntry (Declare.definition_entry ~univs:univs (EConstr.to_constr sigma term6)) in
  let kind = Decl_kinds.IsDefinition Decl_kinds.Definition in
  let declared_ctnt = Declare.declare_constant name (defent, kind) in
  let sp_inst2 = {
    sp_static_arguments = sp_inst.sp_static_arguments;
    sp_partapp_ctnt = sp_inst.sp_partapp_ctnt;
    sp_specialization_name = SpDefinedCtnt declared_ctnt;
    sp_cfunc_name = sp_inst.sp_cfunc_name }
  in
  let inst_map = ConstrMap.add partapp sp_inst2 sp_cfg.sp_instance_map in
  specialize_config_map := !specialize_config_map |>
    Cmap.add ctnt { sp_cfg with sp_instance_map = inst_map };
  Feedback.msg_info (Pp.str "specialized defined:" ++ spc () ++ Printer.pr_constant env ctnt)

  (*
  let name =
    match names.spi_partapp_id with
    | Some id -> id
    | None -> gensym_partapp ()
  in
  let univs = Evd.univ_entry ~poly:false sigma in
  let defent = Entries.DefinitionEntry (Declare.definition_entry ~univs:univs partapp) in
  let kind = Decl_kinds.IsDefinition Decl_kinds.Definition in
  let ctnt = Declare.declare_constant name (defent, kind) in
  let sp_inst = {
    sp_static_arguments = args;
    sp_partapp_ctnt = ctnt;
    sp_specialized_id = None;
    sp_specialized_ctnt = None }
  in
  specialize_config_map := !specialize_config_map |>
    Cmap.add ctnt { sp_cfg with
      sp_instance_map = ConstrMap.add partapp sp_inst sp_cfg.sp_instance_map
    };
  Feedback.msg_info (Pp.str "partapp defined:" ++ spc () ++ Printer.pr_constant env ctnt)
  *)
