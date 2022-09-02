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
open GlobRef

(* open Term *)
open Constr
open EConstr

open CErrors

open Cgenutil
open State

let pr_s_or_d (sd : s_or_d) : Pp.t =
  match sd with
  | SorD_S -> Pp.str "s"
  | SorD_D -> Pp.str "d"

let drop_trailing_d (sd_list : s_or_d list) : s_or_d list =
  List.fold_right (fun sd l -> match (sd,l) with (SorD_D,[]) -> [] | _ -> sd :: l) sd_list []

let is_function_icommand (icommand : instance_command) : bool =
  match icommand with
  | CodeGenFunc -> true
  | CodeGenStaticFunc -> true
  | CodeGenPrimitive -> false
  | CodeGenConstant -> false

let string_of_icommand (icommand : instance_command) : string =
  match icommand with
  | CodeGenFunc -> "Func"
  | CodeGenStaticFunc -> "StaticFunc"
  | CodeGenPrimitive -> "Primitive"
  | CodeGenConstant -> "Constant"

let pr_constant_or_constructor (env : Environ.env) (func : Constr.t) : Pp.t =
  match Constr.kind func with
  | Const (ctnt, _) -> Printer.pr_constant env ctnt
  | Construct (cstr, _) -> Printer.pr_constructor env cstr
  | _ -> user_err (Pp.str "[codegen] expect constant or constructor")

let pr_codegen_arguments (env : Environ.env) (sigma : Evd.evar_map) (sp_cfg : specialization_config) : Pp.t =
  Pp.str "CodeGen StaticArgs" +++
  pr_constant_or_constructor env sp_cfg.sp_func +++
  pp_sjoinmap_list pr_s_or_d sp_cfg.sp_sd_list ++
  Pp.str "."

let pr_codegen_instance (env : Environ.env) (sigma : Evd.evar_map) (sp_cfg : specialization_config) (sp_inst : specialization_instance) : Pp.t =
  let icommand = sp_inst.sp_icommand in
  let func = sp_cfg.sp_func in
  let static_args = sp_inst.sp_static_arguments in
  let cfunc_name = sp_inst.sp_cfunc_name in
  Pp.str "CodeGen" +++
  Pp.str (string_of_icommand icommand) +++
  pr_constant_or_constructor env sp_cfg.sp_func +++
  (pp_sjoin_list (snd (List.fold_right
         (fun sd (args, res) ->
           match sd with
           | SorD_S ->
               (List.tl args, (Printer.pr_constr_env env sigma (List.hd args) :: res))
           | SorD_D ->
               (args, (Pp.str "_" :: res)))
         sp_cfg.sp_sd_list (static_args, [])))) +++
  Pp.str "=>" +++
  Pp.str (escape_as_coq_string cfunc_name) +++
  (if sp_inst.sp_presimp_constr = func then
    Pp.str "_"
  else
    Printer.pr_constr_env env sigma sp_inst.sp_presimp_constr) +++
  (match sp_inst.sp_simplified_status with
  | SpNoSimplification -> Pp.mt ()
  | SpExpectedId s_id -> Id.print s_id
  | SpDefined (ctnt, refered_cfuncs) -> Printer.pr_constant env ctnt) ++
  Pp.str "." +++
  (match sp_inst.sp_simplified_status with
  | SpNoSimplification -> Pp.str "(*no-simplification*)"
  | SpExpectedId s_id -> Pp.str "(*before-simplification*)"
  | SpDefined (ctnt, refered_cfuncs) -> Pp.str "(*after-simplification*)")

let command_print_specialization (funcs : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pr_cfg sp_cfg =
    msg_info_hov (pr_codegen_arguments env sigma sp_cfg);
    let feedback_instance sp_inst =
      msg_info_hov (pr_codegen_instance env sigma sp_cfg sp_inst);
      match sp_inst.sp_simplified_status with
      | SpNoSimplification -> ()
      | SpExpectedId id -> ()
      | SpDefined (ctnt, referred_cfuncs) ->
          msg_info_hov (Pp.str "Dependency" +++
            Pp.str sp_inst.sp_cfunc_name +++
            Pp.str "=>" +++
            pp_sjoinmap_list Pp.str (StringSet.elements referred_cfuncs) ++
            Pp.str ".")
    in
    ConstrMap.iter (fun _ -> feedback_instance) sp_cfg.sp_instance_map
  in
  let l = if funcs = [] then
            ConstrMap.bindings !specialize_config_map |>
            (List.sort @@ fun (x,_) (y,_) -> Constr.compare x y) |>
            List.map snd
          else
            funcs |> List.map @@ fun func ->
              let gref = Smartlocate.global_with_alias func in
              let func = match gref with
                | ConstRef ctnt -> Constr.mkConst ctnt
                | ConstructRef cstr -> Constr.mkConstruct cstr
                | _ -> user_err (Pp.str "[codegen] constant or constructor expected:" +++
                                 Printer.pr_global gref)
              in
              match ConstrMap.find_opt func !specialize_config_map with
              | None -> user_err (Pp.str "[codegen] not specialized:" +++ Printer.pr_global gref)
              | Some sp_cfg -> sp_cfg
  in
  msg_info_hov (Pp.str "Number of source functions:" +++ Pp.int (ConstrMap.cardinal !specialize_config_map));
  List.iter pr_cfg l

let func_of_qualid (env : Environ.env) (qualid : Libnames.qualid) : Constr.t =
  let gref = Smartlocate.global_with_alias qualid in
  match gref with
    | ConstRef ctnt -> Constr.mkConst ctnt
    | ConstructRef cstr -> Constr.mkConstruct cstr
    | _ -> user_err (Pp.str "[codegen] constant or constructor expected:" +++ Printer.pr_global gref)

let codegen_define_static_arguments ?(cfunc : string option) (env : Environ.env) (sigma : Evd.evar_map) (func : Constr.t) (sd_list : s_or_d list) : specialization_config =
  let func_is_cstr =
    match Constr.kind func with
    | Const _ -> false
    | Construct _ -> true
    | _ -> user_err (Pp.str "[codegen] codegen_define_static_arguments needs constant or constructor for func:" +++
                     Printer.pr_constr_env env sigma func)
  in
  let sp_cfg = {
    sp_func=func;
    sp_is_cstr=func_is_cstr;
    sp_sd_list=sd_list;
    sp_instance_map = ConstrMap.empty
  } in
  specialize_config_map := ConstrMap.add func sp_cfg !specialize_config_map;
  msg_info_hov (Pp.hov 2 (Pp.str "[codegen]" +++
    (match cfunc with Some f -> Pp.str "[cfunc:" ++ Pp.str f ++ Pp.str "]" | None -> Pp.mt ()) +++
    pr_codegen_arguments env sigma sp_cfg));
  sp_cfg

let codegen_define_or_check_static_arguments ?(cfunc : string option) (env : Environ.env) (sigma : Evd.evar_map) (func : Constr.t) (sd_list : s_or_d list) : specialization_config =
  match ConstrMap.find_opt func !specialize_config_map with
  | None ->
      codegen_define_static_arguments ?cfunc env sigma func sd_list
  | Some sp_cfg ->
      let sd_list_old = drop_trailing_d sp_cfg.sp_sd_list in
      let sd_list_new = drop_trailing_d sd_list in
      (if sd_list_old <> sd_list_new then
        user_err (Pp.str "[codegen] inconsistent specialization configuration for" +++
        Printer.pr_constr_env env sigma func ++ Pp.str ":" +++
        Pp.str "[" ++ pp_sjoinmap_list pr_s_or_d sd_list_old ++ Pp.str "]" +++
        Pp.str "expected but" +++
        Pp.str "[" ++ pp_sjoinmap_list pr_s_or_d sd_list_new ++ Pp.str "]"));
      sp_cfg

let command_arguments (func : Libnames.qualid) (sd_list : s_or_d list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let func = func_of_qualid env func in
  (if ConstrMap.mem func !specialize_config_map then
    user_err (Pp.str "[codegen] specialization already configured:" +++ Printer.pr_constr_env env sigma func));
  ignore (codegen_define_static_arguments env sigma func sd_list)

let rec determine_type_arguments (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : bool list =
  (* msg_info_hov (Printer.pr_econstr_env env sigma ty); *)
  let ty = Reductionops.whd_all env sigma ty in
  match EConstr.kind sigma ty with
  | Prod (x,t,b) ->
      let t = Reductionops.whd_all env sigma t in
      let is_type_arg = EConstr.isSort sigma t in
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env = EConstr.push_rel decl env in
      is_type_arg :: determine_type_arguments env sigma b
  | _ -> []

let is_monomorphic_type_for_determine_static_arguments (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : bool =
  let rec aux env ty =
    match EConstr.kind sigma ty with
    | Prod (x,t,b) ->
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        is_monomorphic_type env sigma t &&
        is_monomorphic_type env2 sigma b
    | Ind _ -> true
    | App (f,args) when isInd sigma f -> Array.for_all (aux env) args
    | Rel _ -> true
        (* type variable.
          Since type variables are defined as static in determine_static_arguments,
          the variable will be instantiated with a monomorphic type. *)
    | _ -> false
  in
  aux env ty

let rec determine_static_arguments (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : bool list =
  (* msg_info_hov (Printer.pr_econstr_env env sigma ty); *)
  let ty = Reductionops.whd_all env sigma ty in
  match EConstr.kind sigma ty with
  | Prod (x,t,b) ->
      msg_debug_hov (Pp.str "[codegen:determine_static_arguments] t=" ++ Printer.pr_econstr_env env sigma t);
      let t = Reductionops.nf_all env sigma t in
      msg_debug_hov (Pp.str "[codegen:determine_static_arguments] normalized_t=" ++ Printer.pr_econstr_env env sigma t);
      let is_static_arg = not (is_monomorphic_type_for_determine_static_arguments env sigma t) in
      msg_debug_hov (Pp.str "[codegen:determine_static_arguments] is_static_arg=" ++ Pp.bool is_static_arg);
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env = EConstr.push_rel decl env in
      is_static_arg :: determine_static_arguments env sigma b
  | _ -> []

let determine_sd_list (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : s_or_d list =
  List.map
    (function true -> SorD_S | false -> SorD_D)
    (determine_static_arguments env sigma ty)

let codegen_auto_arguments_internal
    ?(cfunc : string option)
    (env : Environ.env) (sigma : Evd.evar_map)
    (func : Constr.t) : specialization_config =
  match ConstrMap.find_opt func !specialize_config_map with
  | Some sp_cfg -> sp_cfg (* already defined *)
  | None ->
      let ty = Retyping.get_type_of env sigma (EConstr.of_constr func) in
      let sd_list = (determine_sd_list env sigma ty) in
      codegen_define_static_arguments ?cfunc env sigma func sd_list

let codegen_auto_sd_list
    (env : Environ.env) (sigma : Evd.evar_map)
    (func : Constr.t) : s_or_d list =
  match ConstrMap.find_opt func !specialize_config_map with
  | Some sp_cfg -> sp_cfg.sp_sd_list (* already defined *)
  | None ->
      let ty = Retyping.get_type_of env sigma (EConstr.of_constr func) in
      determine_sd_list env sigma ty

let codegen_auto_arguments_1 (env : Environ.env) (sigma : Evd.evar_map)
    (func : Libnames.qualid) : unit =
  let func = func_of_qualid env func in
  ignore (codegen_auto_arguments_internal env sigma func)

let command_auto_arguments (func_list : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  List.iter (codegen_auto_arguments_1 env sigma) func_list

let build_presimp (env : Environ.env) (sigma : Evd.evar_map)
    (f : EConstr.t) (f_type : EConstr.types) (sd_list : s_or_d list)
    (static_args : Constr.t list) : (Evd.evar_map * Constr.t * EConstr.types) =
  let rec aux env f f_type sd_list static_args =
    match sd_list with
    | [] ->
        if static_args = [] then
          f
        else
          user_err (Pp.str "[codegen] too many static arguments")
    | sd :: sd_list' ->
        let f_type = Reductionops.whd_all env sigma f_type in
        (match EConstr.kind sigma f_type with
        | Prod (x,t,c) ->
            (match sd with
            | SorD_S ->
                (match static_args with
                | [] -> user_err (Pp.str "[codegen] needs more argument")
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
        | _ -> user_err (Pp.str "[codegen] needs a function type"))
  in
  let sigma0 = sigma in
  let sd_list = drop_trailing_d sd_list in
  let t = aux env f f_type sd_list (List.map EConstr.of_constr static_args) in
  let (sigma, ty) = Typing.type_of env sigma t in
  Pretyping.check_evars env ~initial:sigma0 sigma t;
  let t = Evarutil.flush_and_check_evars sigma t in
  let ty = Reductionops.nf_all env sigma ty in
  (if not (is_monomorphic_type env sigma ty) then
    user_err (Pp.hov 2 (Pp.str "[codegen] pre-simplified term must have monomorphic type:" +++ Printer.pr_econstr_env env sigma ty)));
  (sigma, t, ty)

let gensym_simplification (suffix : string) : Names.Id.t * Names.Id.t =
  let n = !gensym_ps_num in
  gensym_ps_num := n + 1;
  let suffix2 = if suffix = "" then suffix else "_" ^ suffix in
  let p = "codegen_p" ^ string_of_int n ^ suffix2 in (* pre-simplified *)
  let s = "codegen_s" ^ string_of_int n ^ suffix2 in (* simplified *)
  (Id.of_string p, Id.of_string s)

let interp_args (env : Environ.env) (sigma : Evd.evar_map)
    (istypearg_list : bool list)
    (user_args : Constrexpr.constr_expr list) : Evd.evar_map * EConstr.t list =
  let interp_arg sigma istypearg user_arg =
    let sigma0 = sigma in
    let interp = if istypearg then Constrintern.interp_type_evars
                              else Constrintern.interp_constr_evars in
    let (sigma, arg) = interp env sigma user_arg in
    (* msg_info_hov (Printer.pr_econstr_env env sigma arg); *)
    Pretyping.check_evars env ~initial:sigma0 sigma arg;
    (sigma, arg)
  in
  CList.fold_left2_map interp_arg sigma istypearg_list user_args

let label_name_of_constant_or_constructor (func : Constr.t) : string =
  match Constr.kind func with
  | Const (ctnt, _) -> Label.to_string (Constant.label ctnt)
  | Construct (((mutind, i), j), _) ->
      let j0 = j - 1 in
      let env = Global.env () in
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.Declarations.mind_packets.(i) in
      let cons_id = oind_body.Declarations.mind_consnames.(j0) in
      Id.to_string cons_id
  | _ -> user_err (Pp.str "[codegen] expect constant or constructor")

let codegen_define_instance
    ?(cfunc : string option)
    (env : Environ.env) (sigma : Evd.evar_map)
    (icommand : instance_command)
    (func : Constr.t) (static_args : Constr.t list)
    (names_opt : sp_instance_names option) : Environ.env * specialization_instance =
  let sp_cfg = match ConstrMap.find_opt func !specialize_config_map with
    | None -> user_err (Pp.str "[codegen] specialization arguments not configured")
    | Some sp_cfg -> sp_cfg
  in
  (if (is_function_icommand icommand) && sp_cfg.sp_is_cstr then
    user_err (Pp.str "[codegen]" +++ Pp.str (string_of_icommand icommand) +++
              Pp.str "is used for a constructor:" +++
              Printer.pr_constr_env env sigma func));
  (if (not (is_function_icommand icommand)) &&
       match names_opt with Some { spi_simplified_id = Some _ } -> true
                          | _ -> false then
    user_err (Pp.str "[codegen] simplified id is specified for" +++ Pp.str (string_of_icommand icommand) +++ Pp.str ":" +++
              Printer.pr_constr_env env sigma func));
  let efunc = EConstr.of_constr func in
  let efunc_type = Retyping.get_type_of env sigma efunc in
  let (sigma, presimp, presimp_type) = build_presimp env sigma efunc efunc_type sp_cfg.sp_sd_list static_args in
  (if (icommand = CodeGenConstant) &&
      not (isInd sigma (fst (decompose_appvect sigma presimp_type))) then
    user_err (Pp.str "[codegen] CodeGen Constant needs a constant:" +++
      Printer.pr_constr_env env sigma presimp +++ Pp.str ":" +++
      Printer.pr_econstr_env env sigma presimp_type));
  (if ConstrMap.mem presimp sp_cfg.sp_instance_map then
    user_err (Pp.str "[codegen] specialization instance already configured:" +++ Printer.pr_constr_env env sigma presimp));
  let sp_inst =
    let func_name = label_name_of_constant_or_constructor func in
    let check_cfunc_name_conflict cfunc_name =
      match is_function_icommand icommand, CString.Map.find_opt cfunc_name !cfunc_instance_map with
      | true, None -> ()
      | true, Some (CodeGenCfuncGenerate (sp_cfg, sp_inst)) ->
          user_err
            (Pp.str "[codegen] C function name already used:" +++
            Pp.str cfunc_name +++
            Pp.str "for" +++
            Printer.pr_constr_env env sigma sp_inst.sp_presimp +++
            Pp.str "but also for" +++
            Printer.pr_constr_env env sigma presimp)
      | true, Some (CodeGenCfuncPrimitive _) ->
          user_err
            (Pp.str "[codegen] C function name already used:" +++
            Pp.str cfunc_name +++
            Pp.str "for primitives" +++
            Pp.str "but also for" +++
            Printer.pr_constr_env env sigma presimp)
      | false, None -> ()
      | false, Some (CodeGenCfuncGenerate (sp_cfg, sp_inst)) ->
          user_err
            (Pp.str "[codegen] C function name already used:" +++
            Pp.str cfunc_name +++
            Pp.str "for" +++
            Printer.pr_constr_env env sigma sp_inst.sp_presimp +++
            Pp.str "but also for a primitive")
      | false, Some (CodeGenCfuncPrimitive _) -> ()
    in
    let generated_simplification_syms = ref None in
    let lazy_gensym_simplification () =
      match !generated_simplification_syms with
      | Some ids -> ids
      | None ->
          let ids = gensym_simplification func_name in
          generated_simplification_syms := Some ids;
          ids
    in
    let lazy_gensym_p () = let (id, _) = lazy_gensym_simplification () in id in
    let lazy_gensym_s () = let (_, id) = lazy_gensym_simplification () in id in
    let has_static_arguments = List.exists (fun sd -> sd = SorD_S) sp_cfg.sp_sd_list in
    let presimp_id_specified = match names_opt with Some { spi_presimp_id = Some _ } -> true | _ -> false in
    let need_presimplified_ctnt = has_static_arguments || presimp_id_specified
    in
    let s_id () = match names_opt with
      | Some { spi_simplified_id = Some s_id } -> s_id
      | _ -> lazy_gensym_s ()
    in
    let p_id () = match names_opt with
      | Some { spi_presimp_id = Some p_id } -> p_id
      | _ -> lazy_gensym_p ()
    in
    let cfunc_name = match names_opt with
      | Some { spi_cfunc_name = Some name } ->
          (* We accept C's non-idetifier, such as "0" here. *)
          name
      | _ ->
          if not has_static_arguments then
            (* We use Gallina function name as-is for functions without static arguments *)
            if valid_c_id_p func_name then
              func_name
            else
              user_err (Pp.str "[codegen] Gallina function name is invalid in C:" +++ Pp.str func_name)
          else
            (* We use presimp name for functions with static arguments *)
            c_id (Id.to_string (p_id ()))
    in
    check_cfunc_name_conflict cfunc_name;
    let presimp_constr =
      if not need_presimplified_ctnt then
        func (* use the original function for fully dynamic function *)
      else
        let globref = Declare.declare_definition
          ~info:(Declare.Info.make ())
          ~cinfo:(Declare.CInfo.make ~name:(p_id ()) ~typ:(Some presimp_type) ())
          ~opaque:false
          ~body:(EConstr.of_constr presimp)
          sigma
        in
        let declared_ctnt = Globnames.destConstRef globref in
        Constr.mkConst declared_ctnt
    in
    let simplified_status =
      if is_function_icommand icommand then
        SpExpectedId (s_id ())
      else (* CodeGenPrimitive or CodeGenConstant *)
        SpNoSimplification
    in
    let sp_inst = {
      sp_presimp = presimp;
      sp_static_arguments = static_args;
      sp_presimp_constr = presimp_constr;
      sp_simplified_status = simplified_status;
      sp_cfunc_name = cfunc_name;
      sp_icommand = icommand; }
    in
    sp_inst
  in
  let cfunc_name = sp_inst.sp_cfunc_name in
  msg_info_hov (Pp.str "[codegen]" +++
    (match cfunc with Some f -> Pp.str "[cfunc:" ++ Pp.str f ++ Pp.str "]" | None -> Pp.mt ()) +++
    pr_codegen_instance env sigma sp_cfg sp_inst);
  gallina_instance_map := (ConstrMap.add sp_inst.sp_presimp_constr (sp_cfg, sp_inst) !gallina_instance_map);
  gallina_instance_map := (ConstrMap.add presimp (sp_cfg, sp_inst) !gallina_instance_map);
  (if is_function_icommand icommand then
    cfunc_instance_map := (CString.Map.add cfunc_name (CodeGenCfuncGenerate (sp_cfg, sp_inst)) !cfunc_instance_map)
  else
    match CString.Map.find_opt cfunc_name !cfunc_instance_map with
    | None -> cfunc_instance_map := (CString.Map.add cfunc_name (CodeGenCfuncPrimitive [(sp_cfg, sp_inst)]) !cfunc_instance_map);
    | Some (CodeGenCfuncPrimitive l) -> cfunc_instance_map := (CString.Map.add cfunc_name (CodeGenCfuncPrimitive ((sp_cfg, sp_inst)::l)) !cfunc_instance_map)
    | Some (CodeGenCfuncGenerate l) -> assert false);
  let inst_map = ConstrMap.add presimp sp_inst sp_cfg.sp_instance_map in
  let sp_cfg2 = { sp_cfg with sp_instance_map = inst_map } in
  specialize_config_map := ConstrMap.add func sp_cfg2 !specialize_config_map;
  (new_env_with_rels env, sp_inst)

let codegen_instance_command
    (icommand : instance_command)
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr option list)
    (names : sp_instance_names) : Environ.env * specialization_instance =
  let sd_list = List.map
    (fun arg -> match arg with None -> SorD_D | Some _ -> SorD_S)
    user_args
  in
  let static_args = List.filter_map
    (fun arg -> match arg with None -> None| Some a -> Some a)
    user_args
  in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let func = func_of_qualid env func in
  let func_type = Retyping.get_type_of env sigma (EConstr.of_constr func) in
  let func_istypearg_list = determine_type_arguments env sigma func_type in
  (if List.length func_istypearg_list < List.length sd_list then
    user_err (Pp.str "[codegen] too many arguments:" +++
      Printer.pr_constr_env env sigma func +++
      Pp.str "(" ++
      Pp.int (List.length sd_list) ++ Pp.str " for " ++
      Pp.int (List.length func_istypearg_list) ++ Pp.str ")"));
  let func_istypearg_list = CList.map_filter_i
    (fun i arg -> match arg with None -> None | Some _ -> Some (List.nth func_istypearg_list i))
    user_args
  in
  let (sigma, args) = interp_args env sigma func_istypearg_list static_args in
  let args = List.map (Reductionops.nf_all env sigma) args in
  let args = List.map (Evarutil.flush_and_check_evars sigma) args in
  ignore (codegen_define_or_check_static_arguments env sigma func sd_list);
  codegen_define_instance env sigma icommand func args (Some names)

let command_function
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr option list)
    (names : sp_instance_names) : unit =
  let (env, sp_inst) = codegen_instance_command CodeGenFunc func user_args names in
  codegen_add_header_generation (GenPrototype sp_inst.sp_cfunc_name);
  codegen_add_source_generation (GenFunc sp_inst.sp_cfunc_name)

let command_static_function
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr option list)
    (names : sp_instance_names) : unit =
  let (env, sp_inst) = codegen_instance_command CodeGenStaticFunc func user_args names in
  codegen_add_source_generation (GenFunc sp_inst.sp_cfunc_name)

let command_primitive
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr option list)
    (names : sp_instance_names) : unit =
  ignore (codegen_instance_command CodeGenPrimitive func user_args names)

let command_constant
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr list)
    (names : sp_instance_names) : unit =
  let user_args = List.map (fun arg -> Some arg) user_args in
  ignore (codegen_instance_command CodeGenConstant func user_args names)

let command_global_inline (func_qualids : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let funcs = List.map (func_of_qualid env) func_qualids in
  let ctnts = List.map
    (fun func ->
      match Constr.kind func with
      | Const (ctnt, _) -> ctnt
      | _ -> user_err_hov (Pp.str "[codegen] constant expected:" +++ Printer.pr_constr_env env sigma func))
    funcs
  in
  let f pred ctnt = Cpred.add ctnt pred in
  specialize_global_inline := List.fold_left f !specialize_global_inline ctnts

let command_local_inline (func_qualid : Libnames.qualid) (func_qualids : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let func = func_of_qualid env func_qualid in
  let ctnt =
    match Constr.kind func with
    | Const (ctnt, _) -> ctnt
    | _ -> user_err_hov (Pp.str "[codegen] constant expected:" +++ Printer.pr_constr_env env sigma func)
  in
  let funcs = List.map (func_of_qualid env) func_qualids in
  let ctnts = List.map
    (fun func ->
      match Constr.kind func with
      | Const (ctnt, _) -> ctnt
      | _ -> user_err_hov (Pp.str "[codegen] constant expected:" +++ Printer.pr_constr_env env sigma func))
    funcs
  in
  let local_inline = !specialize_local_inline in
  let pred = match Cmap.find_opt ctnt local_inline with
             | None -> Cpred.empty
             | Some pred -> pred in
  let f pred ctnt = Cpred.add ctnt pred in
  let pred' = List.fold_left f pred ctnts in
  specialize_local_inline := Cmap.add ctnt pred' local_inline

let inline1 (env : Environ.env) (sigma : Evd.evar_map) (pred : Cpred.t) (term : EConstr.t) : EConstr.t =
  let rec aux term =
    match EConstr.kind sigma term with
    | Const (ctnt, univ) ->
        if Cpred.mem ctnt pred then
          let cbody = Environ.lookup_constant ctnt env in
          let body = match Global.body_of_constant_body Library.indirect_accessor cbody with
                     | None -> user_err (Pp.str "[codegen] couldn't obtain the body:" +++ Printer.pr_constant env ctnt)
                     | Some (body,_, _) -> body
          in
          aux (EConstr.of_constr body)
        else
          term
    | _ ->
        EConstr.map sigma aux term
  in
  aux term

let inline (env : Environ.env) (sigma : Evd.evar_map) (pred : Cpred.t) (term : EConstr.t) : EConstr.t =
  let result = inline1 env sigma pred term in
  check_convertible "inline" env sigma term result;
  result

(*
  Coq 8.14 changes the representation of match-expression.
  (dev/doc/case-repr.md in Coq source)
  It forces that binders of case-branches must be same as the type of
  constructors, including let-ins in the binders.
  However codegen transforms let-ins: V-normalization introduces let-ins,
  arguments completion moves let-ins.
  Also, our code generator assumes that case-branches must start
  with sequence of lambdas, without let-in.
  So we don't support let-ins in constructor type now.
  check_letin_in_cstr_type validates this condition.

  We may support let-ins in constructor in future.
  codegen would copy let-ins into the body of case-branches.
*)
let rec check_letin_in_cstr_type (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : unit =
  check_letin_in_cstr_type1 env sigma term
and check_letin_in_cstr_type1 (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Rel _ | Const _ | Construct _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ -> ()
  | Var _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Var:" +++ Printer.pr_econstr_env env sigma term)
  | Evar _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Evar:" +++ Printer.pr_econstr_env env sigma term)
  | Prod _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Prod:" +++ Printer.pr_econstr_env env sigma term)
  | CoFix _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected CoFix:" +++ Printer.pr_econstr_env env sigma term)
  | Array _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Array:" +++ Printer.pr_econstr_env env sigma term)
  | Cast (e,ck,t) -> check_letin_in_cstr_type env sigma e
  | Lambda (x, t, b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      check_letin_in_cstr_type env2 sigma b
  | LetIn (x, e, t, b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      check_letin_in_cstr_type env sigma e;
      check_letin_in_cstr_type env2 sigma b
  | Case (ci, u, pms, p, iv, item, brs) ->
      let (ci, _, pms, p0, _, item, brs0) =
        EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, brs) in
      Array.iter
        (fun (ctx, br) ->
          List.iteri
            (fun i -> function
            | Context.Rel.Declaration.LocalAssum _ -> ()
            | Context.Rel.Declaration.LocalDef (x,e,t) ->
                let cstr = (ci.ci_ind, i) in
                user_err_hov
                  (Pp.str "[codegen] constructor type contains let-in:" +++
                  Printer.pr_constructor env cstr +++
                  Pp.str "of" +++
                  Printer.pr_inductive env ci.ci_ind))
            ctx)
        brs0;
      check_letin_in_cstr_type env sigma item;
      Array.iter
        (fun (ctx, br) ->
          let env2 = EConstr.push_rel_context ctx env in
          check_letin_in_cstr_type env2 sigma br)
        brs0
  | Proj (proj, e) ->
      check_letin_in_cstr_type env sigma e
  | App (f, args) ->
      check_letin_in_cstr_type env sigma f;
      Array.iter (check_letin_in_cstr_type env sigma) args
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      Array.iter (check_letin_in_cstr_type env2 sigma) fary

(* useless ?
let rec strip_cast (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (* msg_info_hov (Pp.str "strip_cast arg:" +++ Printer.pr_econstr_env env sigma term); *)
  let result = strip_cast1 env sigma term in
  (* msg_info_hov (Pp.str "strip_cast ret:" +++ Printer.pr_econstr_env env sigma result); *)
  check_convertible "strip_cast" env sigma term result;
  result
and strip_cast1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Ind _
  | Const _ | Construct _ | Int _ | Prod _ -> term
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (x, t, strip_cast env2 sigma b)
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (strip_cast env2 sigma) fary in
      mkFix ((ks, j), (nary, tary, fary'))
  | CoFix (i, ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (strip_cast env2 sigma) fary in
      mkCoFix (i, (nary, tary, fary'))
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let e' = strip_cast env sigma e in
      let b' = strip_cast env2 sigma b in
      mkLetIn (x, e', t, b')
  | Case (ci, p, item, branches) ->
      let item' = strip_cast env sigma item in
      let branches' = Array.map (strip_cast env sigma) branches in
      mkCase (ci, p, item', branches')
  | App (f,args) ->
      let f = strip_cast env sigma f in
      let args = Array.map (strip_cast env sigma) args in
      mkApp (f, args)
  | Cast (e,ck,ty) -> strip_cast env sigma e
  | Proj (proj, e) ->
      let e = strip_cast env sigma e in
      mkProj (proj, e)
*)

let rec expand_eta_top (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  let result = expand_eta_top1 env sigma term in
  check_convertible "expand_eta_top" env sigma term result;
  result
and expand_eta_top1 (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Cast (e,ck,t) -> expand_eta_top env sigma e (* strip cast *)
  | Lambda (x,ty,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (x, ty, expand_eta_top env2 sigma b)
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (expand_eta_top env2 sigma) fary in
      mkFix ((ks, j), (nary, tary, fary'))
  | _ ->
      let ty = Retyping.get_type_of env sigma term in
      let ty = Reductionops.nf_all env sigma ty in
      let (args, result_type) = decompose_prod sigma ty in
      let args' = List.map
        (fun (arg_name, arg_ty) ->
          let arg_name' =
            Context.map_annot
              (Namegen.named_hd env sigma arg_ty)
              arg_name
          in
          (arg_name', arg_ty))
        args
      in
      let n = List.length args in
      let term' = Vars.lift n (search_fixclo_to_expand_eta env sigma term) in
      compose_lam args' (mkApp (term', Array.map mkRel (array_rev (iota_ary 1 n))))
and search_fixclo_to_expand_eta (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Const _ | Construct _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ -> term
  | Var _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Var:" +++ Printer.pr_econstr_env env sigma term)
  | Evar _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Evar:" +++ Printer.pr_econstr_env env sigma term)
  | Prod _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Prod:" +++ Printer.pr_econstr_env env sigma term)
  | CoFix _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected CoFix:" +++ Printer.pr_econstr_env env sigma term)
  | Array _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Array:" +++ Printer.pr_econstr_env env sigma term)
  | Cast (e,ck,t) -> search_fixclo_to_expand_eta env sigma e (* strip cast *)
  | Lambda (x, t, b) ->
      (* closure generating lambda found.  Apply eta expansion. *)
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let b' = expand_eta_top env2 sigma b in
      mkLambda (x, t, b')
  | LetIn (x, e, t, b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let e' = search_fixclo_to_expand_eta env sigma e in
      let b' = search_fixclo_to_expand_eta env2 sigma b in
      mkLetIn (x, e', t, b')
  | Case (ci, u, pms, p, iv, c, bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, c, bl) in
      let bl' =
        Array.map2
          (fun (nas, body) (ctx, _) ->
            let env2 = EConstr.push_rel_context ctx env in
            (nas, search_fixclo_to_expand_eta env2 sigma body))
          bl bl0
      in
      mkCase (ci, u, pms, p, iv, c, bl')
  | Proj (proj, e) ->
      let e' = search_fixclo_to_expand_eta env sigma e in
      mkProj (proj, e')
  | App (f, args) ->
      let f' = search_fixclo_to_expand_eta env sigma f in
      let args' = Array.map (search_fixclo_to_expand_eta env sigma) args in
      mkApp (f', args')
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      (* fixpoint found.  Apply eta expansion. *)
      let env2 = push_rec_types prec env in
      let fary' = Array.map (expand_eta_top env2 sigma) fary in
      mkFix ((ks, j), (nary, tary, fary'))

let map_under_context_with_binders (g : 'a -> 'a) (f : 'a -> EConstr.t -> EConstr.t) (l : 'a) (d : EConstr.case_return) : EConstr.case_return =
  let (nas, p) = d in
  let l = Util.iterate g (Array.length nas) l in
  let p' = f l p in
  if p' == p then d else (nas, p')

(*val map_return_predicate_with_binders : ('a -> 'a) -> ('a -> EConstr.t -> EConstr.t) -> 'a -> EConstr.case_return -> EConstr.case_return*)

let map_return_predicate_with_binders (g : 'a -> 'a) (f : 'a -> EConstr.t -> EConstr.t) (l : 'a) (p : EConstr.case_return) : EConstr.case_return =
  map_under_context_with_binders g f l p

let rec normalizeV (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  (if !opt_debug_normalizeV then
    msg_debug_hov (Pp.str "[codegen] normalizeV arg:" +++ Printer.pr_econstr_env env sigma term));
  let result = normalizeV1 env sigma term in
  (if !opt_debug_normalizeV then
    msg_debug_hov (Pp.str "[codegen] normalizeV ret:" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "normalizeV" env sigma term result;
  result
and normalizeV1 (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  let wrap_lets hoisted_exprs lifted_term =
    let hoisted_types = List.map (Retyping.get_type_of env sigma) hoisted_exprs in
    let hoisted_names = List.map (fun ty -> Context.nameR (Id.of_string (Namegen.hdchar env sigma ty))) hoisted_types in
    let rec aux i names exprs types acc_term =
      match names, exprs, types with
      | [], [], [] -> acc_term
      | x :: names', e :: exprs', ty :: types' ->
          let ty' = Vars.lift i ty in
          let e' = Vars.lift i (normalizeV env sigma e) in
          let acc_term' = aux (i+1) names' exprs' types' acc_term in
          mkLetIn (x, e', ty', acc_term')
      | _, _, _ -> user_err (Pp.str "[codegen] inconsistent list length")
    in
    aux 0 hoisted_names hoisted_exprs hoisted_types lifted_term
  in
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Ind _
  | Const _ | Construct _ | Int _ | Float _ | Array _ | Prod _ -> term
  | Lambda (x,ty,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (x, ty, normalizeV env2 sigma b)
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (normalizeV env2 sigma) fary in
      mkFix ((ks, j), (nary, tary, fary'))
  | CoFix (i, ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (normalizeV env2 sigma) fary in
      mkCoFix (i, (nary, tary, fary'))
  | LetIn (x,e,ty,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, ty) in
      let env2 = EConstr.push_rel decl env in
      let e' = normalizeV env sigma e in
      let b' = normalizeV env2 sigma b in
      mkLetIn (x, e', ty, b')
  | Case (ci, u, pms, p, iv, item, bl) ->
      if isRel sigma item then
        let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
        let bl' =
          Array.map2
            (fun (nas, body) (ctx, _) ->
              let env2 = EConstr.push_rel_context ctx env in
              (nas, normalizeV env2 sigma body))
            bl bl0
        in
        mkCase (ci, u, pms, p, iv, item, bl')
      else
        let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
        let term =
          mkCase (ci, u,
            Array.map (Vars.lift 1) pms,
            map_return_predicate_with_binders succ (Vars.liftn 1) 1 p,
            map_invert (Vars.lift 1) iv,
            mkRel 1,
            Array.map2
              (fun (nas, body) (ctx, _) ->
                let env2 = EConstr.push_rel_context ctx env in
                (nas, Vars.liftn 1 (List.length ctx + 1) (normalizeV env2 sigma body)))
              bl bl0)
        in
        wrap_lets [item] term
  | App (f,args) ->
      let f = normalizeV env sigma f in
      let hoist_args = Array.map (fun arg -> not (isRel sigma arg)) args in
      let nargs = Array.fold_left (fun n b -> n + if b then 1 else 0) 0 hoist_args in
      let hoisted_args = CList.filter_with (Array.to_list hoist_args) (Array.to_list args) in
      let app =
	let f' = Vars.lift nargs f in
        let (args', _) = array_fold_right_map
	  (fun (arg, hoist) n -> if not hoist then
                                   mkRel (destRel sigma arg + nargs), n
                                 else
                                   mkRel n, n+1)
	  (array_combine args hoist_args) 1
        in
        mkApp (f', args')
      in
      wrap_lets hoisted_args app
  | Cast (e,ck,ty) ->
      if isRel sigma e then term
      else wrap_lets [e] (mkCast (mkRel 1, ck, Vars.lift 1 ty))
  | Proj (proj, e) ->
      if isRel sigma e then term
      else wrap_lets [e] (mkProj (proj, mkRel 1))

(* The innermost let binding is appeared first in the result:
  Here, "exp" means AST of exp, not string.

    decompose_lets
      "let x : nat := 0 in
       let y : nat := 1 in
       let z : nat := 2 in
      body"

  returns

    ([("z","2","nat"); ("y","1","nat"); ("x","0","nat")], "body")

  This order of bindings is same as Constr.rel_context used by
  Environ.push_rel_context.
*)
let decompose_lets (sigma : Evd.evar_map) (term : EConstr.t) : (Name.t Context.binder_annot * EConstr.t * EConstr.types) list * EConstr.t =
  let rec aux term defs =
    match EConstr.kind sigma term with
    | LetIn (x, e, ty, b) ->
        aux b ((x, e, ty) :: defs)
    | _ -> (defs, term)
  in
  aux term []

let rec compose_lets (defs : (Name.t Context.binder_annot * EConstr.t * EConstr.types) list) (body : EConstr.t) : EConstr.t =
  match defs with
  | [] -> body
  | (x,e,ty) :: rest ->
      compose_lets rest (mkLetIn (x, e, ty, body))

let reduce_arg (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel i ->
      (match Environ.lookup_rel i env with
      | Context.Rel.Declaration.LocalAssum _ -> term
      | Context.Rel.Declaration.LocalDef (n,e,t) ->
          (match Constr.kind e with
          | Rel j -> mkRel (i + j)      (* delta-var *)
          | _ -> term))
  | _ -> term

let debug_reduction (rule : string) (msg : unit -> Pp.t) : unit =
  if !opt_debug_reduction then
    msg_debug_hov (Pp.str ("[codegen] reduction(" ^ rule ^ "):") ++ Pp.fnl () ++ msg ())

let test_bounded_fix (env : Environ.env) (sigma : Evd.evar_map) (n : int)
    (lift : int -> EConstr.t -> EConstr.t) (ks : int array)
    (prec : Name.t Context.binder_annot array * EConstr.types array * EConstr.t array) =
  (*msg_info_hov (Pp.str "test_bounded_fix: n=" ++ Pp.int n +++
    Printer.pr_econstr_env env sigma (mkFix ((ks,0),prec)));*)
  let h = Array.length ks in
  let vals_opt =
    let rec check_consecutive_fixes i acc =
      if h <= i then
        Some acc
      else
        match EConstr.lookup_rel (n + i) env with
        | Context.Rel.Declaration.LocalAssum _ -> None
        | Context.Rel.Declaration.LocalDef (_,e,_) ->
            match EConstr.kind sigma e with
            | Fix ((ks', j'), prec') ->
                if j' = h - i - 1 then
                  check_consecutive_fixes (i+1) (e :: acc)
                else
                  None
            | _ -> None
    in
    check_consecutive_fixes 0 []
  in
  match vals_opt with
  | None -> false
  | Some vals ->
      CList.for_all_i
        (fun j e -> EConstr.eq_constr sigma e
          (lift (-(n+h-1-j)) (mkFix ((ks, j), prec))))
        0 vals

(* find_bounded_fix returns (Some i) where i is the de Bruijn index that
    env[i] is (mkFix ((ks,0),prec)),
    env[i-1] is (mkFix ((ks,1),prec)), ...
    env[i-n+1] is (mkFix ((ks,n-1),prec))
  where n is the nubmer of the mutually recursive functions (i.e. the length of ks).

  None is returned otherwise.
  *)
let find_bounded_fix (env : Environ.env) (sigma : Evd.evar_map) (ks : int array)
    (prec : Name.t Context.binder_annot array * EConstr.types array * EConstr.t array) :
    int option =
      (*msg_info_hov (Pp.str "[codegen] find_bounded_fix:" +++
        Printer.pr_econstr_env env sigma (mkFix ((ks,0),prec)));*)
  let (nary, tary, fary) = prec in
  let h = Array.length fary in
  let nb_rel = Environ.nb_rel env in
  match free_variables_index_range env sigma (mkFix ((ks,0),prec)) with
  | None ->
      (*msg_info_hov (Pp.str "[codegen] find_bounded_fix: fv_range=None");*)
      let lift _ term = term in
      let rec loop n =
        if nb_rel < n + h - 1 then
          None
        else
          if test_bounded_fix env sigma n lift ks prec then
            Some (n + h - 1)
          else
            loop (n+1)
      in
      loop 1
  | Some (fv_min, fv_max) ->
      (*msg_info_hov (Pp.str "[codegen] find_bounded_fix: fv_range=Some (" ++ Pp.int fv_min ++ Pp.str "," ++ Pp.int fv_max ++ Pp.str ")");*)
      let lift = Vars.lift in
      let rec loop n =
        if fv_min <= n + h - 1 then
          None
        else
          if test_bounded_fix env sigma n lift ks prec then
            Some (n + h - 1)
          else
            loop (n+1)
      in
      loop 1

(* lams is a list from innermost lambda to outermost lambda *)
let rec push_rel_lams (lams : (Name.t Context.binder_annot * EConstr.t) list) (env : Environ.env) : Environ.env =
  match lams with
  | [] -> env
  | (x, ty) :: rest ->
      let decl = Context.Rel.Declaration.LocalAssum (x, ty) in
      let env2 = EConstr.push_rel decl env in
      push_rel_lams rest env2

(* invariant: letin-bindings in env is reduced form *)
let rec reduce_exp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  let t1 = Unix.times () in
  (if !opt_debug_reduce_exp then (* Set Debug CodeGen ReduceExp. *)
    msg_debug_hov (Pp.str "[codegen] reduce_exp arg:" +++ Printer.pr_econstr_env env sigma term));
  let result = reduce_exp1 env sigma term in
  (if !opt_debug_reduce_exp then
    let t2 = Unix.times () in
    msg_debug_hov (Pp.str "[codegen] reduce_exp ret (" ++ Pp.real (t2.Unix.tms_utime -. t1.Unix.tms_utime) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "reduce_exp" env sigma term result;
  result

and reduce_exp1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel i ->
      let term2 = reduce_arg env sigma term in
      if destRel sigma term2 <> i then
        (* reduction: delta-var *)
        (debug_reduction "delta-var" (fun () ->
          Printer.pr_econstr_env env sigma term ++ Pp.fnl () ++
          Pp.str "->" ++ Pp.fnl () ++
          Printer.pr_econstr_env env sigma term2);
        check_convertible "reduction(delta-var)" env sigma term term2;
        term2)
      else
        term
  | Var _ | Meta _ | Evar _ | Sort _ | Prod _
  | Const _ | Ind _ | Construct _ | Int _ | Float _ | Array _ -> term
  | Cast (e,ck,t) -> reduce_exp env sigma e
  | Lambda _ ->
      let (lams, b) = decompose_lam sigma term in
      let env2 = push_rel_lams lams env in
      compose_lam lams (reduce_exp env2 sigma b)
  | LetIn (x,e,t,b) ->
      let e' = reduce_exp env sigma e in (* xxx: we don't want to reduce function? *)
      if isLetIn sigma e' then
        (* reduction: zeta-flat *)
        let (defs, body) = decompose_lets sigma e' in
        let n = List.length defs in
        let t' = Vars.lift n t in
        let b' = Vars.liftn n 2 b in
        let term2 = compose_lets defs (mkLetIn (x, body, t', b')) in
        debug_reduction "zeta-flat" (fun () ->
          let term1 = mkLetIn (x,e',t,b) in
          Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
          Pp.str "->" ++ Pp.fnl () ++
          Printer.pr_econstr_env env sigma term2);
        check_convertible "reduction(zeta-flat)" env sigma term term2;
        let ctx = List.map (fun (x,e,t) -> Context.Rel.Declaration.LocalDef (x,e,t)) defs in
        let env2 = EConstr.push_rel_context ctx env in
        let decl = Context.Rel.Declaration.LocalDef (x, body, t') in
        let env3 = EConstr.push_rel decl env2 in
        compose_lets defs (mkLetIn (x, body, t', reduce_exp env3 sigma b'))
      else
        let decl = Context.Rel.Declaration.LocalDef (x, e', t) in
        let env2 = EConstr.push_rel decl env in
        mkLetIn (x, e', t, reduce_exp env2 sigma b)
  | Case _ ->
      try_iota_match env sigma term
        (fun term2 -> reduce_exp env sigma term2)
        (fun term2 -> term2)
  | Proj (pr,item) ->
      let item' = reduce_arg env sigma item in
      let default () = mkProj (pr, item') in
      let i = destRel sigma item' in
      (match EConstr.lookup_rel i env with
      | Context.Rel.Declaration.LocalAssum _ -> default ()
      | Context.Rel.Declaration.LocalDef (x,e,t) ->
          (* msg_info_hov (Pp.str "[codegen] reduce_exp(Proj): lookup = " ++ Printer.pr_econstr_env (Environ.pop_rel_context i env) sigma e);
          msg_info_hov (Pp.str "[codegen] reduce_exp(Proj): Projection.npars = " ++ int (Projection.npars pr));
          msg_info_hov (Pp.str "[codegen] reduce_exp(Proj): Projection.arg = " ++ int (Projection.arg pr)); *)
          let (f, args) = decompose_appvect sigma e in
          (match EConstr.kind sigma f with
          | Construct _ ->
              (* reduction: iota-proj *)
              let term2 = args.(Projection.npars pr + Projection.arg pr) in
              let term2 = Vars.lift i term2 in
              debug_reduction "iota-proj" (fun () ->
                let term1 = default () in
                Pp.str "proj-item = " ++
                Printer.pr_econstr_env env sigma item ++ Pp.str " = " ++
                Printer.pr_econstr_env (Environ.pop_rel_context i env) sigma e ++ Pp.fnl () ++
                Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
                Pp.str "->" ++ Pp.fnl () ++
                Printer.pr_econstr_env env sigma term2);
              check_convertible "reduction(iota-proj)" env sigma term term2;
              reduce_exp env sigma term2
          | _ -> default ()))
  | Fix ((ks,j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      mkFix ((ks, j), (nary, tary, Array.map (reduce_exp env2 sigma) fary))
  | CoFix (i, ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      mkCoFix (i, (nary, tary, Array.map (reduce_exp env2 sigma) fary))
  | App (f,args) ->
      (*msg_info_hov (Pp.str "[codegen] reduce_exp App f1:" +++ Printer.pr_econstr_env env sigma f);*)
      let args_nf = Array.map (reduce_arg env sigma) args in
      reduce_app env sigma f args_nf
and reduce_app (env : Environ.env) (sigma : Evd.evar_map) (f : EConstr.t) (args_nf : EConstr.t array) : EConstr.t =
  let t1 = Unix.times () in
  let term = mkApp (f, args_nf) in
  (if !opt_debug_reduce_app then (* Set Debug CodeGen ReduceApp. *)
    msg_debug_hov (Pp.str "[codegen] reduce_app arg:" +++ Printer.pr_econstr_env env sigma term));
  let result = reduce_app1 env sigma f args_nf in
  (if !opt_debug_reduce_app then
    let t2 = Unix.times () in
    msg_debug_hov (Pp.str "[codegen] reduce_app ret (" ++ Pp.real (t2.Unix.tms_utime -. t1.Unix.tms_utime) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "reduce_app" env sigma term result;
  result
and reduce_app1 (env : Environ.env) (sigma : Evd.evar_map) (f : EConstr.t) (args_nf : EConstr.t array) : EConstr.t =
  if isRel sigma f then
    let m = destRel sigma f in
    match EConstr.lookup_rel m env with
    | Context.Rel.Declaration.LocalAssum _ -> reduce_app2 env sigma f args_nf
    | Context.Rel.Declaration.LocalDef (x,e,t) ->
        (* We don't inline Case expression at function position because
           it can duplicate computation.
           For example, if
             let f := match x with tt => let y = y1 + y2 in fun z => y + z end
             in f 1 + f 2
           is reduced to
             match x with tt => let y = y1 + y2 in fun z => y + z end 1 +
             match x with tt => let y = y1 + y2 in fun z => y + z end 2,
           y1 + y2 is duplicated.
           Note that Proj cannot have such let-in expression.
           So we will support it (after we support downward funargs,
           restricted closures).  *)
        let (f_f, f_args) = decompose_appvect sigma e in
        match EConstr.kind sigma f_f with
        | Rel _ | Const _ | Construct _ | Lambda _ | Fix _ ->
            (* reduction: delta-fun *)
            reduce_app env sigma
              (Vars.lift m f_f)
              (Array.append (Array.map (Vars.lift m) f_args) args_nf)
        | _ ->
            reduce_app2 env sigma f args_nf
  else
    reduce_app2 env sigma f args_nf
and reduce_app2 (env : Environ.env) (sigma : Evd.evar_map) (f : EConstr.t) (args_nf : EConstr.t array) : EConstr.t =
  (*msg_info_hov (Pp.str "[codegen] reduce_app f_content:" +++ Printer.pr_econstr_env env sigma f_content);*)
  let default () = mkApp (reduce_exp env sigma f, args_nf) in
  let term1 = mkApp (f, args_nf) in
  match EConstr.kind sigma f with
  | Lambda (x,t,b) ->
      (* reduction: beta-var *)
      (* We apply beta reduction as much as possible using Reductionops.beta_applist. *)
      (let term2 = Reductionops.beta_applist sigma (f, (Array.to_list args_nf)) in
      debug_reduction "beta-var" (fun () ->
        Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
        Pp.str "->" ++ Pp.fnl () ++
        Printer.pr_econstr_env env sigma term2);
      check_convertible "reduction(beta-var)" env sigma term1 term2;
      reduce_exp env sigma term2)
  | App (f_f, f_args) ->
      (* reduction: delta-app *)
      let f_args_nf = Array.map (reduce_arg env sigma) f_args in
      reduce_app env sigma f_f (Array.append f_args_nf args_nf)
  | LetIn _ ->
      (* reduction: zeta-app *)
      let (defs, body) = decompose_lets sigma f in
      let args_nf_lifted = Array.map (Vars.lift (List.length defs)) args_nf in
      let term2 = compose_lets defs (mkApp (body, args_nf_lifted)) in
      debug_reduction "zeta-app" (fun () ->
        Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
        Pp.str "->" ++ Pp.fnl () ++
        Printer.pr_econstr_env env sigma term2);
      check_convertible "reduction(zeta-app)" env sigma term1 term2;
      reduce_exp env sigma term2
  | Case _ ->
      try_iota_match env sigma f
        (fun term2 -> reduce_app env sigma term2 args_nf)
        (fun term2 -> mkApp (term2, args_nf))
  | Fix ((ks,j), ((nary, tary, fary) as prec)) ->
      if ks.(j) < Array.length args_nf then
        let decarg_var = args_nf.(ks.(j)) in
        let decarg_decl = EConstr.lookup_rel (destRel sigma decarg_var) env in
        (match decarg_decl with
        | Context.Rel.Declaration.LocalAssum _ -> default ()
        | Context.Rel.Declaration.LocalDef (_,decarg_val,_) ->
            let (decarg_f, decarg_args) = decompose_appvect sigma decarg_val in
            if isConstruct sigma decarg_f then
              let h = Array.length fary in
              let fj = fary.(j) in
              match find_bounded_fix env sigma ks prec with
              | Some bounded_fix ->
                  (* reduction: iota-fix' *)
                  (*msg_info_hov (Pp.str "[codegen] bounded_fix: " ++ Printer.pr_rel_decl (Environ.pop_rel_context bounded_fix env) sigma (Environ.lookup_rel bounded_fix env));*)
                  let fj_subst = Vars.substl (List.map (fun i -> mkRel i) (iota_list (bounded_fix-h+1) h)) fj in
                  let term2 = mkApp (fj_subst, args_nf) in
                  debug_reduction "iota-fix-reuse" (fun () ->
                    let env2 = Environ.pop_rel_context (destRel sigma decarg_var) env in
                    let nf_decarg_val = Reductionops.nf_all env2 sigma decarg_val in
                    Pp.str "decreasing-argument = " ++
                    Printer.pr_econstr_env env sigma decarg_var ++ Pp.str " = " ++
                    Printer.pr_econstr_env env2 sigma decarg_val ++ Pp.str " = " ++
                    Printer.pr_econstr_env env sigma nf_decarg_val ++ Pp.fnl () ++
                    Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
                    Pp.str "->" ++ Pp.fnl () ++
                    Printer.pr_econstr_env env sigma term2);
                  check_convertible "reduction(iota-fix-reuse)" env sigma term1 term2;
                  reduce_app env sigma fj_subst args_nf
              | None ->
                  (* reduction: iota-fix *)
                  let args_nf_lifted = Array.map (Vars.lift h) args_nf in
                  let (_, defs) = CArray.fold_left2_map
                    (fun j' x t -> (j'+1, (x, Vars.lift j' (mkFix ((ks,j'), prec)), Vars.lift j' t)))
                    0 nary tary
                  in
                  let defs = Array.to_list (array_rev defs) in
                  let term2 = compose_lets defs (mkApp (fj, args_nf_lifted)) in
                  debug_reduction "iota-fix" (fun () ->
                    Pp.str "decreasing-argument = " ++
                    Printer.pr_econstr_env env sigma decarg_var ++ Pp.str " = " ++
                    Printer.pr_econstr_env (Environ.pop_rel_context (destRel sigma decarg_var) env) sigma decarg_val ++ Pp.fnl () ++
                    Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
                    Pp.str "->" ++ Pp.fnl () ++
                    Printer.pr_econstr_env env sigma term2);
                  check_convertible "reduction(iota-fix)" env sigma term1 term2;
                  let ctx = List.map (fun (x,e,t) -> Context.Rel.Declaration.LocalDef (x,e,t)) defs in
                  let env2 = EConstr.push_rel_context ctx env in
                  let b = reduce_app env2 sigma fj args_nf_lifted in
                  compose_lets defs b
            else
              default ())
      else
        default ()
  | _ -> default ()

and try_iota_match (env : Environ.env) (sigma : Evd.evar_map)
    (term1 : EConstr.t)
    (success : EConstr.t -> 'result)
    (failure : EConstr.t -> 'result) =
  let (ci,u,pms,p,iv,item,bl) = destCase sigma term1 in
  let item' = reduce_arg env sigma item in
  let failure2 () =
    let (_, _, _, p0, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
    let term2 = mkCase (ci, u, pms, p, iv, item',
      Array.map2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          (nas, reduce_exp env2 sigma body))
        bl bl0)
    in
    failure term2
  in
  let i = destRel sigma item' in
  (match EConstr.lookup_rel i env with
  | Context.Rel.Declaration.LocalAssum _ -> failure2 ()
  | Context.Rel.Declaration.LocalDef (x,item_content,t) ->
      let (f, args) = decompose_appvect sigma item_content in
      (match EConstr.kind sigma f with
      | Construct ((ind, j), _) ->
          (* reduction: iota-match *)
          let args = (array_skipn ci.ci_npar args) in
          let args = Array.map (Vars.lift i) args in
          let (nas, branch) = bl.(j-1) in
          if Array.length nas <> Array.length args then
            user_err (Pp.str "[codegen:bug] Array.length nas <> Array.length args");
          let term2 = Vars.substl (CArray.rev_to_list args) branch in (* xxx: let-in in constructor types not supported *)
          debug_reduction "iota-match" (fun () ->
            let item_env = Environ.pop_rel_context i env in
            Pp.str "match-item =" +++
            Printer.pr_econstr_env env sigma item +++ Pp.str "=" +++
            (if destRel sigma item <> destRel sigma item' then
              Printer.pr_econstr_env env sigma item' +++ Pp.str "="
            else Pp.mt ()) +++
            Printer.pr_econstr_env item_env sigma item_content ++ Pp.fnl () ++
            Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
            Pp.str "->" ++ Pp.fnl () ++
            Printer.pr_econstr_env env sigma term2);
          check_convertible "reduction(iota-match)" env sigma term1 term2;
          success term2
      | _ ->
          failure2 ()))

let rec normalize_types (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ | Array _
  | Const _ | Construct _ -> term
  | Evar (ev, es) ->
      mkEvar (ev, List.map (normalize_types env sigma) es)
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
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, p0, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      (* We use Reductionops.nf_all for pms, p and iv.
         This reduces variables.
         It makes possible to remove let-in outside of this match-expression such as:
         let S := nat in match n in list S return nat with ... end
         Note that "S" of "in list S" is represented by pms.  *)
      let pms' = Array.map (Reductionops.nf_all env sigma) pms in
      let p' =
        let (nas,body), (ctx,_) = p, p0 in
        let env2 = EConstr.push_rel_context ctx env in
        (nas, Reductionops.nf_all env2 sigma body)
      in
      let iv' = map_invert (Reductionops.nf_all env sigma) iv in
      let item' = normalize_types env sigma item in
      let bl' =
        Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            (nas, normalize_types env2 sigma body))
          bl bl0
      in
      mkCase (ci,u,pms',p',iv',item',bl')
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
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let tary' = Array.map (Reductionops.nf_all env sigma) tary in
      let fary' = Array.map (normalize_types env2 sigma) fary in
      mkFix ((ks, j), (nary, tary', fary'))
  | CoFix (i, ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let tary' = Array.map (Reductionops.nf_all env sigma) tary in
      let fary' = Array.map (normalize_types env2 sigma) fary in
      mkCoFix (i, (nary, tary', fary'))

(*
  "normalize_static_arguments" breaks V-normal form but it is not a problem
  because "delete_unused_let" works well with general Gallina terms and
  "replace" recovers V-normal form.

  normalize_static_arguments: breaks V-normal, reduces variable references from static arguments
  delete_unused_let: removes unsed let bindings
  replace: replaces application with static arguments by specialized function application
*)
let rec normalize_static_arguments (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ -> term
  | Var _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Var:" +++ Printer.pr_econstr_env env sigma term)
  | Evar _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Evar:" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Cast:" +++ Printer.pr_econstr_env env sigma term)
  | Prod _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Prod:" +++ Printer.pr_econstr_env env sigma term)
  | CoFix _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected CoFix:" +++ Printer.pr_econstr_env env sigma term)
  | Array _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Array:" +++ Printer.pr_econstr_env env sigma term)
  | Lambda (x, t, b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let b' = normalize_static_arguments env2 sigma b in
      mkLambda (x, t, b')
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (normalize_static_arguments env2 sigma) fary in
      mkFix ((ks, j), (nary, tary, fary'))
  | LetIn (x, e, t, b) ->
      let e' = normalize_static_arguments env sigma e in
      let decl = Context.Rel.Declaration.LocalDef (x, e', t) in
      let env2 = EConstr.push_rel decl env in
      let b' = normalize_static_arguments env2 sigma b in
      mkLetIn (x, e', t, b')
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let bl' =
        Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            (nas, normalize_static_arguments env2 sigma body))
          bl bl0
      in
      mkCase (ci,u,pms,p,iv,item,bl')
  | Proj (proj, e) ->
      term (* e is a variable because V-normal form *)
  | Const (ctnt, u) ->
      term
  | Construct (cstr, u) ->
      term
  | App (f, args) ->
      let normalize_args f' =
        let sd_list = codegen_auto_sd_list env sigma f' in
        let nl = List.length sd_list in
        let na = Array.length args in
        (* We don't raise an error if nl <> na because
           the application itself can be dropped if it is not used *)
        let sd_ary =
          if nl < na then
            Array.of_list (List.append sd_list (CList.make (na - nl) SorD_D))
          else
            Array.of_list (CList.firstn na sd_list)
        in
        let args' = Array.map2
          (fun sd arg ->
            match sd with
            | SorD_S -> Reductionops.nf_all env sigma arg
            | SorD_D -> arg)
          sd_ary
          args
        in
        mkApp (f, args')
      in
      match EConstr.kind sigma f with
      | Const (ctnt, u) ->
          let f' = Constr.mkConst ctnt in
          normalize_args f'
      | Construct (cstr, u) ->
          let f' = Constr.mkConstruct cstr in
          normalize_args f'
      | _ ->
          let f' = normalize_static_arguments env sigma f in
          mkApp (f', args)

let rec count_false_in_prefix (n : int) (vars_used : bool list) : int =
  if n <= 0 then
    0
  else
    match vars_used with
    | [] -> 0
    | b :: rest ->
        if b then
          count_false_in_prefix (n-1) rest
        else
          1 + count_false_in_prefix (n-1) rest

let unlift_unused (sigma : Evd.evar_map) (vars_used : bool list) (term : EConstr.t) : EConstr.t =
  let rec aux (vars_used : bool list) (term : EConstr.t) : EConstr.t =
    match EConstr.kind sigma term with
    | Var _ -> user_err (Pp.str "[codegen] codegen doesn't support Var.")
    | Evar _ -> user_err (Pp.str "[codegen] codegen doesn't support Evar.")
    | Meta _ -> user_err (Pp.str "[codegen] codegen doesn't support Meta.")
    | Int _ -> user_err (Pp.str "[codegen] codegen doesn't support Int.")
    | Float _ -> user_err (Pp.str "[codegen] codegen doesn't support Float.")
    | Array _ -> user_err (Pp.str "[codegen] codegen doesn't support Array.")
    | CoFix _ -> user_err (Pp.str "[codegen] codegen doesn't support CoFix.")
    | Sort _ | Ind _ | Const _ | Construct _ -> term
    | Rel i ->
        if not (List.nth vars_used (i-1)) then
          user_err (Pp.str "[codegen:bug] unlift_unused found that vars_used is invalid");
        mkRel (i - count_false_in_prefix (i-1) vars_used)
    | Proj (proj, e) ->
        mkProj (proj, aux vars_used e)
    | Cast (e,ck,t) ->
        mkCast (aux vars_used e, ck, aux vars_used t)
    | App (f, args) ->
        mkApp (aux vars_used f, Array.map (aux vars_used) args)
    | LetIn (x,e,t,b) ->
        mkLetIn (x, aux vars_used e, aux vars_used e, aux (true :: vars_used) e)
    | Case (ci,u,pms,p,iv,item,bl) ->
       let pms' = Array.map (aux vars_used) pms in
       let p' =
         let (nas,body) = p in
         let body' = aux (CList.addn (Array.length nas) true vars_used) body in
         (nas,body')
       in
       let iv' = map_invert (aux vars_used) iv in
       let item' = aux vars_used item in
       let bl' = Array.map
         (fun (nas,body) -> (nas, aux (CList.addn (Array.length nas) true vars_used) body))
         bl
       in
       mkCase (ci, u, pms', p', iv', item', bl')
    | Prod (x,t,b) ->
        mkProd (x, aux vars_used t, aux (true :: vars_used) b)
    | Lambda (x,t,b) ->
        mkLambda (x, aux vars_used t, aux (true :: vars_used) b)
    | Fix ((ks, j), (nary, tary, fary)) ->
        let h = Array.length fary in
        let vars_used' = CList.addn h true vars_used in
        mkFix ((ks, j),
               (nary,
                Array.map (aux vars_used) tary,
                Array.map (aux vars_used') fary))
  in
  aux vars_used term

let rec delete_unused_let_rec (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (IntSet.t * (bool list -> EConstr.t)) =
  (if !opt_debug_delete_let then
    msg_debug_hov (Pp.str "[codegen] delete_unused_let_rec arg:" +++ Printer.pr_econstr_env env sigma term));
  let (fvs, retf) = delete_unused_let_rec1 env sigma term in
  (fvs,
   fun vars_used ->
     assert (List.length vars_used = Environ.nb_rel env);
     retf vars_used)
and delete_unused_let_rec1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (IntSet.t * (bool list -> EConstr.t)) =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ | Array _
  | Const _ | Construct _ -> (IntSet.empty, fun vars_used -> term)
  | Rel i ->
      let fvs = IntSet.singleton (Environ.nb_rel env - i) in
      (fvs, fun vars_used -> mkRel (i - count_false_in_prefix (i-1) vars_used))
  | Evar (ev, es) ->
      let fs2 = List.map (delete_unused_let_rec env sigma) es in
      let fs = List.map snd fs2 in
      let fvs = List.fold_left IntSet.union IntSet.empty (List.map fst fs2) in
      (fvs, fun vars_used -> mkEvar (ev, List.map (fun f -> f vars_used) fs))
  | Proj (proj, e) ->
      let (fvs, f) = delete_unused_let_rec env sigma e in
      (fvs, fun vars_used -> mkProj (proj, f vars_used))
  | Cast (e,ck,t) ->
      let (fvse, fe) = delete_unused_let_rec env sigma e in
      let (fvst, ft) = delete_unused_let_rec env sigma t in
      (IntSet.union fvse fvst, fun vars_used -> mkCast(fe vars_used, ck, ft vars_used))
  | App (f, args) ->
      let (fvs1, ff) = delete_unused_let_rec env sigma f in
      let fargs2 = Array.map (delete_unused_let_rec env sigma) args in
      let fargs = Array.map snd fargs2 in
      let fvs = Array.fold_left IntSet.union fvs1 (Array.map fst fargs2) in
      (fvs, fun vars_used -> mkApp (ff vars_used, Array.map (fun g -> g vars_used) fargs))
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let (fvsb, fb) = delete_unused_let_rec env2 sigma b in
      let declared_var_used = IntSet.mem (Environ.nb_rel env) fvsb in
      let (fvse, fe) = delete_unused_let_rec env sigma e in
      let (fvst, ft) = delete_unused_let_rec env sigma t in
      let retain =
        declared_var_used ||
        (Linear.is_linear env sigma t) ||
        (IntSet.exists
          (fun i ->
            let rel = EConstr.lookup_rel (Environ.nb_rel env - i) env in
            let ty = Context.Rel.Declaration.get_type rel in
            Linear.is_linear env sigma ty)
          fvse)
      in
      if retain then
        (* Environ.nb_rel env, same as Environ.nb_rel env2 - 1,
          means the bound variable with this let-in. *)
        let fvs = IntSet.union (IntSet.remove (Environ.nb_rel env) fvsb) (IntSet.union fvse fvst) in
        (fvs, fun vars_used -> mkLetIn (x, fe vars_used, ft vars_used, fb (true :: vars_used)))
      else
        (* reduction: zeta-del *)
        (fvsb, fun vars_used -> fb (false :: vars_used))
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, p0, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let fv =
        Array.fold_left
          (fun fv pm -> IntSet.union fv (free_variables_level_set env sigma pm))
          IntSet.empty pms
      in
      let fv = IntSet.union fv
        (let (nas,body), (ctx,_) = p, p0 in
        let env2 = EConstr.push_rel_context ctx env in
        free_variables_level_set ~without:(Array.length nas) env2 sigma body)
      in
      let fv =
        Constr.fold_invert
          (fun fv e -> IntSet.union fv (free_variables_level_set env sigma e))
          fv iv
      in
      let fv = IntSet.union fv (free_variables_level_set env sigma item) in
      let branches2 =
        Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            let (fv_br, g) = delete_unused_let_rec env2 sigma body in
            let fv_br' = IntSet.filter (fun l -> l < Environ.nb_rel env) fv_br in
            (fv_br', g))
          bl bl0
      in
      let fv = Array.fold_left (fun fv (fv_br,_) -> IntSet.union fv fv_br) fv branches2 in
      (fv,
       fun vars_used ->
         let pms' = Array.map (unlift_unused sigma vars_used) pms in
         let p' =
           let (nas,body) = p in
           let body' = unlift_unused sigma (CList.addn (Array.length nas) true vars_used) body in
           (nas,body')
         in
         let iv' = map_invert (unlift_unused sigma vars_used) iv in
         let item' = unlift_unused sigma vars_used item in
         let bl' = Array.map2
           (fun (nas,_) (_,g) -> (nas, g (CList.addn (Array.length nas) true vars_used)))
           bl branches2
         in
         mkCase (ci, u, pms', p', iv', item', bl'))
  | Prod (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let (fvst, ft) = delete_unused_let_rec env sigma t in
      let (fvsb, fb) = delete_unused_let_rec env2 sigma b in
      let fvs = IntSet.union fvst (IntSet.remove (Environ.nb_rel env) fvsb) in
      (fvs, fun vars_used -> mkProd (x, ft vars_used, fb (true :: vars_used)))
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let (fvst, ft) = delete_unused_let_rec env sigma t in
      let (fvse, fe) = delete_unused_let_rec env2 sigma e in
      let fvs = IntSet.union fvst (IntSet.remove (Environ.nb_rel env) fvse) in
      (fvs, fun vars_used -> mkLambda (x, ft vars_used, fe (true :: vars_used)))
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let h = Array.length fary in
      let env2 = push_rec_types prec env in
      let ftary2 = Array.map (delete_unused_let_rec env sigma) tary in
      let ftary = Array.map snd ftary2 in
      let fvst = Array.fold_left IntSet.union IntSet.empty (Array.map fst ftary2) in
      let ffary2 = Array.map (delete_unused_let_rec env2 sigma) fary in
      let ffary = Array.map snd ffary2 in
      let fvsf = Array.fold_left IntSet.union IntSet.empty (Array.map fst ffary2) in
      let fvs =
        let n = Environ.nb_rel env in
        IntSet.union fvst (IntSet.filter (fun i -> i < n) fvsf)
      in
      (fvs,
       fun vars_used ->
         let vars_used' = CList.addn h true vars_used in
         mkFix ((ks, j),
                (nary,
                 Array.map (fun g -> g vars_used) ftary,
                 Array.map (fun g -> g vars_used') ffary)))
  | CoFix (i, ((nary, tary, fary) as prec)) ->
      let h = Array.length fary in
      let env2 = push_rec_types prec env in
      let ftary2 = Array.map (delete_unused_let_rec env sigma) tary in
      let ftary = Array.map snd ftary2 in
      let fvst = Array.fold_left IntSet.union IntSet.empty (Array.map fst ftary2) in
      let ffary2 = Array.map (delete_unused_let_rec env2 sigma) fary in
      let ffary = Array.map snd ffary2 in
      let fvsf = Array.fold_left IntSet.union IntSet.empty (Array.map fst ffary2) in
      let fvs =
        let n = Environ.nb_rel env in
        IntSet.union fvst (IntSet.filter (fun i -> i < n) fvsf)
      in
      (fvs,
       fun vars_used ->
        let vars_used' = CList.addn h true vars_used in
        mkCoFix (i,
                 (nary,
                  Array.map (fun g -> g vars_used) ftary,
                  Array.map (fun g -> g vars_used') ffary)))

let delete_unused_let (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (if !opt_debug_delete_let then
    msg_debug_hov (Pp.str "[codegen] delete_unused_let arg:" +++ Printer.pr_econstr_env env sigma term));
  assert (Environ.nb_rel env = 0);
  let (fvs, f) = delete_unused_let_rec env sigma term in
  let result = f [] in
  (if !opt_debug_delete_let then
    msg_debug_hov (Pp.str "[codegen] delete_unused_let ret:" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "specialize" env sigma term result;
  result

(* func must be a constant or constructor *)
let replace_app ~(cfunc : string) (env : Environ.env) (sigma : Evd.evar_map) (func : Constr.t) (args : EConstr.t array) : Environ.env * EConstr.t * string =
  (* msg_info_hov (Pp.str "[codegen] replace_app:" +++ Printer.pr_econstr_env env sigma (mkApp ((EConstr.of_constr func), args))); *)
  let sp_cfg = codegen_auto_arguments_internal ~cfunc env sigma func in
  let sd_list = drop_trailing_d sp_cfg.sp_sd_list in
  (if Array.length args < List.length sd_list then
    user_err (Pp.str "[codegen] Not enough arguments for" +++
              Printer.pr_constr_env env sigma func +++
              Pp.str "(needs" +++
              Pp.int (List.length sd_list) +++
              Pp.str "but" +++
              Pp.int (Array.length args) ++
              Pp.str ")"));
  let sd_list = List.append sd_list (List.init (Array.length args - List.length sd_list) (fun _ -> SorD_D)) in
  let static_flags = List.map (fun sd -> sd = SorD_S) sd_list in
  let nf_static_args = CArray.filter_with static_flags args in (* static arguments are already normalized by normalize_static_arguments *)
  (Array.iteri (fun i nf_arg ->
    let fvs = free_variables_index_set env sigma nf_arg in
    if not (IntSet.is_empty fvs) then
      user_err (Pp.str "[codegen] Free variable found in a static argument:" +++
        Printer.pr_constr_env env sigma func ++
        Pp.str "'s" +++
        Pp.str (CString.ordinal (i+1)) +++
        Pp.str "static argument" +++
        Printer.pr_econstr_env env sigma nf_arg +++
        Pp.str "refer" +++
        pp_joinmap_list (Pp.str ",")
          (fun k ->
            let decl = Environ.lookup_rel k env in
            let name = Context.Rel.Declaration.get_name decl in
            Pp.str (str_of_name_permissive name))
          (IntSet.elements fvs)
        ))
    nf_static_args);
  let nf_static_args = CArray.map_to_list (EConstr.to_constr sigma) nf_static_args in
  let efunc = EConstr.of_constr func in
  let efunc_type = Retyping.get_type_of env sigma efunc in
  let (_, presimp, _) = build_presimp env sigma efunc efunc_type sd_list nf_static_args in
  (*msg_info_hov (Pp.str "[codegen] replace presimp:" +++ Printer.pr_constr_env env sigma presimp);*)
  let (env, sp_inst) = match ConstrMap.find_opt presimp sp_cfg.sp_instance_map with
    | None ->
        let icommand = if sp_cfg.sp_is_cstr then CodeGenPrimitive else CodeGenStaticFunc in
        codegen_define_instance ~cfunc env sigma icommand func nf_static_args None
    | Some sp_inst -> (env, sp_inst)
  in
  let sp_ctnt = sp_inst.sp_presimp_constr in
  let dynamic_flags = List.map (fun sd -> sd = SorD_D) sd_list in
  let newexp = mkApp (EConstr.of_constr sp_ctnt, CArray.filter_with dynamic_flags args) in
  (env, newexp, sp_inst.sp_cfunc_name)

(* This function assumes S-normal form.
   So this function doesn't traverse subterms of Proj, Cast,
   arguments of App and item of Case. *)
let rec replace ~(cfunc : string) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Environ.env * EConstr.t * StringSet.t =
  (if !opt_debug_replace then
    msg_debug_hov (Pp.str "[codegen] replace arg:" +++ Printer.pr_econstr_env env sigma term));
  let (env, result, referred_cfuncs) = replace1 ~cfunc env sigma term in
  (if !opt_debug_replace then
    msg_debug_hov (Pp.str "[codegen] replace ret:" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "replace" env sigma term result;
  (env, result, referred_cfuncs)
and replace1 ~(cfunc : string) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Environ.env * EConstr.t * StringSet.t =
  match EConstr.kind sigma term with
  | Rel _ | Var _ | Meta _ | Evar _ | Sort _ | Prod _
  | Ind _ | Int _ | Float _ | Array _
  | Proj _ | Cast _ -> (env, term, StringSet.empty)
  | Lambda (x, t, e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let (env2', e', referred_cfuncs) = replace ~cfunc env2 sigma e in
      let env' = Environ.pop_rel_context 1 env2' in
      (env', mkLambda (x, t, e'), referred_cfuncs)
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let ((env2', referred_cfuncs), fary') = CArray.fold_left_map
        (fun (env3, referred_cfuncs) f ->
          let (env4, f', referred_cfuncs') = replace ~cfunc env3 sigma f in
          ((env4, StringSet.union referred_cfuncs referred_cfuncs'), f'))
        (env2, StringSet.empty) fary
      in
      let env' = Environ.pop_rel_context (Array.length nary) env2' in
      (env', mkFix ((ks, j), (nary, tary, fary')), referred_cfuncs)
  | CoFix _ ->
      user_err (Pp.str "[codegen] codegen doesn't support CoFix.")
  | LetIn (x, e, t, b) ->
      let (env', e', referred_cfuncs1) = replace ~cfunc env sigma e in
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env' in
      let (env2', b', referred_cfuncs2) = replace ~cfunc env2 sigma b in
      let env'' = Environ.pop_rel_context 1 env2' in
      let referred_cfuncs = StringSet.union referred_cfuncs1 referred_cfuncs2 in
      (env'', mkLetIn (x, e', t, b'), referred_cfuncs)
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, p0, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let ((env', referred_cfuncs), bl') = CArray.fold_left2_map
        (fun (env2, referred_cfuncs) (nas,body) (ctx,_) ->
          let env2x = EConstr.push_rel_context ctx env2 in
          let (env3x, body', referred_cfuncs') = replace ~cfunc env2x sigma body in
          let env3 = Environ.pop_rel_context (Array.length nas) env3x in
          ((env3, StringSet.union referred_cfuncs referred_cfuncs'), (nas,body')))
        (env, StringSet.empty) bl bl0
      in
      (env', mkCase (ci,u,pms,p,iv,item,bl'), referred_cfuncs)
  | Const (ctnt, u) ->
      let f' = Constr.mkConst ctnt in
      let (env2, f'', referred_cfunc) = replace_app ~cfunc env sigma f' [| |] in
      (env2, f'', StringSet.singleton referred_cfunc)
  | Construct (cstr, u) ->
      let f' = Constr.mkConstruct cstr in
      let (env2, f'', referred_cfunc) = replace_app ~cfunc env sigma f' [| |] in
      (env2, f'', StringSet.singleton referred_cfunc)
  | App (f, args) ->
      match EConstr.kind sigma f with
      | Const (ctnt, u) ->
          let f' = Constr.mkConst ctnt in
          let (env2, f'', referred_cfunc) = replace_app ~cfunc env sigma f' args in
          (env2, f'', StringSet.singleton referred_cfunc)
      | Construct (cstr, u) ->
          let f' = Constr.mkConstruct cstr in
          let (env2, f'', referred_cfunc) = replace_app ~cfunc env sigma f' args in
          (env2, f'', StringSet.singleton referred_cfunc)
      | _ ->
          let (env', f, referred_cfuncs) = replace ~cfunc env sigma f in
          (env', mkApp (f, args), referred_cfuncs)

let rec reduce_eta (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (if !opt_debug_reduce_eta then
    msg_debug_hov (Pp.str "[codegen] reduce_eta arg:" +++ Printer.pr_econstr_env env sigma term));
  let result = reduce_eta1 env sigma term in
  (if !opt_debug_reduce_eta then
    msg_debug_hov (Pp.str "[codegen] reduce_eta ret:" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "reduce_eta" env sigma term result;
  result

and reduce_eta1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel i ->
      term
  | Var _ | Meta _ | Evar _ | Sort _ | Prod _ | Array _ | CoFix _ ->
      user_err (Pp.str "[codegen:reduce_eta] unexpected" +++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | Const _ | Ind _ | Construct _ | Int _ | Float _ -> term
  | Cast (e,ck,t) -> reduce_eta env sigma e
  | Lambda _ ->
      let (lams, b) = decompose_lam sigma term in
      let env2 = push_rel_lams lams env in
      (match EConstr.kind sigma b with
      | App (f, args) when isFix sigma f ->
          (*msg_info_hov (Pp.str "[codegen:reduce_eta1]" +++
            Pp.str "f=" ++ Printer.pr_econstr_env env2 sigma f +++
            Pp.str "args=[" ++ pp_sjoinmap_ary (Printer.pr_econstr_env env2 sigma) args ++ Pp.str "]");*)
          let min_fv =
            match free_variables_index_range env2 sigma f with
            | None -> List.length lams + 1 (* does not refer variables in lams *)
            | Some (min,max) -> min
          in
          let nargs = Array.length args in
          let rec instantiate_prods f_ty i acc =
            if i < nargs then
              let f_ty = Reductionops.whd_all env2 sigma f_ty in
              match EConstr.kind sigma f_ty with
              | Prod (x,ty,b) ->
                  let ty = Reductionops.nf_all env2 sigma ty in
                  instantiate_prods (Vars.subst1 args.(i) b) (i+1) (ty :: acc)
              | _ -> assert false
            else
              acc
          in
          let f_ty = Retyping.get_type_of env2 sigma f in
          (*msg_info_hov (Pp.str "[codegen:reduce_eta1]" +++
            Pp.str "f_ty=" ++ (Printer.pr_econstr_env env2 sigma f_ty));*)
          let prods = instantiate_prods f_ty 0 [] in
          (*msg_info_hov (Pp.str "[codegen:reduce_eta1]" +++
            Pp.str "f_formal_args=[" ++ pp_sjoinmap_list (Printer.pr_econstr_env env2 sigma) (List.rev prods) ++ Pp.str "]");*)
          let rec count_eta_reducible_args lams prods n =
            match lams, prods with
            | (x,ty_lam) :: rest_lams, ty_prod :: rest_prods ->
                if nargs <= n then
                  n
                else if min_fv-1 <= n then
                  n
                else if destRel sigma args.(nargs - n - 1) <> (n+1) then
                  n
                else
                  if EConstr.eq_constr sigma (Vars.lift (n+1) ty_lam) ty_prod then
                    count_eta_reducible_args rest_lams rest_prods (n+1)
                  else
                    n
            | _, _ -> n
          in
          let n = count_eta_reducible_args lams prods 0 in
          (*msg_info_hov (Pp.str "[codegen:reduce_eta1] num_eta_reducible_args=" ++ Pp.int n);*)
          if n = nargs then
            (* We apply eta reduction only if it eliminates all arguments.
              If some arguments are retained (i.e. partial application is retained),
              they will be reproduced by complete_args
              with different variable names.
              *)
            let lams3 = CList.skipn n lams in
            let args3 = [||] in
            let f3 = Vars.lift (-n) f in
            let env3 = push_rel_lams lams3 env in
            compose_lam lams3 (reduce_eta env3 sigma (mkApp (f3,args3)))
          else
            compose_lam lams (reduce_eta env2 sigma b)
      | _ ->
        compose_lam lams (reduce_eta env2 sigma b))
  | LetIn (x,e,t,b) ->
      let e' = reduce_eta env sigma e in
      let decl = Context.Rel.Declaration.LocalDef (x, e', t) in
      let env2 = EConstr.push_rel decl env in
      mkLetIn (x, e', t, reduce_eta env2 sigma b)
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let bl' =
        Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            (nas,reduce_eta env2 sigma body))
          bl bl0
      in
      mkCase (ci,u,pms,p,iv,item,bl')
  | Proj (pr,item) ->
      term
  | Fix ((ks,j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      mkFix ((ks, j), (nary, tary, Array.map (reduce_eta env2 sigma) fary))
  | App (f,args) ->
      mkApp (reduce_eta env sigma f, args)

(*
  complete_args_fun transforms "term" which does not contain partial applications.
*)
let rec complete_args_fun (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (if !opt_debug_complete_arguments then
    msg_debug_hov (Pp.str "[codegen] complete_args_fun arg:" +++ Printer.pr_econstr_env env sigma term));
  let result = complete_args_fun1 env sigma term in
  (if !opt_debug_complete_arguments then
    msg_debug_hov (Pp.str "[codegen] complete_args_fun result:" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "complete_args_fun" env sigma term result;
  result
and complete_args_fun1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (x, t, complete_args_fun env2 sigma e)
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary2 = Array.map (complete_args_fun env2 sigma) fary in
      mkFix ((ks, j), (nary, tary, fary2))
  | _ ->
      complete_args_exp env sigma term

(*
  - complete_args_exp transforms closure creation expressions in "term" to
    lambda-expressions with all arguments. (fix-term is permitted.)
  - closure creation are
    - partial application, or
    - constant and constructor of function type which is not positioned
      at a function position of application.
  - We don't consider a variable as closure creation.
    (because the closure is already creaated and bounded to the variable.)
*)
and complete_args_exp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (if !opt_debug_complete_arguments then
    msg_debug_hov (Pp.str "[codegen] complete_args_exp arg:" +++
    Printer.pr_econstr_env env sigma term));
  let result = complete_args_exp1 env sigma term in
  (if !opt_debug_complete_arguments then
    msg_debug_hov (Pp.str "[codegen] complete_args_exp result:" +++ Printer.pr_econstr_env env sigma result));
  check_convertible "complete_args_exp" env sigma term result;
  result
and complete_args_exp1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  let eta term =
    let fargs =
      let ty = Retyping.get_type_of env sigma term in
      let ty = Reductionops.nf_all env sigma ty in
      fst (decompose_prod sigma ty)
      (* fargs is a list from innermost formal argument to outermost formal argument *)
    in
    if CList.is_empty fargs then
      term
    else
      let r = List.length fargs in
      let term' = Vars.lift r term in
      let args = (Array.map mkRel (array_rev (iota_ary 1 r))) in
      (* reduction/expansion: eta-expansion *)
      compose_lam fargs (mkApp (term', args))
  in
  match EConstr.kind sigma term with
  | App (f,args) ->
      (match EConstr.kind sigma f with
      | Rel _ | Const _ | Construct _ -> eta term
      | Fix _  -> eta (mkApp (complete_args_fun env sigma f, args))
      | _ -> user_err (Pp.str "[codegen:complete_args_exp:bug] unexpected function position:" +++ Printer.pr_econstr_env env sigma f))
  | Cast (e,ck,t) -> complete_args_exp env sigma e
  | Rel i -> term
  | Const _ -> eta term
  | Construct _ -> eta term
  | Lambda _ ->
      complete_args_fun env sigma term
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      mkLetIn (x,
        complete_args_exp env sigma e,
        t,
        complete_args_exp env2 sigma b)
  | Case (ci,u,pms,mpred,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, mpred, iv, item, bl) in
      mkCase (ci,u,pms,mpred,iv,item,
        Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            (nas, complete_args_exp env2 sigma body))
          bl bl0)
  | Fix _ ->
      complete_args_fun env sigma term
  | Proj (proj, e) ->
      mkProj (proj, complete_args_exp env sigma e)
  | Var _ | Meta _ | Evar _
  | Sort _ | Prod _ | Ind _
  | CoFix _
  | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:complete_arguments_exp] unexpected term:" +++
        Printer.pr_econstr_env env sigma term)

let complete_args (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (*msg_debug_hov (Pp.str "[codegen] complete_args arg:" +++ Printer.pr_econstr_env env sigma term);*)
  let result = complete_args_fun env sigma term in
  (*msg_debug_hov (Pp.str "[codegen] complete_args result:" +++ Printer.pr_econstr_env env sigma result);*)
  result

let rec formal_argument_names (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Name.t Context.binder_annot list =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      x :: formal_argument_names env2 sigma e
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      formal_argument_names env2 sigma fary.(j)
  | _ -> []

let monomorphism_check (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : unit =
  let ty = Retyping.get_type_of env sigma term in
  if not (is_monomorphic_type env sigma (Reductionops.nf_all env sigma ty)) then
    user_err (Pp.str "[codegen] function must be monomorphic:" +++
      Printer.pr_econstr_env env sigma term +++
      Pp.str ":" +++
      Printer.pr_econstr_env env sigma ty);
  let rec aux env term =
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | Cast _
    | CoFix _ | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen] unexpected term:" +++
        Printer.pr_econstr_env env sigma term)
    | Sort _ | Prod (_, _, _) | Ind _ ->
      user_err (Pp.str "[codegen] type in expression:" +++
        Printer.pr_econstr_env env sigma term)
    | Lambda (x,t,b) ->
        if not (is_monomorphic_type env sigma t) then
          user_err (Pp.str "[codegen] lambda argument type must be monomorphic:" +++ Printer.pr_econstr_env env sigma t);
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        aux env2 b
    | LetIn (x,e,t,b) ->
        if not (is_monomorphic_type env sigma t) then
          user_err (Pp.str "[codegen] let-in type must be monomorphic:" +++ Printer.pr_econstr_env env sigma t);
        aux env e;
        let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
        let env2 = EConstr.push_rel decl env in
        aux env2 b;
    | Fix ((ks, j), (nary, tary, fary)) ->
        Array.iter
          (fun t ->
            if not (is_monomorphic_type env sigma t) then
              user_err (Pp.str "[codegen] fix-function must be monomorphic:" +++ Printer.pr_econstr_env env sigma t))
          tary;
        let env2 = push_rec_types (nary, tary, fary) env in
        Array.iter (fun f -> aux env2 f) fary
    | App (f,args) -> aux env f
    | Rel _ -> ()
    | Const _ -> ()
    | Construct _ -> ()
    | Case (ci,u,pms,mpred,iv,item,bl) ->
        let (_, _, _, mpred0, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, mpred, iv, item, bl) in
        (let (nas,body), (ctx,_) = mpred, mpred0 in
          let env2 = EConstr.push_rel_context ctx env in
          let body = Reductionops.nf_all env2 sigma body in
          if not (is_monomorphic_type env2 sigma body) then
            user_err (Pp.str "[codegen] match-predicate must be monomorphic:" +++ Printer.pr_econstr_env env sigma body));
        Array.iter2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            (for i = List.length ctx downto 1 do
              let ty = Context.Rel.Declaration.get_type (lookup_rel i env2) in
              let env1 = Environ.pop_rel_context i env2 in
              let ty = Reductionops.nf_all env1 sigma ty in
              if not (is_monomorphic_type env1 sigma ty) then
                user_err (Pp.str "[codegen] constructor argument type in match-expression must be monomorphic:" +++ Printer.pr_econstr_env env sigma ty)
            done);
            aux env2 body)
          bl bl0;
    | Proj _ -> ()
  in
  aux env term

let rename_vars (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  let make_new_name prefix counter old_name =
    counter := !counter +1;
    let prefix = prefix ^ string_of_int !counter in
    match old_name with
    | Name.Anonymous -> Name.mk_name (Id.of_string prefix)
    | Name.Name id -> Name.mk_name (Id.of_string (prefix ^ "_" ^ (c_id (Id.to_string id))))
  in
  let num_vars = ref 0 in
  let make_new_var old_name = Context.map_annot (fun old_name -> make_new_name "v" num_vars old_name) old_name in
  let num_fixfuncs = ref 0 in
  let make_new_fixfunc old_name = Context.map_annot (fun old_name -> make_new_name "fixfunc" num_fixfuncs old_name) old_name in
  let rec r (env : Environ.env) (term : EConstr.t) =
    match EConstr.kind sigma term with
    | Lambda (x,t,e) ->
        let x2 = make_new_var x in
        let decl = Context.Rel.Declaration.LocalAssum (x2, t) in
        let env2 = EConstr.push_rel decl env in
        mkLambda (x2, t, r env2 e)
    | LetIn (x,e,t,b) ->
        let x2 = make_new_var x in
        let decl = Context.Rel.Declaration.LocalDef (x2, e, t) in
        let env2 = EConstr.push_rel decl env in
        mkLetIn (x2, r env e, t, r env2 b)
    | Fix ((ks, j), (nary, tary, fary)) ->
        let nary2 = Array.map (fun n -> make_new_fixfunc n) nary in
        let env2 = push_rec_types (nary2, tary, fary) env in
        let fary2 = Array.map (fun e -> r env2 e) fary in
        let tary2 = Array.map2 (fun t f ->
            let argnames = List.rev (formal_argument_names env2 sigma f) in
            let (args, result_type) = decompose_prod sigma t in
            (if List.length argnames <> List.length args then
              user_err (Pp.str "[codegen:rename_vars:bug] unexpected length of formal arguments:"));
            let args2 = List.map2 (fun (arg_name, arg_type) arg_name2 -> (arg_name2, arg_type)) args argnames in
            compose_prod args2 result_type)
          tary fary2
        in
        mkFix ((ks, j), (nary2, tary2, fary2))
    | App (f,args) ->
        mkApp (r env f, args)
    | Cast (e,ck,t) -> mkCast (r env e, ck, t)
    | Rel i -> term
    | Const _ -> term
    | Construct _ -> term
    | Case (ci,u,pms,mpred,iv,item,bl) ->
        let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, mpred, iv, item, bl) in
        mkCase (ci, u, pms, mpred, iv, item,
          Array.map2
            (fun (nas,body) (ctx,_) ->
              let env2 = EConstr.push_rel_context ctx env in
              let nas' = Array.map make_new_var nas in
              (nas', r env2 body))
            bl bl0)
    | Proj _ -> term
    | Var _ | Meta _ | Evar _ | Sort _ | Prod (_, _, _) | Ind _
    | CoFix _ | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:rename_vars] unexpected term:" +++
        Printer.pr_econstr_env env sigma term)
  in
  r env term

let prevterm : EConstr.t option ref = ref None
let specialization_time = ref (Unix.times ())

let init_debug_simplification () : unit =
  if !opt_debug_simplification then begin
    prevterm := None;
    specialization_time := Unix.times ()
  end

let debug_simplification (env : Environ.env) (sigma : Evd.evar_map) (step : string) (term : EConstr.t) : unit =
  if !opt_debug_simplification then
    (let old = !specialization_time in
    let now = Unix.times () in
    let pp_time = Pp.str "(" ++ Pp.real (now.Unix.tms_utime -. old.Unix.tms_utime) ++ Pp.str "[s])" in
    (match !prevterm with
    | None ->
        msg_debug_hov (Pp.str ("--" ^ step ^ "--> ") ++ pp_time ++ Pp.fnl () ++ (pr_deep (Printer.pr_econstr_env env sigma term)))
    | Some prev ->
        if exact_term_eq sigma prev term then
          msg_debug_hov (Pp.str ("--" ^ step ^ "--> term not changed ") ++ pp_time)
        else
          msg_debug_hov (Pp.str ("--" ^ step ^ "--> ") ++ pp_time ++ Pp.fnl () ++ (pr_deep (Printer.pr_econstr_env env sigma term))));
    prevterm := Some term;
    specialization_time := now)

    (*
let combine_equality_proofs (env : Environ.env) (sigma : Evd.evar_map) (term1 : EConstr.t) (term2 : EConstr.t) (proofs : (EConstr.t * EConstr.t * EConstr.t) list) : EConstr.t * EConstr.types =
  let eq = lib_ref "core.eq.type" in
  let eq_ind = lib_ref "core.eq.ind" in
  let eq_refl = lib_ref "core.eq.refl" in
  let ty = Retyping.get_type_of env sigma term1 in
  let eq_prop = mkApp (eq, [| ty; term1; term2 |]) in
  let p = mkLambda (Context.anonR, ty, (mkApp (eq, [| ty; term1; mkRel 1 |]))) in
  let rec aux proofs =
    match proofs with
    | [] ->
        mkApp (eq_refl, [| ty; term1 |])
    | [(first_lhs, first_rhs, first_proof)] ->
        first_proof
    | (last_lhs, last_rhs, last_proof) :: rest_proofs ->
        mkApp (eq_ind, [| ty; last_lhs; p; aux rest_proofs; last_rhs; last_proof |])
  in
  (aux proofs, eq_prop)
  *)

let codegen_simplify (cfunc : string) : Environ.env * Constant.t * StringSet.t =
  init_debug_simplification ();
  let (sp_cfg, sp_inst) =
    match CString.Map.find_opt cfunc !cfunc_instance_map with
    | None ->
        user_err (Pp.str "[codegen] specialization instance not defined:" +++
                  Pp.str (escape_as_coq_string cfunc))
    | Some (CodeGenCfuncPrimitive _) ->
        user_err (Pp.str "[codegen] not a target of simplification:" +++
                  Pp.str (escape_as_coq_string cfunc))
    | Some (CodeGenCfuncGenerate (sp_cfg, sp_inst)) -> (sp_cfg, sp_inst)
  in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let s_id = (match sp_inst.sp_simplified_status with
    | SpNoSimplification -> user_err (Pp.str "[codegen] not a target of simplification:" +++ Pp.str cfunc)
    | SpExpectedId s_id -> s_id
    | SpDefined _ -> user_err (Pp.str "[codegen] already simplified:" +++ Pp.str cfunc))
  in
  let presimp = sp_inst.sp_presimp in
  let epresimp = EConstr.of_constr presimp in
  let ctnt =
    match Constr.kind sp_cfg.sp_func with
    | Const (ctnt,_) -> ctnt
    | Construct _ -> user_err (Pp.str "[codegen] constructor is not simplifiable")
    | _ -> user_err (Pp.str "[codegen] non-constant and non-constructor simplification")
  in
  msg_info_hov (Pp.str "[codegen]" +++
    Pp.str "[cfunc:" ++ Pp.str cfunc ++ Pp.str "]" +++
    Pp.str "Start simplification:" +++ Id.print s_id);
  let inline_pred =
    let pred_func = Cpred.singleton ctnt in
    let global_pred = !specialize_global_inline in
    let local_pred = (match Cmap.find_opt ctnt !specialize_local_inline with
                     | None -> Cpred.empty
                     | Some pred -> pred) in
    Cpred.union (Cpred.union pred_func global_pred) local_pred
  in
  debug_simplification env sigma "pre-simplified" epresimp;
  let term = inline env sigma inline_pred epresimp in
  debug_simplification env sigma "inline" term;
  let () = check_letin_in_cstr_type env sigma term in
  (*let term = strip_cast env sigma term in*)
  let term = expand_eta_top env sigma term in
  debug_simplification env sigma "expand_eta_top" term;
  let term = normalizeV env sigma term in
  debug_simplification env sigma "normalizeV" term;
  let rec repeat_reduction sigma term =
    let term1 = term in
    let term = reduce_exp env sigma term in
    debug_simplification env sigma "reduce_exp" term;
    let (sigma, term) = Matchapp.simplify_matchapp env sigma term in
    debug_simplification env sigma "simplify_matchapp" term;
    if EConstr.eq_constr sigma term1 term then
      term
    else
      repeat_reduction sigma term
  in
  let term = repeat_reduction sigma term in
  let term = normalize_types env sigma term in
  debug_simplification env sigma "normalize_types" term;
  let term = normalize_static_arguments env sigma term in
  debug_simplification env sigma "normalize_static_arguments" term;
  let term = delete_unused_let env sigma term in
  debug_simplification env sigma "delete_unused_let" term;
  let (env, term, referred_cfuncs) = replace ~cfunc env sigma term in (* "replace" modifies global env *)
  debug_simplification env sigma "replace" term;
  let term = reduce_eta env sigma term in
  debug_simplification env sigma "reduce_eta" term;
  let term = complete_args env sigma term in
  debug_simplification env sigma "complete_args" term;
  monomorphism_check env sigma term;
  Linear.borrowcheck env sigma term;
  Linear.downwardcheck env sigma cfunc term;
  let term = rename_vars env sigma term in
  debug_simplification env sigma "rename_vars" term;
  let declared_ctnt =
    let globref = Declare.declare_definition
      ~info:(Declare.Info.make ())
      ~cinfo:(Declare.CInfo.make ~name:s_id ~typ:None ())
      ~opaque:false
      ~body:term
      sigma
    in
    Globnames.destConstRef globref
  in
  let env = Global.env () in
  let sp_inst2 = {
    sp_presimp = sp_inst.sp_presimp;
    sp_static_arguments = sp_inst.sp_static_arguments;
    sp_presimp_constr = sp_inst.sp_presimp_constr;
    sp_simplified_status = SpDefined (declared_ctnt, referred_cfuncs);
    sp_cfunc_name = sp_inst.sp_cfunc_name;
    sp_icommand = sp_inst.sp_icommand; }
  in
  msg_info_hov (Pp.str "[codegen]" +++
    Pp.str "[cfunc:" ++ Pp.str cfunc ++ Pp.str "]" +++
    Pp.str "Simplified function defined:" +++ Printer.pr_constant env declared_ctnt);
  (let m = !gallina_instance_map in
    let m = ConstrMap.set sp_inst.sp_presimp_constr (sp_cfg, sp_inst2) m in
    let m = ConstrMap.set presimp (sp_cfg, sp_inst2) m in
    let m = ConstrMap.add (Constr.mkConst declared_ctnt) (sp_cfg, sp_inst2) m in
    gallina_instance_map := m);
  (let m = !cfunc_instance_map in
    let m = CString.Map.set sp_inst.sp_cfunc_name (CodeGenCfuncGenerate (sp_cfg, sp_inst2)) m in
    cfunc_instance_map := m);
  (let inst_map = ConstrMap.add presimp sp_inst2 sp_cfg.sp_instance_map in
   let sp_cfg2 = { sp_cfg with sp_instance_map = inst_map } in
   let m = !specialize_config_map in
   specialize_config_map := ConstrMap.add sp_cfg.sp_func sp_cfg2 m);
  (*msg_debug_hov (Pp.str "[codegen:codegen_simplify] declared_ctnt=" ++ Printer.pr_constant env declared_ctnt);*)
  (env, declared_ctnt, referred_cfuncs)

let command_simplify_function (cfuncs : string list) : unit =
  List.iter
    (fun cfunc_name ->
      ignore (codegen_simplify cfunc_name))
    cfuncs

let rec recursive_simplify (visited : StringSet.t ref) (rev_postorder : string list ref) (cfunc : string) : unit =
  if StringSet.mem cfunc !visited then
    ()
  else
    (visited := StringSet.add cfunc !visited;
    match CString.Map.find_opt cfunc !cfunc_instance_map with
    | None -> user_err (Pp.str "[codegen] unknown C function:" +++ Pp.str cfunc)
    | Some (CodeGenCfuncGenerate (sp_cfg, sp_inst)) ->
        (match sp_inst.sp_simplified_status with
        | SpNoSimplification -> ()
        | SpExpectedId _ ->
            let (_, _, referred_cfuncs) = codegen_simplify cfunc in
            (StringSet.iter (recursive_simplify visited rev_postorder) referred_cfuncs);
            rev_postorder := cfunc :: !rev_postorder
        | SpDefined (declared_ctnt, referred_cfuncs) ->
            (StringSet.iter (recursive_simplify visited rev_postorder) referred_cfuncs);
            rev_postorder := cfunc :: !rev_postorder)
    | Some (CodeGenCfuncPrimitive _) -> ())

let command_simplify_dependencies (cfuncs : string list) : unit =
  let visited = ref StringSet.empty in
  StringSet.iter
    (fun cfunc ->
      let rev_postorder = ref [] in
      recursive_simplify visited rev_postorder cfunc;
      msg_info_hov (Pp.str "[codegen] postorder from" +++
        Pp.str cfunc ++ Pp.str ":" +++
        pp_sjoinmap_list Pp.str (List.rev_append !rev_postorder [])))
    (StringSet.of_list cfuncs)

let codegen_resolve_dependencies (gen_list : code_generation list) : code_generation list =
  let visited = ref StringSet.empty in
  List.fold_right
    (fun gen new_genlist ->
      match gen with
      | GenSnippet snippet ->
          gen :: new_genlist
      | GenPrototype cfunc ->
          gen :: new_genlist
      | GenFunc cfunc ->
          let rev_postorder = ref [] in
          recursive_simplify visited rev_postorder cfunc;
          list_map_append (fun cfunc -> GenFunc cfunc) !rev_postorder new_genlist
      | GenMutual cfuncs ->
          match cfuncs with
          | [] -> new_genlist
          | cfunc1 :: rest ->
              let rev_postorder = ref [] in
              recursive_simplify visited rev_postorder cfunc1;
              list_map_append
                (fun cfunc2 ->
                  if cfunc1 = cfunc2 then
                    gen (* GenMutual cfunc1 :: rest *)
                  else
                    GenFunc cfunc2)
                !rev_postorder new_genlist)
    gen_list
    []

let command_resolve_dependencies () : unit =
  generation_map :=
    CString.Map.map codegen_resolve_dependencies !generation_map

let command_print_generation_list gen_list =
  List.iter
    (fun gen ->
      match gen with
      | GenSnippet snippet ->
          msg_info_hov (Pp.str "GenSnippet" +++ Pp.str (escape_as_coq_string snippet))
      | GenPrototype cfunc ->
          msg_info_hov (Pp.str "GenPrototype" +++ Pp.str cfunc)
      | GenFunc cfunc ->
          msg_info_hov (Pp.str "GenFunc" +++ Pp.str cfunc)
      | GenMutual cfuncs ->
          msg_info_hov (Pp.str "GenMutual" +++ pp_sjoinmap_list Pp.str cfuncs))
    (List.rev_append gen_list [])

let command_print_generation_map () =
  (match !current_header_filename with
  | None -> msg_info_hov (Pp.str "current_header_filename = None")
  | Some fn -> msg_info_hov (Pp.str "current_header_filename =" +++ Pp.str (escape_as_coq_string fn)));
  (match !current_source_filename with
  | None -> msg_info_hov (Pp.str "current_source_filename = None")
  | Some fn -> msg_info_hov (Pp.str "current_source_filename =" +++ Pp.str (escape_as_coq_string fn)));
  CString.Map.iter
    (fun filename gen_list ->
      msg_info_hov (Pp.str filename);
      command_print_generation_list gen_list)
    !generation_map

let command_deallocator (func : Libnames.qualid) (user_args : Constrexpr.constr_expr list) (cfunc : string) : unit =
  let open Declarations in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let gref = Smartlocate.global_with_alias func in
  let (mutind,func) =
    match gref with
    | IndRef ind ->
        let (mutind,_) = ind in
        (mutind, Constr.mkInd ind)
    | ConstructRef cstr ->
        let ((mutind,_),_) = cstr in
        (mutind, Constr.mkConstruct cstr)
    | _ -> user_err (Pp.str "[codegen] inductive or constructor expected:" +++ Printer.pr_global gref)
  in
  let mind_body = Environ.lookup_mind mutind env in
  (if mind_body.mind_nparams <> List.length user_args then
    user_err (Pp.str "[codegen] unexpected number of inductive type parameters:" +++
      Pp.int mind_body.mind_nparams +++ Pp.str "expected but" +++
      Pp.int (List.length user_args) +++ Pp.str "given for" +++
      Printer.pr_constr_env env sigma func));
  let func_type = Retyping.get_type_of env sigma (EConstr.of_constr func) in
  let func_istypearg_list = determine_type_arguments env sigma func_type in
  let func_istypearg_list = CList.firstn (List.length user_args) func_istypearg_list in
  let (sigma, args) = interp_args env sigma func_istypearg_list user_args in
  let args = List.map (Reductionops.nf_all env sigma) args in
  let args = List.map (Evarutil.flush_and_check_evars sigma) args in
  let t = Constr.mkApp (func, Array.of_list args) in
  (*msg_debug_hov (Pp.str "[codegen] command_deallocator_type:" +++ Printer.pr_econstr_env env sigma t);*)
  deallocator_cfunc_map := ConstrMap.add t cfunc !deallocator_cfunc_map
