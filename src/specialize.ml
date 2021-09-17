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
open Pp

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
  | CodeGenFunction -> true
  | CodeGenStaticFunction -> true
  | CodeGenPrimitive -> false
  | CodeGenConstant -> false

let string_of_icommand (icommand : instance_command) : string =
  match icommand with
  | CodeGenFunction -> "Function"
  | CodeGenStaticFunction -> "Static Function"
  | CodeGenPrimitive -> "Primitive"
  | CodeGenConstant -> "Constant"

let pr_constant_or_constructor (env : Environ.env) (func : Constr.t) : Pp.t =
  match Constr.kind func with
  | Const (ctnt, _) -> Printer.pr_constant env ctnt
  | Construct (cstr, _) -> Printer.pr_constructor env cstr
  | _ -> user_err (Pp.str "[codegen] expect constant or constructor")

let pr_codegen_arguments (env : Environ.env) (sigma : Evd.evar_map) (sp_cfg : specialization_config) : Pp.t =
  Pp.str "CodeGen Arguments" +++
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

let determine_sd_list (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : s_or_d list =
  List.map
    (function true -> SorD_S | false -> SorD_D)
    (determine_type_arguments env sigma ty)

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
  (sigma, t, ty)

let gensym_ps (suffix : string) : Names.Id.t * Names.Id.t =
  let n = !gensym_ps_num in
  gensym_ps_num := n + 1;
  let suffix2 = if suffix = "" then suffix else "_" ^ suffix in
  let p = "codegen_p" ^ string_of_int n ^ suffix2 in
  let s = "codegen_s" ^ string_of_int n ^ suffix2 in
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
      not (isInd sigma (fst (decompose_app sigma presimp_type))) then
    user_err (Pp.str "[codegen] CodeGen Constant needs a constant:" +++
      Printer.pr_constr_env env sigma presimp +++ str ":" +++
      Printer.pr_econstr_env env sigma presimp_type));
  (if ConstrMap.mem presimp sp_cfg.sp_instance_map then
    user_err (Pp.str "[codegen] specialization instance already configured:" +++ Printer.pr_constr_env env sigma presimp));
  let sp_inst =
    let check_cfunc_name_conflict cfunc_name =
      match CString.Map.find_opt cfunc_name !cfunc_instance_map with
      | None -> ()
      | Some (sp_cfg, sp_inst) ->
          user_err
            (Pp.str "[codegen] C function name already used:" +++
            Pp.str cfunc_name +++
            Pp.str "for" +++
            Printer.pr_constr_env env sigma sp_inst.sp_presimp +++
            Pp.str "but also for" +++
            Printer.pr_constr_env env sigma presimp)
    in
    let generated_ps_syms = ref None in
    let lazy_gensym_ps suffix =
      match !generated_ps_syms with
      | Some ps_ids -> ps_ids
      | None ->
          let ps_ids = gensym_ps suffix in
          generated_ps_syms := Some ps_ids;
          ps_ids
    in
    let lazy_gensym_p suffix = fst (lazy_gensym_ps suffix) in
    let lazy_gensym_s suffix = snd (lazy_gensym_ps suffix) in
    let need_presimplified_ctnt =
      List.exists (fun sd -> sd = SorD_S) sp_cfg.sp_sd_list ||
      (match names_opt with Some { spi_presimp_id = Some _ } -> true | _ -> false)
    in
    let func_name = label_name_of_constant_or_constructor func in
    let s_id () = match names_opt with
      | Some { spi_simplified_id = Some s_id } -> s_id
      | _ -> lazy_gensym_s func_name
    in
    let p_id () = match names_opt with
      | Some { spi_presimp_id = Some p_id } -> p_id
      | _ -> lazy_gensym_p func_name
    in
    let cfunc_name = match names_opt with
      | Some { spi_cfunc_name = Some name } ->
          (* We accept C's non-idetifier, such as "0" here. *)
          name
      | _ ->
          if not need_presimplified_ctnt then
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
  cfunc_instance_map := (CString.Map.add cfunc_name (sp_cfg, sp_inst) !cfunc_instance_map);
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
  let (env, sp_inst) = codegen_instance_command CodeGenFunction func user_args names in
  codegen_add_header_generation (GenPrototype sp_inst.sp_cfunc_name);
  codegen_add_source_generation (GenFunc sp_inst.sp_cfunc_name)

let command_static_function
    (func : Libnames.qualid)
    (user_args : Constrexpr.constr_expr option list)
    (names : sp_instance_names) : unit =
  let (env, sp_inst) = codegen_instance_command CodeGenStaticFunction func user_args names in
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

let check_convertible (phase : string) (env : Environ.env) (sigma : Evd.evar_map) (t1 : EConstr.t) (t2 : EConstr.t) : unit =
  if Reductionops.is_conv env sigma t1 t2 then
    ()
  else
    user_err (Pp.str "[codegen] translation inconvertible:" +++ Pp.str phase ++
      Pp.fnl () ++
      Printer.pr_econstr_env env sigma t1 ++ Pp.fnl () ++
      Pp.str "=/=>" ++ Pp.fnl () ++
      Printer.pr_econstr_env env sigma t2)

let command_global_inline (func_qualids : Libnames.qualid list) : unit =
  let env = Global.env () in
  let funcs = List.map (func_of_qualid env) func_qualids in
  let ctnts = List.filter_map (fun func -> match Constr.kind func with Const (ctnt, _) -> Some ctnt | _ -> None) funcs in
  let f pred ctnt = Cpred.add ctnt pred in
  specialize_global_inline := List.fold_left f !specialize_global_inline ctnts

let command_local_inline (func_qualid : Libnames.qualid) (func_qualids : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let func = func_of_qualid env func_qualid in
  let ctnt =
    match Constr.kind func with
    | Const (ctnt, _) -> ctnt
    | _ -> user_err (Pp.str "[codegen] constant expected:" +++ Printer.pr_constr_env env sigma func)
  in
  let funcs = List.map (func_of_qualid env) func_qualids in
  let ctnts = List.filter_map (fun func -> match Constr.kind func with Const (ctnt, _) -> Some ctnt | _ -> None) funcs in
  let local_inline = !specialize_local_inline in
  let pred = match Cmap.find_opt ctnt local_inline with
             | None -> Cpred.empty
             | Some pred -> pred in
  let f pred ctnt = Cpred.add ctnt pred in
  let pred' = List.fold_left f pred ctnts in
  specialize_local_inline := Cmap.add ctnt pred' local_inline

let inline1 (env : Environ.env) (sigma : Evd.evar_map) (pred : Cpred.t) (term : EConstr.t) : EConstr.t =
  let trans = {
    TransparentState.tr_var = Id.Pred.empty;
    TransparentState.tr_cst = pred
  } in
  let reds = CClosure.RedFlags.red_add_transparent CClosure.RedFlags.no_red trans in
  let term = Reductionops.clos_norm_flags reds env sigma term in
  term

let inline (env : Environ.env) (sigma : Evd.evar_map) (pred : Cpred.t) (term : EConstr.t) : EConstr.t =
  let result = inline1 env sigma pred term in
  check_convertible "inline" env sigma term result;
  result

(* useless ?
let rec strip_cast (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (* msg_info_hov (Pp.str "strip_cast arg: " ++ Printer.pr_econstr_env env sigma term); *)
  let result = strip_cast1 env sigma term in
  (* msg_info_hov (Pp.str "strip_cast ret: " ++ Printer.pr_econstr_env env sigma result); *)
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
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (strip_cast env2 sigma) fary in
      mkFix ((ia, i), (nary, tary, fary'))
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
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let prec = (nameary, tyary, funary) in
      let env2 = push_rec_types prec env in
      let funary' = Array.map (expand_eta_top env2 sigma) funary in
      mkFix ((ia, i), (nameary, tyary, funary'))
  | _ ->
      let ty = Retyping.get_type_of env sigma term in
      let ty = Reductionops.nf_all env sigma ty in
      match EConstr.kind sigma ty with
      | Prod _ ->
          let (args, result_type) = decompose_prod sigma ty in
          (* (Name.t Context.binder_annot * t) list * t *)
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
          let term' = Vars.lift n term in
          compose_lam args' (mkApp (term', Array.map mkRel (array_rev (iota_ary 1 n))))
      | _ ->
          search_fix_to_expand_eta env sigma term
and search_fix_to_expand_eta (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel _ | Const _ | Construct _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ -> term
  | Var _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Var:" +++ Printer.pr_econstr_env env sigma term)
  | Evar _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Evar:" +++ Printer.pr_econstr_env env sigma term)
  | Prod _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Prod:" +++ Printer.pr_econstr_env env sigma term)
  | CoFix _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected CoFix:" +++ Printer.pr_econstr_env env sigma term)
  | Array _ -> user_err (Pp.str "[codegen:normalize_static_arguments] unexpected Array:" +++ Printer.pr_econstr_env env sigma term)
  | Cast (e,ck,t) -> search_fix_to_expand_eta env sigma e (* strip cast *)
  | Lambda (x, t, b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let b' = search_fix_to_expand_eta env2 sigma b in
      mkLambda (x, t, b')
  | LetIn (x, e, t, b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let e' = search_fix_to_expand_eta env sigma e in
      let b' = search_fix_to_expand_eta env2 sigma b in
      mkLetIn (x, e', t, b')
  | Case (ci, p, iv, item, branches) ->
      let branches' = Array.map (search_fix_to_expand_eta env sigma) branches in
      mkCase (ci, p, iv, item, branches')
  | Proj (proj, e) ->
      let e' = search_fix_to_expand_eta env sigma e in
      mkProj (proj, e')
  | App (f, args) ->
      let f' = search_fix_to_expand_eta env sigma f in
      let args' = Array.map (search_fix_to_expand_eta env sigma) args in
      mkApp (f', args')
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (expand_eta_top env2 sigma) fary in
      mkFix ((ks, j), (nary, tary, fary'))

let rec normalizeV (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : EConstr.t =
  (if !opt_debug_normalizeV then
    msg_debug_hov (Pp.str "[codegen] normalizeV arg: " ++ Printer.pr_econstr_env env sigma term));
  let result = normalizeV1 env sigma term in
  (if !opt_debug_normalizeV then
    msg_debug_hov (Pp.str "[codegen] normalizeV ret: " ++ Printer.pr_econstr_env env sigma result));
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
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let prec = (nameary, tyary, funary) in
      let env2 = push_rec_types prec env in
      let funary' = Array.map (normalizeV env2 sigma) funary in
      mkFix ((ia, i), (nameary, tyary, funary'))
  | CoFix (i, (nameary, tyary, funary)) ->
      let prec = (nameary, tyary, funary) in
      let env2 = push_rec_types prec env in
      let funary' = Array.map (normalizeV env2 sigma) funary in
      mkCoFix (i, (nameary, tyary, funary'))
  | LetIn (x,e,ty,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, ty) in
      let env2 = EConstr.push_rel decl env in
      let e' = normalizeV env sigma e in
      let b' = normalizeV env2 sigma b in
      mkLetIn (x, e', ty, b')
  | Case (ci, p, iv, item, branches) ->
      if isRel sigma item then
        mkCase (ci, p, iv, item, Array.map (normalizeV env sigma) branches)
      else
        let term =
          mkCase (ci,
                  Vars.lift 1 p,
                  iv,
                  mkRel 1,
                  Array.map
                    (fun branch -> Vars.lift 1 (normalizeV env sigma branch))
                    branches)
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

let rec fv_range_rec (sigma : Evd.evar_map) (numlocal : int) (term : EConstr.t) : (int*int) option =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ | Array _
  | Const _ | Construct _ -> None
  | Rel i ->
      if numlocal < i then
        Some (i-numlocal,i-numlocal)
      else
        None
  | Evar (ev, es) ->
      fv_range_array sigma numlocal (Array.of_list es)
  | Proj (proj, e) ->
      fv_range_rec sigma numlocal e
  | Cast (e,ck,t) ->
      merge_range
        (fv_range_rec sigma numlocal e)
        (fv_range_rec sigma numlocal t)
  | App (f, args) ->
      merge_range
        (fv_range_rec sigma numlocal f)
        (fv_range_array sigma numlocal args)
  | LetIn (x,e,t,b) ->
      merge_range3
        (fv_range_rec sigma numlocal e)
        (fv_range_rec sigma numlocal t)
        (fv_range_rec sigma (numlocal+1) b)
  | Case (ci, p, iv, item, branches) ->
      merge_range3
        (fv_range_rec sigma numlocal p)
        (fv_range_rec sigma numlocal item)
        (fv_range_array sigma numlocal branches)
  | Prod (x,t,b) ->
      merge_range
        (fv_range_rec sigma numlocal t)
        (fv_range_rec sigma (numlocal+1) b)
  | Lambda (x,t,b) ->
      merge_range
        (fv_range_rec sigma numlocal t)
        (fv_range_rec sigma (numlocal+1) b)
  | Fix ((ia, i), (nary, tary, fary)) ->
      merge_range
        (fv_range_array sigma numlocal tary)
        (fv_range_array sigma (numlocal + Array.length fary) fary)
  | CoFix (i, (nary, tary, fary)) ->
      merge_range
        (fv_range_array sigma numlocal tary)
        (fv_range_array sigma (numlocal + Array.length fary) fary)
and fv_range_array (sigma : Evd.evar_map) (numlocal : int) (terms : EConstr.t array) : (int*int) option =
  Array.fold_left
    (fun acc term -> merge_range acc (fv_range_rec sigma numlocal term))
    None terms

let fv_range (sigma : Evd.evar_map) (term : EConstr.t) : (int*int) option =
  fv_range_rec sigma 0 term

let test_bounded_fix (env : Environ.env) (sigma : Evd.evar_map) (k : int)
    (lift : int -> EConstr.t -> EConstr.t) (ia : int array)
    (prec : Name.t Context.binder_annot array * EConstr.types array * EConstr.t array) =
  (*msg_info_hov (Pp.str "test_bounded_fix: k=" ++ Pp.int k +++
    Printer.pr_econstr_env env sigma (mkFix ((ia,0),prec)));*)
  let n = Array.length ia in
  let vals_opt =
    let rec loop j acc =
      if n <= j then
        Some acc
      else
        match EConstr.lookup_rel (k + j) env with
        | Context.Rel.Declaration.LocalAssum _ -> None
        | Context.Rel.Declaration.LocalDef (_,e,_) ->
            match EConstr.kind sigma e with
            | Fix ((ia', i'), prec') ->
                if i' = n - j - 1 then
                  loop (j+1) (e :: acc)
                else
                  None
            | _ -> None

    in
    loop 0 []
  in
  match vals_opt with
  | None -> false
  | Some vals ->
      CList.for_all_i
        (fun i e -> EConstr.eq_constr sigma e
          (lift (-(k+n-1-i)) (mkFix ((ia, i), prec))))
        0 vals

(* This function returns (Some i) where i is the de Bruijn index that
    env[i] is (mkFix ((ia,0),prec)),
    env[i-1] is (mkFix ((ia,1),prec)), ...
    env[i-n+1] is (mkFix ((ia,n-1),prec))
  where n is the nubmer of the mutually recursive functions (i.e. the length of ia).

  None is returned otherwise.
  *)
let find_bounded_fix (env : Environ.env) (sigma : Evd.evar_map) (ia : int array)
    (prec : Name.t Context.binder_annot array * EConstr.types array * EConstr.t array) :
    int option =
      (*msg_info_hov (Pp.str "[codegen] find_bounded_fix:" +++
        Printer.pr_econstr_env env sigma (mkFix ((ia,0),prec)));*)
  let (nary, tary, fary) = prec in
  let n = Array.length fary in
  let nb_rel = Environ.nb_rel env in
  match fv_range sigma (mkFix ((ia,0),prec)) with
  | None ->
      (*msg_info_hov (Pp.str "[codegen] find_bounded_fix: fv_range=None");*)
      let lift _ term = term in
      let rec loop k =
        if nb_rel < k + n - 1 then
          None
        else
          if test_bounded_fix env sigma k lift ia prec then
            Some (k + n - 1)
          else
            loop (k+1)
      in
      loop 1
  | Some (fv_min, fv_max) ->
      (*msg_info_hov (Pp.str "[codegen] find_bounded_fix: fv_range=Some (" ++ Pp.int fv_min ++ Pp.str "," ++ Pp.int fv_max ++ Pp.str ")");*)
      let lift = Vars.lift in
      let rec loop k =
        if fv_min <= k + n - 1 then
          None
        else
          if test_bounded_fix env sigma k lift ia prec then
            Some (k + n - 1)
          else
            loop (k+1)
      in
      loop 1

(* assumption: ty is a type (not a function that returns a type) *)
let is_ind_type (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  let ty = Reductionops.whd_all env sigma ty in
  match EConstr.kind sigma ty with
  | Ind _ -> true
  | App (f, args) -> isInd sigma f
  | _ -> false

let try_iota_match (env : Environ.env) (sigma : Evd.evar_map)
    (ci : case_info) (p : EConstr.t) (iv : (EConstr.t, EInstance.t) case_invert)
    (item : EConstr.t) (branches : EConstr.t array)
    (success : Environ.env -> EConstr.t -> EConstr.t -> EConstr.t array -> 'a) (failure : unit -> 'result) =
  let i = destRel sigma item in
  (match EConstr.lookup_rel i env with
  | Context.Rel.Declaration.LocalAssum _ -> failure ()
  | Context.Rel.Declaration.LocalDef (x,e,t) ->
      let (f, args) = decompose_app sigma e in
      (match EConstr.kind sigma f with
      | Construct ((ind, j), _) ->
          (* reduction: iota-match *)
          let branch = branches.(j-1) in
          let args = (Array.of_list (CList.skipn ci.ci_npar args)) in
          let args = Array.map (Vars.lift i) args in
          let item_env = Environ.pop_rel_context i env in
          success item_env e branch args
      | _ -> failure ()))

(* invariant: letin-bindings in env is reduced form *)
let rec reduce_exp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  let t1 = Unix.times () in
  (if !opt_debug_reduce_exp then (* Set Debug CodeGen ReduceExp. *)
    msg_debug_hov (Pp.str "[codegen] reduce_exp arg: " ++ Printer.pr_econstr_env env sigma term));
  let result = reduce_exp1 env sigma term in
  (if !opt_debug_reduce_exp then
    let t2 = Unix.times () in
    msg_debug_hov (Pp.str "[codegen] reduce_exp ret (" ++ Pp.real (t2.Unix.tms_utime -. t1.Unix.tms_utime) ++ Pp.str "): " ++ Printer.pr_econstr_env env sigma result));
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
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      mkLambda (x, t, reduce_exp env2 sigma e)
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
  | Case (ci,p,iv,item,branches) ->
      let item' = reduce_arg env sigma item in
      try_iota_match env sigma ci p iv item' branches
        (fun item_env item_content branch args ->
          let term2 = mkApp (branch, args) in
          debug_reduction "iota-match" (fun () ->
            let term1 = mkCase (ci, p, iv, item', branches) in
            Pp.str "match-item = " ++
            Printer.pr_econstr_env env sigma item ++ Pp.str " = " ++
            Printer.pr_econstr_env item_env sigma item_content ++ Pp.fnl () ++
            Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
            Pp.str "->" ++ Pp.fnl () ++
            Printer.pr_econstr_env env sigma term2);
          check_convertible "reduction(iota-match)" env sigma term term2;
          reduce_exp env sigma term2)
        (fun () -> mkCase (ci, p, iv, item', Array.map (reduce_exp env sigma) branches))
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
          let (f, args) = decompose_app sigma e in
          (match EConstr.kind sigma f with
          | Construct _ ->
              (* reduction: iota-proj *)
              let term2 = List.nth args (Projection.npars pr + Projection.arg pr) in
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
  | Fix ((ia,i), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      mkFix ((ia, i), (nary, tary, Array.map (reduce_exp env2 sigma) fary))
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
    msg_debug_hov (Pp.str "[codegen] reduce_app arg: " ++ Printer.pr_econstr_env env sigma term));
  let result = reduce_app1 env sigma f args_nf in
  (if !opt_debug_reduce_app then
    let t2 = Unix.times () in
    msg_debug_hov (Pp.str "[codegen] reduce_app ret (" ++ Pp.real (t2.Unix.tms_utime -. t1.Unix.tms_utime) ++ Pp.str "): " ++ Printer.pr_econstr_env env sigma result));
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
        let (f_f, f_args) = decompose_app sigma e in
        match EConstr.kind sigma f_f with
        | Rel _ | Const _ | Construct _ | Lambda _ | Fix _ ->
            (* reduction: delta-fun *)
            reduce_app env sigma
              (Vars.lift m f_f)
              (Array.append (CArray.map_of_list (Vars.lift m) f_args) args_nf)
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
      if isLambda sigma b || isFix sigma b ||
         let app_ty = Retyping.get_type_of env sigma (mkApp (f, args_nf)) in
         is_ind_type env sigma app_ty then
        (* reduction: beta-var *)
        (* We apply beta reduction only for the first argument.
           We don't Reductionops.beta_applist sigma (f, (Array.to_list args_nf))
           because it apply beta reduction multiply when f is nested lambda. *)
        (let first_arg = args_nf.(0) in
         let rest_args = Array.sub args_nf 1 (Array.length args_nf - 1) in
         let term2 = mkApp (Vars.subst1 first_arg b, rest_args) in
        debug_reduction "beta-var" (fun () ->
          Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
          Pp.str "->" ++ Pp.fnl () ++
          Printer.pr_econstr_env env sigma term2);
        check_convertible "reduction(beta-var)" env sigma term1 term2;
        reduce_exp env sigma term2)
      else
        default ()
  | App (f_f, f_args) ->
      (* reduction: delta-app *)
      let f_args_nf = Array.map (reduce_arg env sigma) f_args in
      reduce_app env sigma f_f (Array.append f_args_nf args_nf)
  | LetIn (x,e,t,b) ->
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
  | Case (ci,p,iv,item,branches) ->
      let item' = reduce_arg env sigma item in
      try_iota_match env sigma ci p iv item' branches
        (fun item_env item_content branch args ->
          let term2 = mkApp (branch, args) in
          debug_reduction "iota-match" (fun () ->
            let term1 = mkCase (ci, p, iv, item', branches) in
            Pp.str "match-item = " ++
            Printer.pr_econstr_env env sigma item ++ Pp.str " = " ++
            Printer.pr_econstr_env item_env sigma item_content ++ Pp.fnl () ++
            Printer.pr_econstr_env env sigma term1 ++ Pp.fnl () ++
            Pp.str "->" ++ Pp.fnl () ++
            Printer.pr_econstr_env env sigma term2);
          check_convertible "reduction(iota-match)" env sigma f term2;
          reduce_app env sigma branch (Array.append args args_nf))
        (fun () -> mkApp (mkCase (ci, p, iv, item', Array.map (reduce_exp env sigma) branches), args_nf))
  | Fix ((ia,i), ((nary, tary, fary) as prec)) ->
      if ia.(i) < Array.length args_nf then
        let decarg_var = args_nf.(ia.(i)) in
        let decarg_decl = EConstr.lookup_rel (destRel sigma decarg_var) env in
        (match decarg_decl with
        | Context.Rel.Declaration.LocalAssum _ -> default ()
        | Context.Rel.Declaration.LocalDef (_,decarg_val,_) ->
            let (decarg_f, decarg_args) = decompose_app sigma decarg_val in
            if isConstruct sigma decarg_f then
              let n = Array.length fary in
              let fi = fary.(i) in
              match find_bounded_fix env sigma ia prec with
              | Some bounded_fix ->
                  (* reduction: iota-fix' *)
                  (*msg_info_hov (Pp.str "[codegen] bounded_fix: " ++ Printer.pr_rel_decl (Environ.pop_rel_context bounded_fix env) sigma (Environ.lookup_rel bounded_fix env));*)
                  let fi_subst = Vars.substl (List.map (fun j -> mkRel j) (iota_list (bounded_fix-n+1) n)) fi in
                  let term2 = mkApp (fi_subst, args_nf) in
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
                  reduce_app env sigma fi_subst args_nf
              | None ->
                  (* reduction: iota-fix *)
                  let args_nf_lifted = Array.map (Vars.lift n) args_nf in
                  let (_, defs) = CArray.fold_left2_map
                    (fun j x t -> (j+1, (x, Vars.lift j (mkFix ((ia,j), prec)), Vars.lift j t)))
                    0 nary tary
                  in
                  let defs = Array.to_list (array_rev defs) in
                  let term2 = compose_lets defs (mkApp (fi, args_nf_lifted)) in
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
                  let b = reduce_app env2 sigma fi args_nf_lifted in
                  compose_lets defs b
            else
              default ())
      else
        default ()
  | _ -> default ()

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
  | Case (ci, p, iv, item, branches) ->
      let p' = Reductionops.nf_all env sigma p in
      let item' = normalize_types env sigma item in
      let branches' = Array.map (normalize_types env sigma) branches in
      mkCase (ci, p', iv, item', branches')
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
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (normalize_static_arguments env2 sigma) fary in
      mkFix ((ia, i), (nary, tary, fary'))
  | LetIn (x, e, t, b) ->
      let e' = normalize_static_arguments env sigma e in
      let decl = Context.Rel.Declaration.LocalDef (x, e', t) in
      let env2 = EConstr.push_rel decl env in
      let b' = normalize_static_arguments env2 sigma b in
      mkLetIn (x, e', t, b')
  | Case (ci, p, iv, item, branches) ->
      let branches' = Array.map (normalize_static_arguments env sigma) branches in
      mkCase (ci, p, iv, item, branches')
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

let rec delete_unused_let_rec (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (IntSet.t * (bool list -> EConstr.t)) =
  (if !opt_debug_delete_let then
    msg_debug_hov (Pp.str "[codegen] delete_unused_let_rec arg: " ++ Printer.pr_econstr_env env sigma term));
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
        let fvs = IntSet.union (IntSet.remove (Environ.nb_rel env) fvsb) (IntSet.union fvse fvst) in
        (fvs, fun vars_used -> mkLetIn (x, fe vars_used, ft vars_used, fb (true :: vars_used)))
      else
        (* reduction: zeta-del *)
        (fvsb, fun vars_used -> fb (false :: vars_used))
  | Case (ci, p, iv, item, branches) ->
      let (fvsp, fp) = delete_unused_let_rec env sigma p in
      let (fvsitem, fitem) = delete_unused_let_rec env sigma item in
      let fbranches2 = Array.map (delete_unused_let_rec env sigma) branches in
      let fbranches = Array.map snd fbranches2 in
      let fvsbrances = Array.fold_left IntSet.union IntSet.empty (Array.map fst fbranches2) in
      let fvs = IntSet.union fvsp (IntSet.union fvsitem fvsbrances) in
      (fvs, fun vars_used -> mkCase (ci, fp vars_used, iv, fitem vars_used, Array.map (fun g -> g vars_used) fbranches))
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
  | Fix ((ia, i), ((nameary, tyary, funary) as prec)) ->
      let h = Array.length funary in
      let env2 = push_rec_types prec env in
      let ftyary2 = Array.map (delete_unused_let_rec env sigma) tyary in
      let ftyary = Array.map snd ftyary2 in
      let fvst = Array.fold_left IntSet.union IntSet.empty (Array.map fst ftyary2) in
      let ffunary2 = Array.map (delete_unused_let_rec env2 sigma) funary in
      let ffunary = Array.map snd ffunary2 in
      let fvsf = Array.fold_left IntSet.union IntSet.empty (Array.map fst ffunary2) in
      let fvs =
        let n = Environ.nb_rel env in
        IntSet.union fvst (IntSet.filter (fun i -> i < n) fvsf)
      in
      (fvs,
       fun vars_used ->
         let vars_used' = CList.addn h true vars_used in
         mkFix ((ia, i),
                (nameary,
                 Array.map (fun g -> g vars_used) ftyary,
                 Array.map (fun g -> g vars_used') ffunary)))
  | CoFix (i, ((nameary, tyary, funary) as prec)) ->
      let h = Array.length funary in
      let env2 = push_rec_types prec env in
      let ftyary2 = Array.map (delete_unused_let_rec env sigma) tyary in
      let ftyary = Array.map snd ftyary2 in
      let fvst = Array.fold_left IntSet.union IntSet.empty (Array.map fst ftyary2) in
      let ffunary2 = Array.map (delete_unused_let_rec env2 sigma) funary in
      let ffunary = Array.map snd ffunary2 in
      let fvsf = Array.fold_left IntSet.union IntSet.empty (Array.map fst ffunary2) in
      let fvs =
        let n = Environ.nb_rel env in
        IntSet.union fvst (IntSet.filter (fun i -> i < n) fvsf)
      in
      (fvs,
       fun vars_used ->
        let vars_used' = CList.addn h true vars_used in
        mkCoFix (i,
                 (nameary,
                  Array.map (fun g -> g vars_used) ftyary,
                  Array.map (fun g -> g vars_used') ffunary)))

let delete_unused_let (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (if !opt_debug_delete_let then
    msg_debug_hov (Pp.str "[codegen] delete_unused_let arg: " ++ Printer.pr_econstr_env env sigma term));
  assert (Environ.nb_rel env = 0);
  let (fvs, f) = delete_unused_let_rec env sigma term in
  let result = f [] in
  (if !opt_debug_delete_let then
    msg_debug_hov (Pp.str "[codegen] delete_unused_let ret: " ++ Printer.pr_econstr_env env sigma result));
  check_convertible "specialize" env sigma term result;
  result

let rec first_fv_rec (sigma : Evd.evar_map) (numrels : int) (term : EConstr.t) : int option =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ | Array _
  | Const _ | Construct _ -> None
  | Rel i -> if numrels < i then Some i else None
  | Evar (ev, es) ->
      array_option_exists (first_fv_rec sigma numrels) (Array.of_list es)
  | Proj (proj, e) ->
      first_fv_rec sigma numrels e
  | Cast (e,ck,t) ->
      shortcut_option_or (first_fv_rec sigma numrels e)
        (fun () -> first_fv_rec sigma numrels t)
  | App (f, args) ->
      shortcut_option_or (first_fv_rec sigma numrels f)
        (fun () -> array_option_exists (first_fv_rec sigma numrels) args)
  | LetIn (x,e,t,b) ->
      shortcut_option_or (first_fv_rec sigma numrels e)
        (fun () -> shortcut_option_or (first_fv_rec sigma numrels t)
          (fun () -> Option.map int_pred (first_fv_rec sigma (numrels+1) b)))
  | Case (ci, p, iv, item, branches) ->
      shortcut_option_or (first_fv_rec sigma numrels p)
        (fun () -> shortcut_option_or (first_fv_rec sigma numrels item)
          (fun () -> array_option_exists (first_fv_rec sigma numrels) branches))
  | Prod (x,t,b) ->
      shortcut_option_or (first_fv_rec sigma numrels t)
        (fun () -> Option.map int_pred (first_fv_rec sigma (numrels+1) b))
  | Lambda (x,t,b) ->
      shortcut_option_or (first_fv_rec sigma numrels t)
        (fun () -> Option.map int_pred (first_fv_rec sigma (numrels+1) b))
  | Fix ((ia, i), (nameary, tyary, funary)) ->
      let n = Array.length funary in
      shortcut_option_or (array_option_exists (first_fv_rec sigma numrels) tyary)
        (fun () -> Option.map (fun i -> i-n) (array_option_exists (first_fv_rec sigma (numrels+n)) funary))
  | CoFix (i, (nameary, tyary, funary)) ->
      let n = Array.length funary in
      shortcut_option_or (array_option_exists (first_fv_rec sigma numrels) tyary)
        (fun () -> Option.map (fun i -> i-n) (array_option_exists (first_fv_rec sigma (numrels+n)) funary))

let first_fv (sigma : Evd.evar_map) (term : EConstr.t) : int option =
  first_fv_rec sigma 0 term

let has_fv sigma term : bool =
  first_fv sigma term <> None

(* func must be a constant or constructor *)
let replace_app ~(cfunc : string) (env : Environ.env) (sigma : Evd.evar_map) (func : Constr.t) (args : EConstr.t array) : Environ.env * EConstr.t * string =
  (* msg_info_hov (Pp.str "[codegen] replace_app: " ++ Printer.pr_econstr_env env sigma (mkApp ((EConstr.of_constr func), args))); *)
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
    let fv_opt = first_fv sigma nf_arg in
    match fv_opt with
    | None -> ()
    | Some k ->
        user_err (Pp.str "[codegen] Free variable found in a static argument:" +++
          Printer.pr_constr_env env sigma func ++
          Pp.str "'s" +++
          Pp.str (CString.ordinal (i+1)) +++
          Pp.str "static argument" +++
          Printer.pr_econstr_env env sigma nf_arg +++
          Pp.str "refer" +++
          Printer.pr_econstr_env env sigma (mkRel k)))
    nf_static_args);
  let nf_static_args = CArray.map_to_list (EConstr.to_constr sigma) nf_static_args in
  let efunc = EConstr.of_constr func in
  let efunc_type = Retyping.get_type_of env sigma efunc in
  let (_, presimp, _) = build_presimp env sigma efunc efunc_type sd_list nf_static_args in
  (*msg_info_hov (Pp.str "[codegen] replace presimp: " ++ Printer.pr_constr_env env sigma presimp);*)
  let (env, sp_inst) = match ConstrMap.find_opt presimp sp_cfg.sp_instance_map with
    | None ->
        let icommand = if sp_cfg.sp_is_cstr then CodeGenPrimitive else CodeGenStaticFunction in
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
    msg_debug_hov (Pp.str "[codegen] replace arg: " ++ Printer.pr_econstr_env env sigma term));
  let (env, result, referred_cfuncs) = replace1 ~cfunc env sigma term in
  (if !opt_debug_replace then
    msg_debug_hov (Pp.str "[codegen] replace ret: " ++ Printer.pr_econstr_env env sigma result));
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
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let ((env2', referred_cfuncs), fary') = CArray.fold_left_map
        (fun (env3, referred_cfuncs) f ->
          let (env4, f', referred_cfuncs') = replace ~cfunc env3 sigma f in
          ((env4, StringSet.union referred_cfuncs referred_cfuncs'), f'))
        (env2, StringSet.empty) fary
      in
      let env' = Environ.pop_rel_context (Array.length nary) env2' in
      (env', mkFix ((ia, i), (nary, tary, fary')), referred_cfuncs)
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
  | Case (ci, p, iv, item, branches) ->
      let ((env', referred_cfuncs), branches') = CArray.fold_left_map
        (fun (env2, referred_cfuncs) f ->
          let (env3, f', referred_cfuncs') = replace ~cfunc env2 sigma f in
          ((env3, StringSet.union referred_cfuncs referred_cfuncs'), f'))
        (env, StringSet.empty) branches
      in
      (env', mkCase (ci, p, iv, item, branches'), referred_cfuncs)
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

(*
  - complete_args_fun transforms "term" to begin with p lambdas.
    (fix can be mixed in the lambdas.)
  - "term" is evaluated with p arguments.
  - p = numargs_of_exp env sigma term
  - complete_args_fun is used for top-level functions and closure creations.
*)
let rec complete_args_fun (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (p : int) : EConstr.t =
  (*msg_debug_hov (Pp.str "[codegen] complete_args_fun arg:" +++ Printer.pr_econstr_env env sigma term +++ Pp.str "(p=" ++ Pp.int p ++ Pp.str ")");*)
  let result = complete_args_fun1 env sigma term p in
  (*msg_debug_hov (Pp.str "[codegen] complete_args_fun result:" +++ Printer.pr_econstr_env env sigma result);*)
  check_convertible "complete_args_fun" env sigma term result;
  result
and complete_args_fun1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (p : int) : EConstr.t =
  if p = 0 then
    complete_args_exp env sigma term [||] 0
  else
    match EConstr.kind sigma term with
    | Lambda (x,t,e) ->
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        mkLambda (x, t, complete_args_fun env2 sigma e (p-1))
    | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
        let env2 = push_rec_types prec env in
        let fary2 = Array.map2
          (fun t f ->
            let p' = numargs_of_type env sigma t in
            complete_args_fun env2 sigma f p')
          tary fary
        in
        mkFix ((ia, i), (nary, tary, fary2))
    | _ ->
        (* reduction/expansion: eta-expansion *)
        let t = Retyping.get_type_of env sigma term in
        let t = Reductionops.nf_all env sigma t in
        let (fargs, result_type) = decompose_prod sigma t in
        let term' = Vars.lift p term in
        let vs = array_rev (iota_ary 1 p) in
        let env2 = EConstr.push_rel_context (List.map (fun (x, t) -> Context.Rel.Declaration.LocalAssum (x,t)) fargs) env in
        let term'' = complete_args_exp env2 sigma term' vs 0 in
        compose_lam fargs term''

(*
  - complete_args_branch translates "term" to begin with p lambdas.
  - Unlike complete_args_fun, it doesn't permt fix in the lambdas.
    This is because code generation for match-expression needs
    a lambda-expression for each assignment of constructor arguments.
  - p <= numargs_of_exp env sigma term
*)
and complete_args_branch (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (p : int) (q : int) : EConstr.t =
  (*msg_debug_hov (Pp.str "[codegen] complete_args_branch arg:" +++ Printer.pr_econstr_env env sigma term +++ Pp.str "(p=" ++ Pp.int p ++ Pp.str " q=" ++ Pp.int q ++ Pp.str ")");*)
  let result = complete_args_branch1 env sigma term p q in
  (*msg_debug_hov (Pp.str "[codegen] complete_args_branch result:" +++ Printer.pr_econstr_env env sigma result);*)
  check_convertible "complete_args_branch" env sigma term result;
  result
and complete_args_branch1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (p : int) (q : int) : EConstr.t =
  if p = 0 then
    complete_args_exp env sigma term [||] q
  else
    match EConstr.kind sigma term with
    | Lambda (x,t,e) ->
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        mkLambda (x, t, complete_args_branch env2 sigma e (p-1) q)
    | _ ->
        (* reduction/expansion: eta-expansion *)
        let t = Retyping.get_type_of env sigma term in
        let t = Reductionops.nf_all env sigma t in
        let (fargs, result_type) = decompose_prod sigma t in
        let fargs' = CList.lastn p fargs in
        let term' = Vars.lift p term in
        let vs = array_rev (iota_ary 1 p) in
        let env2 = EConstr.push_rel_context (List.map (fun (x, t) -> Context.Rel.Declaration.LocalAssum (x,t)) fargs') env in
        let term'' = complete_args_exp env2 sigma term' vs q in
        compose_lam fargs' term''

(*
  - complete_args_exp transforms closure creation expressions in "term vs" to
    lambda-expressions with all arguments. (fix-term is permitted.)
  - "term" is evaluated with argument variables denoted by vs and q unknown values.
  - p = |vs|
  - r = number of arguments of "term" minus p + q
    (term : x1 -> ... -> xp -> y1 -> ... -> yq -> z1 -> ... -> zr -> inductive-type)
  - Note that v (with empty vs) is not closure creation but
    c and C (with empty vs) is closure creation.
    Because local variable (v) is already bound to a closure but
    constant (c) and constructor (C) has no corresponding closure.
*)
and complete_args_exp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (vs : int array) (q : int) : EConstr.t =
  (*msg_debug_hov (Pp.str "[codegen] complete_args_exp arg:" +++
    Printer.pr_econstr_env env sigma term +++ Pp.str "[" ++ pp_sjoinmap_ary (fun i -> Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)) ++ Pp.str "(" ++ Pp.int i ++ Pp.str ")") vs ++ Pp.str "]" +++ Pp.str "(p=" ++ Pp.int (Array.length vs) ++ Pp.str " q=" ++ Pp.int q ++ Pp.str ")");*)
  let term' = mkApp (term, Array.map (fun j -> mkRel j) vs) in
  let result = complete_args_exp1 env sigma term vs q in
  (*msg_debug_hov (Pp.str "[codegen] complete_args_exp result:" +++ Printer.pr_econstr_env env sigma result);*)
  check_convertible "complete_args_exp" env sigma term' result;
  result
and complete_args_exp1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (vs : int array) (q : int) : EConstr.t =
  let p = Array.length vs in
  let fargs = lazy (
      let ty = Retyping.get_type_of env sigma term in
      let ty = Reductionops.nf_all env sigma ty in
      fst (decompose_prod sigma ty))
  in
  let r = lazy (List.length (Lazy.force fargs) - p - q) in
  let mkClosure () =
    let lazy fargs = fargs in
    let lazy r = r in
    let fargs' = CList.firstn (q+r) fargs in
    let term' = Vars.lift (q+r) term in
    let args =
      Array.append
        (Array.map (fun j -> mkRel (j+q+r)) vs)
        (Array.map (fun j -> mkRel j) (array_rev (iota_ary 1 (q+r))))
    in
    (* reduction/expansion: eta-expansion *)
    compose_lam fargs' (mkApp (term', args))
  in
  let mkAppOrClosure () =
    let lazy r = r in
    if r = 0 then
      mkApp (term, Array.map (fun j -> mkRel j) vs)
    else
      mkClosure ()
  in
  match EConstr.kind sigma term with
  | App (f,args) ->
      let vs' = Array.map (fun a -> destRel sigma a) args in
      complete_args_exp env sigma f (Array.append vs' vs) q
  | Cast (e,ck,t) -> complete_args_exp env sigma e vs q
  | Rel i ->
      if p = 0 && q = 0 then
        term
      else
        mkAppOrClosure ()
  | Const _ -> mkAppOrClosure ()
  | Construct _ -> mkAppOrClosure ()
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      (* p = 0, q = 0, r = 0 is not possible because Lambda is a function *)
      if p = 0 && q = 0 then
        (* p = 0, q = 0, r > 0
           closure creation found. *)
        let lazy r = r in
        mkLambda (x, t, complete_args_fun env2 sigma e (p+q+r-1))
      else if p > 0 && (Lazy.force r) = 0 then
        (* p > 0, q = 0, r = 0
           p > 0, q > 0, r = 0
           apply beta-var reduction.
           r = 0 because beta-var needs that the result type is inductive type. *)
        let term' = Vars.subst1 (mkRel vs.(0)) e in (* reduction/expansion: beta *)
        let vs' = Array.sub vs 1 (p-1) in
        complete_args_exp env sigma term' vs' q
      else
        (* p = 0, q > 0, r = 0
           p = 0, q > 0, r > 0
           p > 0, q = 0, r > 0
           p > 0, q > 0, r > 0 *)
        mkApp (
          mkLambda (x, t, complete_args_exp env2 sigma e [||] (p+q-1)),
          Array.map (fun j -> mkRel j) vs)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let vs' = Array.map (fun j -> j+1) vs in
      mkLetIn (x,
        complete_args_exp env sigma e [||] 0,
        t,
        complete_args_exp env2 sigma b vs' q)
  | Case (ci, epred, iv, item, branches) ->
      mkApp (
        mkCase (ci, epred, iv, item,
          Array.mapi
            (fun i br ->
              complete_args_branch env sigma br ci.ci_cstr_nargs.(i) (p+q))
            branches),
        Array.map (fun j -> mkRel j) vs)
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      mkApp (
        mkFix ((ia, i),
          (nary,
           tary,
           Array.mapi
             (fun j f ->
               let t = tary.(j) in
               let n = numargs_of_type env sigma t in
               complete_args_fun env2 sigma f n)
             fary)),
        Array.map (fun j -> mkRel j) vs)
  | Proj (proj, e) ->
      mkApp (
        mkProj (proj,
          complete_args_exp env sigma e [||] 0),
        Array.map (fun j -> mkRel j) vs)
  | Var _ | Meta _ | Evar _
  | Sort _ | Prod _ | Ind _
  | CoFix _
  | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:complete_arguments_exp] unexpected term:" +++
        Printer.pr_econstr_env env sigma term)

let complete_args (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (*msg_debug_hov (Pp.str "[codegen] complete_args arg:" +++ Printer.pr_econstr_env env sigma term);*)
  let result = complete_args_fun env sigma term (numargs_of_exp env sigma term) in
  (*msg_debug_hov (Pp.str "[codegen] complete_args result:" +++ Printer.pr_econstr_env env sigma result);*)
  result

let rec formal_argument_names (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Name.t Context.binder_annot list =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      x :: formal_argument_names env2 sigma e
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      formal_argument_names env2 sigma fary.(i)
  | _ -> []

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
  let rec r (env : Environ.env) (term : EConstr.t) (vars : Name.t Context.binder_annot list) =
    match EConstr.kind sigma term with
    | Lambda (x,t,e) ->
        (match vars with
        | [] ->
            let x2 = make_new_var x in
            let decl = Context.Rel.Declaration.LocalAssum (x2, t) in
            let env2 = EConstr.push_rel decl env in
            mkLambda (x2, t, r env2 e vars)
        | var :: rest ->
            if Name.is_anonymous (Context.binder_name var) then
              let x2 = make_new_var x in
              let decl = Context.Rel.Declaration.LocalAssum (x2, t) in
              let env2 = EConstr.push_rel decl env in
              mkLambda (x2, t, r env2 e rest)
            else
              let decl = Context.Rel.Declaration.LocalAssum (var, t) in
              let env2 = EConstr.push_rel decl env in
              mkLambda (var, t, r env2 e rest))
    | LetIn (x,e,t,b) ->
        let x2 = make_new_var x in
        let decl = Context.Rel.Declaration.LocalDef (x2, e, t) in
        let env2 = EConstr.push_rel decl env in
        mkLetIn (x2, r env e [], t, r env2 b vars)
    | Fix ((ia, i), (nary, tary, fary)) ->
        let nary2 = Array.map (fun n -> make_new_fixfunc n) nary in
        let env2 = push_rec_types (nary2, tary, fary) env in
        let fary2 = Array.map (fun e -> r env2 e []) fary in
        let tary2 = Array.mapi (fun i t ->
            let f = fary2.(i) in
            let argnames = List.rev (formal_argument_names env2 sigma f) in
            let (args, result_type) = decompose_prod sigma t in
            (if List.length argnames <> List.length args then
              user_err (Pp.str "[codegen:rename_vars:bug] unexpected length of formal arguments:"));
            let args2 = List.map2 (fun (arg_name, arg_type) arg_name2 -> (arg_name2, arg_type)) args argnames in
            compose_prod args2 result_type)
          tary
        in
        mkFix ((ia, i), (nary2, tary2, fary2))
    | App (f,args) ->
        let vars2 =
          (List.append
            (CArray.map_to_list
              (fun a ->
                let decl = Environ.lookup_rel (destRel sigma a) env in
                Context.Rel.Declaration.get_annot decl)
              args)
            vars)
        in
        mkApp (r env f vars2, args)
    | Cast (e,ck,t) -> mkCast (r env e vars, ck, t)
    | Rel i -> term
    | Const _ -> term
    | Construct _ -> term
    | Case (ci, epred, iv, item, branches) ->
        mkCase (ci, epred, iv, item,
          Array.mapi
            (fun i br ->
              r env br
                (List.append
                  (List.init ci.ci_cstr_nargs.(i) (fun _ -> Context.anonR))
                  vars))
            branches)
    | Proj _ -> term
    | Var _ | Meta _ | Evar _ | Sort _ | Prod (_, _, _) | Ind _
    | CoFix _ | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:rename_vars] unexpected term:" +++
        Printer.pr_econstr_env env sigma term)
  in
  r env term []

let specialization_time = ref (Unix.times ())

let init_debug_simplification () : unit =
  if !opt_debug_simplification then
    specialization_time := Unix.times ()

let debug_simplification (env : Environ.env) (sigma : Evd.evar_map) (step : string) (term : EConstr.t) : unit =
  if !opt_debug_simplification then
    (let old = !specialization_time in
    let now = Unix.times () in
    msg_debug_hov (Pp.str ("--" ^ step ^ "--> (") ++ Pp.real (now.Unix.tms_utime -. old.Unix.tms_utime) ++ Pp.str "[s])" ++ Pp.fnl () ++ (pr_deep (Printer.pr_econstr_env env sigma term)));
    specialization_time := now)

let codegen_simplify (cfunc : string) : Environ.env * Constant.t * StringSet.t =
  init_debug_simplification ();
  let (sp_cfg, sp_inst) =
    match CString.Map.find_opt cfunc !cfunc_instance_map with
    | None ->
        user_err (Pp.str "[codegen] specialization instance not defined:" +++
                  Pp.str (escape_as_coq_string cfunc))
    | Some (sp_cfg, sp_inst) -> (sp_cfg, sp_inst)
  in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let name = (match sp_inst.sp_simplified_status with
    | SpNoSimplification -> user_err (Pp.str "[codegen] not a target of simplification:" +++ Pp.str cfunc)
    | SpExpectedId id -> id
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
    Pp.str "Start simplification:" +++ Id.print name);
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
  (*let term = strip_cast env sigma term in*)
  let term = expand_eta_top env sigma term in
  debug_simplification env sigma "expand_eta_top" term;
  let term = normalizeV env sigma term in
  debug_simplification env sigma "normalizeV" term;
  let term = reduce_exp env sigma term in
  debug_simplification env sigma "reduce_exp" term;
  let term = normalize_types env sigma term in
  debug_simplification env sigma "normalize_types" term;
  let term = normalize_static_arguments env sigma term in
  debug_simplification env sigma "normalize_static_arguments" term;
  let term = delete_unused_let env sigma term in
  debug_simplification env sigma "delete_unused_let" term;
  let (env, term, referred_cfuncs) = replace ~cfunc env sigma term in (* "replace" modifies global env *)
  debug_simplification env sigma "replace" term;
  let term = complete_args env sigma term in
  debug_simplification env sigma "complete_args" term;
  Linear.linear_type_check_term env sigma term;
  let term = rename_vars env sigma term in
  debug_simplification env sigma "rename_vars" term;
  let globref = Declare.declare_definition
    ~info:(Declare.Info.make ())
    ~cinfo:(Declare.CInfo.make ~name:name ~typ:None ())
    ~opaque:false
    ~body:term
    sigma
  in
  let declared_ctnt = Globnames.destConstRef globref in
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
    let m = CString.Map.set sp_inst.sp_cfunc_name (sp_cfg, sp_inst2) m in
    cfunc_instance_map := m);
  (let inst_map = ConstrMap.add presimp sp_inst2 sp_cfg.sp_instance_map in
   let sp_cfg2 = { sp_cfg with sp_instance_map = inst_map } in
   let m = !specialize_config_map in
   specialize_config_map := ConstrMap.add sp_cfg.sp_func sp_cfg2 m);
  let env = Global.env () in
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
    | Some (sp_cfg, sp_inst) ->
        match sp_inst.sp_simplified_status with
        | SpNoSimplification -> ()
        | SpExpectedId _ ->
            let (_, _, referred_cfuncs) = codegen_simplify cfunc in
            (StringSet.iter (recursive_simplify visited rev_postorder) referred_cfuncs);
            rev_postorder := cfunc :: !rev_postorder
        | SpDefined (declared_ctnt, referred_cfuncs) ->
            (StringSet.iter (recursive_simplify visited rev_postorder) referred_cfuncs);
            rev_postorder := cfunc :: !rev_postorder)

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

let command_deallocator_type (t : Constrexpr.constr_expr) (cfunc : string) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_type_evars env sigma t in
  let t = Reductionops.nf_all env sigma t in
  let t = EConstr.to_constr sigma t in
  deallocator_cfunc_of_type := ConstrMap.add t cfunc !deallocator_cfunc_of_type
