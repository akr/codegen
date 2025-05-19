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
open CErrors
open EConstr

open Cgenutil
open Filegen
open State
open Induc
open Specialize

type indimp_mods = {
  indimp_mods_heap : bool option;
  indimp_mods_output_type_decls : (string * string) option;
  indimp_mods_output_type_impls : (string * string) option;
  indimp_mods_output_func_decls : (string * string) option;
  indimp_mods_output_func_impls : (string * string) option;
  indimp_mods_prefix : string option;
  indimp_mods_static : bool option;
}

let indimp_mods_empty = {
  indimp_mods_heap = None;
  indimp_mods_output_type_decls = None;
  indimp_mods_output_type_impls = None;
  indimp_mods_output_func_decls = None;
  indimp_mods_output_func_impls = None;
  indimp_mods_prefix = None;
  indimp_mods_static = None;
}

let merge_indimp_mods (mods1 : indimp_mods) (mods2 : indimp_mods) : indimp_mods =
  {
    indimp_mods_heap = optmerge "heap" mods1.indimp_mods_heap mods2.indimp_mods_heap;
    indimp_mods_output_type_decls = optmerge "output_type_decls" mods1.indimp_mods_output_type_decls mods2.indimp_mods_output_type_decls;
    indimp_mods_output_type_impls = optmerge "output_type_impls" mods1.indimp_mods_output_type_impls mods2.indimp_mods_output_type_impls;
    indimp_mods_output_func_decls = optmerge "output_func_decls" mods1.indimp_mods_output_func_decls mods2.indimp_mods_output_func_decls;
    indimp_mods_output_func_impls = optmerge "output_func_impls" mods1.indimp_mods_output_func_impls mods2.indimp_mods_output_func_impls;
    indimp_mods_prefix = optmerge "prefix" mods1.indimp_mods_prefix mods2.indimp_mods_prefix;
    indimp_mods_static = optmerge "static" mods1.indimp_mods_static mods2.indimp_mods_static;
  }

(* ind_recursive_p checks only non-mutual recursion.  ind_mutual_p should be checked as well. *)
let ind_recursive_p (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  let open Declarations in
  let (f, _params) = decompose_appvect sigma coq_type in
  let ((mutind0, _i), _u) = destInd sigma f in
  let mutind_body = Environ.lookup_mind mutind0 env in
  let rec traverse f c = f c; Constr.iter (fun c' -> traverse f c') c in
  let exception RecursionFound in
  try
    mutind_body.mind_packets |> Array.iter (fun oneind_body ->
      oneind_body.mind_nf_lc |> Array.iter (fun (ctx, ret) ->
        ctx |> List.iter (fun decl ->
          let cs =
            match decl with
            | Context.Rel.Declaration.LocalAssum (_name, ty) -> [ty]
            | Context.Rel.Declaration.LocalDef (_name, expr, ty) -> [expr; ty]
          in
          cs |> List.iter (traverse (fun c ->
            match Constr.kind c with
            | Ind ((mutind, _i), _u) ->
                if MutInd.CanOrd.equal mutind0 mutind then
                  raise RecursionFound
            | _ -> ())))));
    false
  with RecursionFound ->
    true

let ind_mutual_p (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  (*msg_info_hov (Pp.str "[codegen] ind_mutual_p:" +++ Printer.pr_econstr_env env sigma coq_type);*)
  let open Declarations in
  let (f, _params) = decompose_appvect sigma coq_type in
  let (ind, _u) = destInd sigma f in
  let (mutind, _i) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  mutind_body.mind_ntypes <> 1

let check_ind_id_conflict (mib : Declarations.mutual_inductive_body) : unit =
  let open Declarations in
  let h = Hashtbl.create 0 in
  for i = 0 to mib.mind_ntypes - 1 do
    let oib = mib.mind_packets.(i) in
    let type_id = oib.mind_typename in
    if Hashtbl.mem h type_id then
      user_err (Pp.str "[codegen] inductive type name conflict:" +++ Id.print type_id);
    Hashtbl.add h type_id true
  done;
  for i = 0 to mib.mind_ntypes - 1 do
    let oib = mib.mind_packets.(i) in
    for j0 = 0 to Array.length oib.mind_consnames - 1 do
      let cn_id = oib.mind_consnames.(j0) in
      if Hashtbl.mem h cn_id then
        user_err (Pp.str "[codegen] constructor name conflict:" +++ Id.print cn_id);
      Hashtbl.add h cn_id true
    done
  done

type member_names = {
  member_type_lazy: c_typedata Lazy.t;
  member_name: string;
  member_accessor: string;
}

type nvmember_names = {
  nvmember_type: c_typedata; (* non-void *)
  nvmember_name: string;
  nvmember_accessor: string;
}

type 't cstr_names = {
  cn_j: int;
  cn_id: Id.t;
  cn_name: string;
  cn_enum_const: string;
  cn_struct_tag: string;
  cn_umember: string; (* union member name *)
  cn_members: 't list; (* member_names list or nvmember_names list *)
  cn_deallocator_lazy: string option Lazy.t;
}

type 't ind_names = {
  inm_pind: inductive puniverses;
  inm_params: EConstr.t array;
  inm_name: string;
  inm_struct_tag: string;
  inm_enum_tag: string;
  inm_swfunc: string;
  inm_cstrs: 't cstr_names array;
}

let pr_member_names (_env : Environ.env) (_sigma : Evd.evar_map) (member_names : member_names) : Pp.t =
  Pp.v 2 (Pp.str "{" +++
    Pp.hov 2 (Pp.str "member_type:" +++ (if Lazy.is_val member_names.member_type_lazy then
        match member_names.member_type_lazy with
        | lazy c_type -> pr_c_abstract_decl c_type
      else
        Pp.str "(lazy)")) +++
    Pp.hov 2 (Pp.str "member_name:" +++ Pp.qstring member_names.member_name) +++
    Pp.hov 2 (Pp.str "member_accessor:" +++ Pp.qstring member_names.member_accessor) ++ Pp.brk (0,-2) ++
  Pp.str "}")

let pr_cstr_names (env : Environ.env) (sigma : Evd.evar_map) (cstr_names : member_names cstr_names) : Pp.t =
  Pp.v 2 (Pp.str "{" +++
    Pp.hov 2 (Pp.str "cn_j:" +++ Pp.int cstr_names.cn_j) +++
    Pp.hov 2 (Pp.str "cn_id:" +++ Id.print cstr_names.cn_id) +++
    Pp.hov 2 (Pp.str "cn_name:" +++ Pp.qstring cstr_names.cn_name) +++
    Pp.hov 2 (Pp.str "cn_enum_const:" +++ Pp.qstring cstr_names.cn_enum_const) +++
    Pp.hov 2 (Pp.str "cn_struct_tag:" +++ Pp.qstring cstr_names.cn_struct_tag) +++
    Pp.hov 2 (Pp.str "cn_umember:" +++ Pp.qstring cstr_names.cn_umember) +++
    pp_sjoinmap_list (pr_member_names env sigma) cstr_names.cn_members ++ Pp.brk (0,-2) ++
  Pp.str "}")

let pr_ind_names (env : Environ.env) (sigma : Evd.evar_map) (ind_names : member_names ind_names) : Pp.t =
  Pp.v 2 (Pp.str "{" +++
    Pp.hov 2 (Pp.str "inm_pind:" +++ Printer.pr_inductive env (fst ind_names.inm_pind)) +++
    Pp.hov 2 (Pp.str "inm_params:" +++ pp_sjoinmap_ary (Printer.pr_econstr_env env sigma) ind_names.inm_params) +++
    Pp.hov 2 (Pp.str "inm_name:" +++ Pp.qstring ind_names.inm_name) +++
    Pp.hov 2 (Pp.str "inm_struct_tag:" +++ Pp.qstring ind_names.inm_struct_tag) +++
    Pp.hov 2 (Pp.str "inm_enum_tag:" +++ Pp.qstring ind_names.inm_enum_tag) +++
    Pp.hov 2 (Pp.str "inm_swfunc:" +++ Pp.qstring ind_names.inm_swfunc) +++
    pp_sjoinmap_ary (pr_cstr_names env sigma) ind_names.inm_cstrs ++ Pp.brk (0,-2) ++
  Pp.str "}")

let _ = ignore pr_ind_names

let non_void_cstr_members (cn_members : member_names list) : nvmember_names list =
  cn_members |> List.filter_map (fun { member_type_lazy; member_name; member_accessor } ->
    match member_type_lazy with
    | lazy member_type ->
        if c_type_is_void member_type then
          None
        else
          Some { nvmember_type=member_type;
                 nvmember_name=member_name;
                 nvmember_accessor=member_accessor })

let non_void_cstr_names (cstr_names : member_names cstr_names) : nvmember_names cstr_names =
  { cstr_names with cn_members = non_void_cstr_members cstr_names.cn_members }

let non_void_ind_names (ind_names : member_names ind_names) : nvmember_names ind_names =
  { ind_names with inm_cstrs = Array.map non_void_cstr_names ind_names.inm_cstrs }

(* Generate automatic generated names.  No user configuration considered. *)
let generate_indimp_names (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) ~(global_prefix : string option) ~(heap : bool) : member_names ind_names =
  let (f, args) = decompose_appvect sigma coq_type in
  let params = args in (* xxx: args should be parameters of inductive type *)
  let pind = destInd sigma f in
  let (ind, _u) = pind in
  let (mutind_body, oneind_body) = Inductive.lookup_mind_specif env ind in
  check_ind_id_conflict mutind_body;
  let open Declarations in
  let global_prefix = match global_prefix with Some prefix -> prefix | None -> global_gensym () in
  let i_suffix = "_" ^ Id.to_string oneind_body.mind_typename in
  let inm_name = global_prefix ^ "_type" ^ i_suffix in
  let inm_struct_tag = global_prefix ^ "_istruct" ^ i_suffix in
  let inm_enum_tag = global_prefix ^ "_enum" ^ i_suffix in
  let inm_swfunc = global_prefix ^ "_sw" ^ i_suffix in
  let inm_cstrs =
    oneind_body.mind_consnames |> Array.mapi (fun j0 cn_id ->
      let cn_j = j0 + 1 in
      (*msg_debug_hov (Printer.pr_econstr_env env sigma coq_type);*)
      let cstrterm = mkApp (mkConstructUi (pind, cn_j), params) in
      (*msg_debug_hov (Printer.pr_econstr_env env sigma cstrterm);*)
      let cstrtype = Reductionops.nf_all env sigma (Retyping.get_type_of env sigma cstrterm) in
      let (revargs, _result_type) = decompose_prod sigma cstrtype in
      let j_suffix = "_" ^ Id.to_string cn_id in
      let cn_name = global_prefix ^ "_cstr" ^ j_suffix  in
      let cn_enum_const = global_prefix ^ "_tag" ^ j_suffix in
      let cn_struct_tag = global_prefix ^ "_cstruct" ^ j_suffix in
      let cn_umember = global_prefix ^ "_umember" ^ j_suffix in
      let cn_members =
        (List.rev revargs) |> List.mapi (fun k (arg_name, arg_type) ->
          (if not (EConstr.Vars.closed0 sigma arg_type) then
            user_err_hov (Pp.str "[codegen] dependent constructor argument:" +++
              Pp.pr_nth (k+1) +++ Pp.str "argument of" +++
              Printer.pr_econstr_env env sigma cstrterm +++ Pp.str "is" +++
              Printer.pr_econstr_env env sigma arg_type));
          let k_suffix =
            string_of_int (k+1) ^ "_" ^ Id.to_string cn_id ^
            match Context.binder_name arg_name with
            | Name.Anonymous -> ""
            | Name.Name id -> "_" ^ c_id (Id.to_string id)
          in
          let member_name = global_prefix ^ "_member" ^ k_suffix in
          let member_accessor = global_prefix ^ "_get" ^ k_suffix in
          let member_type_lazy = lazy (if ind_is_void_type env sigma arg_type then c_type_void else c_typename env sigma arg_type) in
          { member_type_lazy; member_name; member_accessor })
      in
      let cn_deallocator_lazy = lazy (
        (* deallocator depends on user configuration (heap or not, void or not, constant or not) *)
        if not heap then
          None
        else
          let nv_cn_members = non_void_cstr_members cn_members in
          if not (CList.is_empty nv_cn_members) then
            Some "free"
          else
            None) in
      { cn_j; cn_id; cn_name; cn_enum_const; cn_struct_tag; cn_umember; cn_members; cn_deallocator_lazy; })
  in
  let result = { inm_pind=pind; inm_params=params; inm_name; inm_struct_tag; inm_enum_tag; inm_swfunc; inm_cstrs } in
  (*msg_info_v (pr_ind_names env sigma result);*)
  result

let get_ind_config_from_ind_names (sigma : Evd.evar_map) (ind_names : member_names ind_names) : ind_config =
  let { inm_pind; inm_params; inm_name; inm_swfunc; inm_cstrs } = ind_names in
  let ind_coq_type = EConstr.to_constr sigma (mkApp (mkIndU inm_pind, inm_params)) in
  let ind_c_type = Some (simple_c_type inm_name) in
  let ind_c_swfunc = Some inm_swfunc in
  let ind_cstr_configs =
    inm_cstrs |> Array.map (fun { cn_id; cn_enum_const; cn_members; cn_deallocator_lazy } ->
      let cstr_id = cn_id in
      let cstr_caselabel = Some cn_enum_const in
      let cstr_deallocator = Some cn_deallocator_lazy in
      let cstr_accessors = cn_members |> CArray.map_of_list (fun { member_name } -> Some member_name) in
      { cstr_id; cstr_caselabel; cstr_accessors; cstr_deallocator; })
  in
  { ind_coq_type; ind_c_type; ind_c_swfunc; ind_cstr_configs }

(* This forces computation of deallocator *)
let check_user_ind_config (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  let { ind_coq_type; ind_c_type; ind_c_swfunc; ind_cstr_configs; } = ind_cfg in
  begin
    match ind_c_type with
    | None -> ()
    | Some ({ c_type_left; c_type_right } as c_type) ->
        if not (valid_c_id_p c_type_left && CString.is_empty c_type_right) then
          user_err_hov (Pp.str "[codegen] IndImp needs C type name as a valid C identifier:" +++ pr_c_abstract_decl c_type)
  end;
  begin
    match ind_c_swfunc with
    | None -> ()
    | Some swfunc -> if not (valid_c_id_p swfunc) then user_err_hov (Pp.str "[codegen] IndImp needs swfunc as a valid C identifier:" +++ Pp.str (quote_coq_string swfunc))
  end;
  ind_cstr_configs |> Array.iter (fun { cstr_id; cstr_caselabel; cstr_accessors; cstr_deallocator; } ->
    begin
      match cstr_caselabel with
      | None -> ()
      | Some caselabel -> if not (valid_c_id_p caselabel) then user_err_hov (Pp.str "[codegen] IndImp needs caselabel as a valid C identifier:" +++ Pp.str (quote_coq_string caselabel))
    end;
    begin
      match cstr_deallocator with
      | None -> ()
      | Some (lazy None) -> ()
      | Some (lazy (Some dealloc)) ->
          user_err_hov (Pp.str "[codegen] IndImp needs deallocator not configured:" +++
          Printer.pr_constr_env env sigma ind_coq_type +++ Id.print cstr_id +++ Pp.str (quote_coq_string dealloc))
    end;
    cstr_accessors |> Array.iter (fun accessor ->
      match accessor with
      | None -> ()
      | Some access ->
          if not (valid_c_id_p access) then user_err_hov (Pp.str "[codegen] IndImp needs accessor as a valid C identifier:" +++ Pp.str (quote_coq_string access))))

let merge_option_right_preference (o1 : 't option) (o2 : 't option) : 't option =
  match o1, o2 with
  | None, None -> None
  | None, Some _ -> o2
  | Some _, None -> o1
  | Some _, Some _ -> o2

let merge_ind_config_right_preference (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg1 : ind_config) (ind_cfg2 : ind_config) : ind_config =
  let { ind_coq_type=ind_coq_type1; ind_c_type=ind_c_type1; ind_c_swfunc=ind_c_swfunc1; ind_cstr_configs=ind_cstr_configs1 } = ind_cfg1 in
  let { ind_coq_type=ind_coq_type2; ind_c_type=ind_c_type2; ind_c_swfunc=ind_c_swfunc2; ind_cstr_configs=ind_cstr_configs2 } = ind_cfg2 in
  if not (Constr.equal ind_coq_type1 ind_coq_type2) then
    user_err_hov (Pp.str "[codegen:merge_ind_config_right_preference] different ind_coq_type:" +++ Printer.pr_constr_env env sigma ind_coq_type1 +++ Printer.pr_constr_env env sigma ind_coq_type2);
  let ind_coq_type = ind_coq_type1 in
  let ind_c_type = merge_option_right_preference ind_c_type1 ind_c_type2 in
  let ind_c_swfunc = merge_option_right_preference ind_c_swfunc1 ind_c_swfunc2 in
  let ind_cstr_configs =
    Array.map2
      (fun cstr_config1 cstr_config2 ->
        let { cstr_id=cstr_id1; cstr_caselabel=cstr_caselabel1; cstr_accessors=cstr_accessors1; cstr_deallocator=cstr_deallocator1; } = cstr_config1 in
        let { cstr_id=cstr_id2; cstr_caselabel=cstr_caselabel2; cstr_accessors=cstr_accessors2; cstr_deallocator=cstr_deallocator2; } = cstr_config2 in
        if not (Id.equal cstr_id1 cstr_id2) then
          user_err_hov (Pp.str "[codegen:merge_ind_config_right_preference] different cstr_id:" +++ Id.print cstr_id1 +++ Id.print cstr_id2);
        let cstr_id = cstr_id1 in
        let cstr_caselabel = merge_option_right_preference cstr_caselabel1 cstr_caselabel2 in
        let cstr_accessors =
          let n1 = Array.length cstr_accessors1 in
          let n2 = Array.length cstr_accessors2 in
          Array.init (if n1 < n2 then n2 else n1) (fun i ->
            let accessor1 = if i < n1 then cstr_accessors1.(i) else None in
            let accessor2 = if i < n2 then cstr_accessors2.(i) else None in
            merge_option_right_preference accessor1 accessor2)
        in
        let cstr_deallocator =
          match cstr_deallocator1, cstr_deallocator2 with
          | None, None -> None
          | None, Some _ -> cstr_deallocator2
          | Some _, None -> cstr_deallocator1
          | Some str_opt_lazy1, Some str_opt_lazy2 ->
              Some (lazy begin
                let (lazy str_opt1, lazy str_opt2) = (str_opt_lazy1, str_opt_lazy2) in
                merge_option_right_preference str_opt1 str_opt2
              end)
        in
        { cstr_id; cstr_caselabel; cstr_accessors; cstr_deallocator })
      ind_cstr_configs1 ind_cstr_configs2
  in
  { ind_coq_type; ind_c_type; ind_c_swfunc; ind_cstr_configs }

let put_ind_config_in_ind_names (env : Environ.env) (sigma : Evd.evar_map) (ind_names : member_names ind_names) (ind_cfg : ind_config) : member_names ind_names =
  let { inm_name; inm_swfunc; inm_cstrs } = ind_names in
  let { ind_coq_type; ind_c_type; ind_c_swfunc; ind_cstr_configs; } = ind_cfg in
  let inm_name =
    match ind_c_type with
    | None -> inm_name
    | Some c_type -> c_type.c_type_left (* check_user_ind_config checks c_type is a simple C identifier *)
  in
  let inm_swfunc = Stdlib.Option.value ind_cfg.ind_c_swfunc ~default:inm_swfunc in
  let inm_cstrs =
    Array.map2 (fun ({ cn_id; cn_enum_const; cn_members; cn_deallocator_lazy; } as cstr_names)
                    { cstr_id; cstr_caselabel; cstr_accessors; cstr_deallocator; } ->
        let cn_enum_const = Stdlib.Option.value cstr_caselabel ~default:cn_enum_const in
        (* cstr_deallocator is ignored because check_user_ind_config checks that it is not specified *)
        let cn_members =
          let n1 = List.length cn_members in
          let n2 = Array.length cstr_accessors in
          if n1 <> n2 then
            user_err_hov (Pp.str "[codegen:put_ind_config_in_ind_names] n1 <> n2");
          Array.init n1 (fun i ->
            let { member_accessor } as cn_mem = List.nth cn_members i in
            let accessor2 = cstr_accessors.(i) in
            let member_accessor = Stdlib.Option.value accessor2 ~default:member_accessor in
            { cn_mem with member_accessor })
        in
        let cn_members = Array.to_list cn_members in
        { cstr_names with cn_enum_const; cn_members; cn_deallocator_lazy; })
      inm_cstrs ind_cstr_configs
  in
  { ind_names with inm_name; inm_swfunc; inm_cstrs; }

(* Merge generated names and user configuration.  Register generated names if no user configuration. *)
let register_indimp (env : Environ.env) (sigma : Evd.evar_map) (ind_names : member_names ind_names) : Environ.env * member_names ind_names =
  (*msg_debug_hov (Pp.str "[codegen:register_indimp]");*)
  let { inm_pind=pind; inm_params=params } = ind_names in
  let coq_type_i = mkApp (mkIndU pind, params) in
  (* Merge information from CodeGen IndType.
     CodeGen IndType COQ_TYPE =>
       ["C_TYPE_LEFT" ["C_TYPE_RIGHT"]]
       [swfunc "C_SWFUNC"]
       [ with ( | CONSTRUCTOR =>
         [case "C_CASELABEL"]
         [accessor "C_ACCESSOR"*]
         [deallocator "C_DEALLOCATOR"] )* ].
         *)
  let indimp_generated_ind_cfg = get_ind_config_from_ind_names sigma ind_names in
  let ind_cfg =
    match lookup_ind_config sigma coq_type_i with
    | None -> indimp_generated_ind_cfg
    | Some ind_cfg ->
        check_user_ind_config env sigma ind_cfg;
        merge_ind_config_right_preference env sigma indimp_generated_ind_cfg ind_cfg
  in
  add_ind_config_map (EConstr.to_constr sigma coq_type_i) ind_cfg;
  let ind_names = put_ind_config_in_ind_names env sigma ind_names ind_cfg in
  (* Merge information from CodeGen Primitive CONSTRUCTOR PARAMS => "CSTR_NAME" *)
  let (env, tuples) =
    let params0 = Array.map (fun param -> Some param) params in
    CArray.fold_left_map
      (fun env cstr_names ->
        let { cn_j; cn_id; cn_name; } = cstr_names in
        let cstrterm = mkConstructUi (pind, cn_j) in
        let cstrterm0 = EConstr.to_constr sigma cstrterm in
        ignore (codegen_define_or_check_static_arguments env sigma cstrterm0 (List.init (Array.length params) (fun _ -> SorD_S)));
        let presimp = EConstr.to_constr sigma (mkApp (cstrterm, params)) in
        match ConstrMap.find_opt presimp (get_gallina_instance_specialization_map ()) with
        | None ->
            let spi = { spi_cfunc_name = Some cn_name; spi_presimp_id = None; spi_simplified_id = None } in
            let (env, _sp_cfg, sp_inst, sp_interface) = codegen_instance_command_primitive env sigma cstrterm params0 (Some spi) in
            (env, (cstr_names, sp_inst, sp_interface))
        | Some (_sp_cfg, { sp_interface = None }) ->
            user_err_hov (Pp.str "[codegen] CodeGen IndImp-generating inductive type has a constructor prohibited by CodeGen NoFunc:" +++ Id.print cn_id);
        | Some (_sp_cfg, ({ sp_interface = Some sp_interface } as sp_inst)) ->
            (env, (cstr_names, sp_inst, sp_interface)))
      env ind_names.inm_cstrs
  in
  let inm_cstrs =
    tuples |> Array.map (fun (cstr_names, sp_inst, sp_interface) ->
      let { sp_icommand } = sp_inst in
      let { sp_cfunc_name = cn_name } = sp_interface in
      if sp_icommand <> CodeGenPrimitive then
        user_err_hov (Pp.str "[codegen] CodeGen IndImp needs that constructors declared by CodeGen Primitive (not " ++ Pp.str (str_instance_command sp_icommand) ++ Pp.str "):" +++ Id.print cstr_names.cn_id);
      if not (valid_c_id_p cn_name) then user_err_hov (Pp.str "[codegen] IndImp needs constructor name as a valid C identifier:" +++ Pp.str (quote_coq_string cn_name));
      { cstr_names with cn_name })
  in
  let ind_names = { ind_names with inm_cstrs } in
  (env, ind_names)

let pr_static (static : bool option) : Pp.t =
  match static with
  | None | Some true -> Pp.str "static"
  | Some false -> Pp.mt ()

let imm_enum_decl (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (single_constructor : bool) : Pp.t =
  let { inm_enum_tag; inm_cstrs } = ind_names in
  if single_constructor then
    Pp.mt ()
  else
    Pp.hov 0 (
      (Pp.str "enum" +++ Pp.str inm_enum_tag +++
      hovbrace (
        pp_joinmap_ary (Pp.str "," ++ Pp.spc ()) (fun { cn_enum_const } -> Pp.str cn_enum_const) inm_cstrs) ++
        Pp.str ";"))

let imm_typedef (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (constant_constructor_only : bool) (single_constructor : bool) : Pp.t =
  let { inm_name; inm_struct_tag; inm_enum_tag; inm_cstrs } = ind_names in
  let member_decls =
    inm_cstrs |> Array.map (fun { cn_members } ->
      cn_members |> pp_sjoinmap_list (fun {nvmember_type; nvmember_name} ->
        Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name) ++ Pp.str ";")))
  in
  let ind_cstrs_with_decls =
    Array.map2
      (fun ind_cstr member_decl -> (ind_cstr, member_decl))
      inm_cstrs member_decls
  in
  let ind_cstrs_with_decls = Array.to_list ind_cstrs_with_decls in
  let pp_cstr_struct_defs =
    if constant_constructor_only || single_constructor then
      Pp.mt ()
    else
      pp_sjoin_list
        (ind_cstrs_with_decls |> List.filter_map (fun ({ cn_struct_tag; cn_members }, member_decl) ->
          if CList.is_empty cn_members then
            None
          else
            Some (
              Pp.hov 0 (Pp.str "struct" +++ Pp.str cn_struct_tag) +++
              vbrace member_decl ++
              Pp.str ";")))
  in
  let pp_typedef =
    Pp.v 0 (
      Pp.str "typedef struct" +++ Pp.str inm_struct_tag +++
      vbrace (
        (if single_constructor then
          Pp.mt ()
        else
          Pp.hov 0 (Pp.str "enum" +++ Pp.str inm_enum_tag +++ Pp.str "tag;")) +++
        (if constant_constructor_only then
          Pp.mt ()
        else if single_constructor then
          Pp.v 0
            (let (_ind_cstr, member_decl) = List.hd ind_cstrs_with_decls in
            member_decl)
        else
          Pp.v 0 (Pp.str "union" +++
                  vbrace (
                    pp_sjoin_list
                      (ind_cstrs_with_decls |> List.filter_map (fun ({ cn_struct_tag; cn_umember; cn_members }, _member_decl) ->
                        if CList.is_empty cn_members then
                          None
                        else
                          Some (
                            Pp.hov 0 (Pp.str "struct" +++
                                      Pp.str cn_struct_tag +++
                                      Pp.str cn_umember ++
                                      Pp.str ";"))))) ++
                  Pp.str " as;"))
      ) ++ Pp.str (" " ^ inm_name ^ ";"))
  in
  pp_cstr_struct_defs +++ pp_typedef

let imm_swfunc (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (single_constructor : bool) (pp_static : Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_swfunc } = ind_names in
  if single_constructor then
    (Pp.mt (), Pp.mt ())
  else
    let pp_declaration = pp_static +++ Pp.str "int" +++ Pp.str inm_swfunc ++ Pp.str "(" ++ Pp.str inm_name +++ Pp.str "x)" in
    let pp_compstmt = vbrace (Pp.hov 0 (Pp.str "return x.tag;")) in
    let pp_prototype = Pp.v 0 (Pp.hov 2 (pp_declaration ++ Pp.str ";")) in
    let pp_definition = Pp.v 0 (Pp.hov 2 pp_declaration +++ pp_compstmt) in
    (pp_prototype, pp_definition)

let imm_accessors (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (single_constructor : bool) (pp_static : Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_cstrs } = ind_names in
  let declaration_compstmt_pairs =
    inm_cstrs |> CArray.map_to_list (fun {cn_umember; cn_members} ->
      cn_members |> List.map (fun {nvmember_type; nvmember_name; nvmember_accessor} ->
        let return_exp =
          if single_constructor then
            "x." ^ nvmember_name
          else
            "x.as." ^ cn_umember ^ "." ^ nvmember_name
        in
        (pp_static +++ Pp.str (compose_c_decl nvmember_type (nvmember_accessor ^ "(" ^ inm_name ^ " x)")),
         vbrace ( Pp.hov 0 (Pp.str "return" +++ Pp.str return_exp ++ Pp.str ";")))))
    |> List.concat
  in
  let pp_prototypes = declaration_compstmt_pairs |> List.map (fun (pp_declaration, _pp_compstmt) -> Pp.v 0 (Pp.hov 2 (pp_declaration ++ Pp.str ";"))) |> pp_sjoin_list in
  let pp_definitions = declaration_compstmt_pairs |> List.map (fun (pp_declaration, pp_compstmt) -> Pp.v 0 (Pp.hov 2 pp_declaration +++ pp_compstmt)) |> pp_sjoin_list in
  (pp_prototypes, pp_definitions)

let imm_cstr (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (single_constructor : bool) (pp_static : Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_cstrs } = ind_names in
  let declaration_compstmt_pairs =
    inm_cstrs |> CArray.map_to_list (fun {cn_name; cn_enum_const; cn_umember; cn_members} ->
      let fargs =
        if CList.is_empty cn_members then
          Pp.str "void"
        else
          pp_joinmap_list (Pp.str "," ++ Pp.spc ())
            (fun {nvmember_type; nvmember_name} -> Pp.str (compose_c_decl nvmember_type nvmember_name))
            cn_members
      in
      let args =
        pp_joinmap_list (Pp.str "," ++ Pp.spc ())
          (fun {nvmember_name} -> Pp.str nvmember_name)
          cn_members
      in
      let pp_declaration = pp_static +++ Pp.str inm_name +++ Pp.str cn_name ++ Pp.str "(" ++ fargs ++ Pp.str ")" in
      let pp_compstmt =
        vbrace (
          Pp.hov 0 (Pp.str inm_name +++ Pp.str "ret" +++
            Pp.str "=" +++
            hbrace (
              if single_constructor then
                args
              else
                let union_init =
                  Pp.str ("." ^ cn_umember) +++
                  Pp.str "=" +++
                  hbrace args
                in
                if CList.is_empty cn_members then
                  Pp.str cn_enum_const
                else
                  (Pp.str cn_enum_const ++ Pp.str "," +++ hbrace union_init)) ++
                  Pp.str ";") +++
            Pp.hov 0 (Pp.str "return ret;")
        )
      in
      (pp_declaration, pp_compstmt))
  in
  let pp_prototypes = declaration_compstmt_pairs |> List.map (fun (pp_declaration, _pp_compstmt) -> Pp.v 0 (Pp.hov 2 (pp_declaration ++ Pp.str ";"))) |> pp_sjoin_list in
  let pp_definitions = declaration_compstmt_pairs |> List.map (fun (pp_declaration, pp_compstmt) -> Pp.v 0 (Pp.hov 2 pp_declaration +++ pp_compstmt)) |> pp_sjoin_list in
  (pp_prototypes, pp_definitions)

let gen_indimp_immediate_impl (ind_names : nvmember_names ind_names) (indimp_mods : indimp_mods) : Pp.t * Pp.t * Pp.t =
  let { inm_cstrs } = ind_names in
  let constant_constructor_only =
    inm_cstrs |> Array.for_all (fun { cn_members } ->
      CList.is_empty cn_members)
  in
  let single_constructor = Array.length inm_cstrs = 1 in
  let pp_enum_decl = imm_enum_decl ind_names indimp_mods single_constructor in
  let pp_typedef = imm_typedef ind_names indimp_mods constant_constructor_only single_constructor in
  let pp_static = pr_static indimp_mods.indimp_mods_static in
  let (pp_swfunc_prototype, pp_swfunc) = imm_swfunc ind_names indimp_mods single_constructor pp_static in
  let (pp_accessors_prototype, pp_accessors) = imm_accessors ind_names indimp_mods single_constructor pp_static in
  let (pp_cstr_prototype, pp_cstr) = imm_cstr ind_names indimp_mods single_constructor pp_static in
  (pp_enum_decl +++ pp_typedef,
   pp_swfunc_prototype +++ pp_accessors_prototype +++ pp_cstr_prototype,
   pp_swfunc +++ pp_accessors +++ pp_cstr)

let gen_indimp_heap_decls (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) : Pp.t =
  let pp_ind_types =
    (* typedef struct inm_struct_tag *inm_name; *)
    let { inm_name; inm_struct_tag } = ind_names in
    Pp.hov 0 (
      Pp.str "typedef" +++
      Pp.str "struct" +++
      Pp.str inm_struct_tag +++
      Pp.str "*" ++
      Pp.str inm_name ++
      Pp.str ";")
  in
  pp_ind_types

let heaps_ind_struct_def (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) : Pp.t =
  let { inm_struct_tag; inm_cstrs } = ind_names in
  let ind_cstr = inm_cstrs.(0) in
  let member_decl =
    (* nvmember_type1 nvmember_name1; ... *)
    let { cn_members } = ind_cstr in
    pp_sjoinmap_list
      (fun {nvmember_type; nvmember_name} ->
        Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name) ++ Pp.str ";"))
      cn_members
  in
  (* struct inm_struct_tag { member_decl } *)
  Pp.hov 0 (Pp.str "struct" +++ Pp.str inm_struct_tag) +++
  vbrace member_decl ++
  Pp.str ";"

let heaps_accessors (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (pp_static : Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_cstrs } = ind_names in
  let ind_cstr = inm_cstrs.(0) in
  let { cn_members } = ind_cstr in
  let declaration_compstmt_pairs =
    cn_members |> List.map (fun {nvmember_type; nvmember_name; nvmember_accessor} ->
      (* pp_static nvmember_type nvmember_accessor(inm_name x) { return x->nvmember_name; } *)
      (pp_static +++ Pp.str (compose_c_decl nvmember_type (nvmember_accessor ^ "(" ^ inm_name ^ " x)")),
       vbrace (Pp.hov 0 (Pp.str "return" +++ Pp.str ("(x->" ^ nvmember_name ^ ")")) ++ Pp.str ";")))
  in
  let pp_prototypes = declaration_compstmt_pairs |> List.map (fun (pp_declaration, _pp_compstmt) -> Pp.v 0 (Pp.hov 2 (pp_declaration ++ Pp.str ";"))) |> pp_sjoin_list in
  let pp_definitions = declaration_compstmt_pairs |> List.map (fun (pp_declaration, pp_compstmt) -> Pp.v 0 (Pp.hov 2 pp_declaration +++ pp_compstmt)) |> pp_sjoin_list in
  (pp_prototypes, pp_definitions)

let heaps_cstr (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (pp_static : Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_cstrs } = ind_names in
  let ind_cstr = inm_cstrs.(0) in
  (*
    pp_static inm_name cn_name(nvmember_type1 nvmember_name1, ...) {
      inm_name p;
      if (!(p = malloc(sizeof(struct list_cons_struct)))) abort();
      p->nvmember_name1 = nvmember_name1;
      ...
      return p;
    }
  *)
  let { cn_name; cn_members } = ind_cstr in
  let fargs =
    if CList.is_empty cn_members then
      Pp.str "void"
    else
      pp_joinmap_list (Pp.str "," ++ Pp.spc ())
        (fun {nvmember_type; nvmember_name} ->
          Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name)))
        cn_members
  in
  let pp_declaration = pp_static +++ Pp.str inm_name +++ Pp.str cn_name ++ Pp.str "(" ++ fargs ++ Pp.str ")" in
  let pp_compstmt =
    vbrace (
      Pp.hov 0 (Pp.str inm_name +++ Pp.str "p;") +++
      Pp.hov 0 (Pp.str ("if (!(p = malloc(sizeof(*p)))) abort();")) +++
      pp_sjoinmap_list
        (fun {nvmember_name} ->
          Pp.hov 0 (Pp.str "p->" ++ Pp.str nvmember_name +++ Pp.str "=" +++ Pp.str nvmember_name ++ Pp.str ";"))
        cn_members +++
      Pp.hov 0 (Pp.str "return p;"))
  in
  let pp_prototype = Pp.v 0 (Pp.hov 2 (pp_declaration ++ Pp.str ";")) in
  let pp_definition = Pp.v 0 (Pp.hov 2 pp_declaration +++ pp_compstmt) in
  (pp_prototype, pp_definition)

let gen_indimp_heap_impls_single_constructor (ind_names : nvmember_names ind_names) (indimp_mods : indimp_mods) : Pp.t * Pp.t * Pp.t =
  let pp_ind_struct_def = heaps_ind_struct_def ind_names indimp_mods in
  let pp_static = pr_static indimp_mods.indimp_mods_static in
  let (pp_accessors_prototype, pp_accessors) = heaps_accessors ind_names indimp_mods pp_static in
  let (pp_cstr_prototype, pp_cstr) = heaps_cstr ind_names indimp_mods pp_static in
  (*msg_debug_hov (Pp.str (Pp.db_string_of_pp pp));*)
  (*msg_info_hov pp;*)
  (pp_ind_struct_def,
   pp_accessors_prototype +++ pp_cstr_prototype,
   pp_accessors +++ pp_cstr)

let heapg_enum_decl (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) : Pp.t =
  let {inm_enum_tag; inm_cstrs} = ind_names in
  (* enum inm_enum_tag { cn_enum_const1, ... }; *)
  Pp.hov 0 (
    (Pp.str "enum" +++ Pp.str inm_enum_tag +++
    hovbrace (
      pp_joinmap_ary (Pp.str "," ++ Pp.spc ()) (fun { cn_enum_const } -> Pp.str cn_enum_const) inm_cstrs) ++
      Pp.str ";"))

let heapg_ind_struct_def (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) : Pp.t =
  let {inm_struct_tag; inm_enum_tag} = ind_names in
  (* struct inm_struct_tag { enum inm_enum_tag tag; }; *)
  Pp.hov 0 (Pp.str "struct" +++ Pp.str inm_struct_tag) +++
    vbrace (Pp.hov 0 (Pp.str ("enum " ^ inm_enum_tag) +++ Pp.str "tag;")) ++
    Pp.str ";"

let heapg_swfunc (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (pp_static : Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_swfunc } = ind_names in
  let pp_swfunc_declaration = pp_static +++ Pp.str "int" +++ Pp.str inm_swfunc ++ Pp.str "(" ++ Pp.str inm_name +++ Pp.str "x)" in
  let pp_swfunc_compstmt = vbrace (Pp.hov 0 (Pp.str "return x->tag;")) in
  (* static int inm_swfunc(inm_name x) { return x->tag; } *)
  let pp_swfunc_prototype = Pp.v 0 (Pp.hov 2 (pp_swfunc_declaration ++ Pp.str ";")) in
  let pp_swfunc = Pp.v 0 (Pp.hov 2 pp_swfunc_declaration +++ pp_swfunc_compstmt) in
  (pp_swfunc_prototype, pp_swfunc)

let heapg_cstr_struct_defs (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) : Pp.t =
  let { inm_enum_tag; inm_cstrs } = ind_names in
  let member_decls =
    (* enum inm_enum_tag tag; nvmember_type1 nvmember_name1; ... *)
    inm_cstrs |> Array.map (fun { cn_members } ->
      Pp.hov 0 (Pp.str ("enum " ^ inm_enum_tag) +++ Pp.str "tag;") +++
      pp_sjoinmap_list
        (fun {nvmember_type; nvmember_name} ->
          Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name) ++ Pp.str ";"))
        cn_members)
  in
  let ind_cstrs_with_decls =
    Array.map2
      (fun ind_cstr member_decl -> (ind_cstr, member_decl))
      inm_cstrs member_decls
  in
  (* struct cn_struct_tag1 { member_decl1 }; ... *)
  ind_cstrs_with_decls |> pp_sjoinmap_ary (fun ({ cn_struct_tag }, member_decl) ->
    Pp.hov 0 (Pp.str "struct" +++ Pp.str cn_struct_tag) +++
    vbrace member_decl ++
    Pp.str ";")

let heapg_accessors (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (pp_static : Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_cstrs } = ind_names in
  let declaration_compstmt_pairs =
    inm_cstrs |> CArray.map_to_list (fun {cn_struct_tag; cn_members} ->
      cn_members |> List.map (fun {nvmember_type; nvmember_name; nvmember_accessor} ->
        (pp_static +++ Pp.str (compose_c_decl nvmember_type (nvmember_accessor ^ "(" ^ inm_name ^ " x)")),
         vbrace (Pp.hov 0 (Pp.str "return" +++ Pp.str ("(((struct " ^ cn_struct_tag ^ " *" ^ ")(x))->" ^ nvmember_name ^ ")")) ++ Pp.str ";"))))
    |> List.concat
  in
  let pp_prototypes = declaration_compstmt_pairs |> List.map (fun (pp_declaration, _pp_compstmt) -> Pp.v 0 (Pp.hov 2 (pp_declaration ++ Pp.str ";"))) |> pp_sjoin_list in
  let pp_definitions = declaration_compstmt_pairs |> List.map (fun (pp_declaration, pp_compstmt) -> Pp.v 0 (Pp.hov 2 pp_declaration +++ pp_compstmt)) |> pp_sjoin_list in
  (pp_prototypes, pp_definitions)

let heapg_cstr (ind_names : nvmember_names ind_names) (_indimp_mods : indimp_mods) (pp_static: Pp.t) : Pp.t * Pp.t =
  let { inm_name; inm_cstrs } = ind_names in
  let declaration_compstmt_pairs =
    inm_cstrs |> CArray.map_to_list (fun { cn_name; cn_enum_const; cn_struct_tag; cn_members } ->
      if CList.is_empty cn_members then
        begin
          (* cn_members is empty:
            static inm_name cn_name(void) {
              static struct cn_struct_tag s = { cn_enum_const };
              return (inm_name)&s;
            }
          *)
          let pp_cstr_declaration = pp_static +++ Pp.str inm_name +++ Pp.str cn_name ++ Pp.str "(void)" in
          let pp_cstr_compstmt =
            vbrace (
              Pp.hov 0 (Pp.str "static struct" +++ Pp.str cn_struct_tag +++ Pp.str "s" +++ Pp.str "=" +++
                hbrace (Pp.str cn_enum_const) ++ Pp.str ";") +++
              Pp.hov 0 (Pp.str "return" +++ Pp.str ("(" ^ inm_name ^ ")&s;")))
          in
          (pp_cstr_declaration, pp_cstr_compstmt)
        end
      else
        begin
        (* cn_members is not empty:
          static inm_name cn_name(nvmember_type1 nvmember_name1, ...) {
            struct cn_struct_tag *p;
            if (!(p = malloc(sizeof( *p)))) abort();
            p->tag = cn_enum_const;
            p->nvmember_name1 = nvmember_name1;
            ...
            return (inm_name)p;
          }
        *)
          let fargs =
            pp_joinmap_list (Pp.str "," ++ Pp.spc ())
              (fun {nvmember_type; nvmember_name} ->
                Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name)))
              cn_members
          in
          let pp_cstr_declaration = pp_static +++ Pp.str inm_name +++ Pp.str cn_name ++ Pp.str "(" ++ fargs ++ Pp.str ")" in
          let pp_cstr_compstmt =
            vbrace (
              Pp.hov 0 (Pp.str "struct" +++ Pp.str cn_struct_tag +++ Pp.str "*p;") +++
              Pp.hov 0 (Pp.str ("if (!(p = malloc(sizeof(" ^ "*p)))) abort();")) +++
              Pp.hov 0 (Pp.str "p->tag =" +++ Pp.str cn_enum_const ++ Pp.str ";") +++
              pp_sjoinmap_list
                (fun {nvmember_name} ->
                  Pp.hov 0 (Pp.str "p->" ++ Pp.str nvmember_name +++ Pp.str "=" +++ Pp.str nvmember_name ++ Pp.str ";"))
                cn_members +++
              Pp.hov 0 (Pp.str "return" +++ Pp.str ("(" ^ inm_name ^ ")p;")))
          in
          (pp_cstr_declaration, pp_cstr_compstmt)
        end)
  in
  let pp_prototypes = declaration_compstmt_pairs |> List.map (fun (pp_declaration, _pp_compstmt) -> Pp.v 0 (Pp.hov 2 (pp_declaration ++ Pp.str ";"))) |> pp_sjoin_list in
  let pp_definitions = declaration_compstmt_pairs |> List.map (fun (pp_declaration, pp_compstmt) -> Pp.v 0 (Pp.hov 2 pp_declaration +++ pp_compstmt)) |> pp_sjoin_list in
  (pp_prototypes, pp_definitions)

let gen_indimp_heap_impls_generic (ind_names : nvmember_names ind_names) (indimp_mods : indimp_mods) : Pp.t * Pp.t * Pp.t =
  let pp_enum_decl = heapg_enum_decl ind_names indimp_mods in
  let pp_ind_struct_def = heapg_ind_struct_def ind_names indimp_mods in
  let pp_static = pr_static indimp_mods.indimp_mods_static in
  let (pp_swfunc_prototype, pp_swfunc) = heapg_swfunc ind_names indimp_mods pp_static in
  let pp_cstr_struct_defs = heapg_cstr_struct_defs ind_names indimp_mods in
  let (pp_accessors_prototype, pp_accessors) = heapg_accessors ind_names indimp_mods pp_static in
  let (pp_cstr_prototype, pp_cstr) = heapg_cstr ind_names indimp_mods pp_static in
  (*msg_debug_hov (Pp.str (Pp.db_string_of_pp pp));*)
  (*msg_info_hov pp;*)
  (pp_enum_decl +++ pp_ind_struct_def +++ pp_cstr_struct_defs,
   pp_swfunc_prototype +++ pp_accessors_prototype +++ pp_cstr_prototype,
   pp_swfunc +++ pp_accessors +++ pp_cstr)

let gen_indimp_heap_impls (ind_names : nvmember_names ind_names) (indimp_mods : indimp_mods) : Pp.t * Pp.t * Pp.t =
  let { inm_cstrs } = ind_names in
  let single_constructor = Array.length inm_cstrs = 1 in
  if single_constructor then
    gen_indimp_heap_impls_single_constructor ind_names indimp_mods
  else
    gen_indimp_heap_impls_generic ind_names indimp_mods

let generate_indimp_immediate (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) (indimp_mods : indimp_mods) : unit =
  msg_info_hov (Pp.str "[codegen] generate_indimp_immediate:" +++ Printer.pr_econstr_env env sigma coq_type);
  let ind_names = generate_indimp_names env sigma coq_type ~global_prefix:indimp_mods.indimp_mods_prefix ~heap:false in
  let env, ind_names = register_indimp env sigma ind_names in
  ignore env;
  (*let (type_decls_filename, type_decls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_type_decls ~default:(get_current_source_filename (), "type_decls") in*)
  let (type_impls_filename, type_impls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_type_impls ~default:(get_current_source_filename (), "type_impls") in
  let (func_decls_filename, func_decls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_func_decls ~default:(get_current_source_filename (), "func_decls") in
  let (func_impls_filename, func_impls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_func_impls ~default:(get_current_source_filename (), "func_impls") in
  let lazy_code = lazy (gen_indimp_immediate_impl (non_void_ind_names ind_names) indimp_mods) in
  let type_impls () = let (type_impls, _func_decls, _func_impls) = Lazy.force lazy_code in Pp.string_of_ppcmds (Pp.v 0 type_impls) in
  let func_decls () = let (_type_impls, func_decls, _func_impls) = Lazy.force lazy_code in Pp.string_of_ppcmds (Pp.v 0 func_decls) in
  let func_impls () = let (_type_impls, _func_decls, func_impls) = Lazy.force lazy_code in Pp.string_of_ppcmds (Pp.v 0 func_impls) in
  codegen_add_generation type_impls_filename (GenThunk (type_impls_section, type_impls));
  codegen_add_generation func_decls_filename (GenThunk (func_decls_section, func_decls));
  codegen_add_generation func_impls_filename (GenThunk (func_impls_section, func_impls));
  ()

let generate_indimp_heap (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) (indimp_mods : indimp_mods) : unit =
  msg_info_hov (Pp.str "[codegen] generate_indimp_heap:" +++ Printer.pr_econstr_env env sigma coq_type);
  (* msg_info_hov (Pp.str "[codegen] generate_indimp_heap:" +++ Printer.pr_econstr_env env sigma coq_type); *)
  let ind_names = generate_indimp_names env sigma coq_type ~global_prefix:indimp_mods.indimp_mods_prefix ~heap:true in
  let env, ind_names = register_indimp env sigma ind_names in
  if optread_indimp_auto_linear () then
    Linear.add_linear_type ~msg_new:true env sigma coq_type;
  ignore env;
  let (type_decls_filename, type_decls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_type_decls ~default:(get_current_source_filename (), "type_decls") in
  let (type_impls_filename, type_impls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_type_impls ~default:(get_current_source_filename (), "type_impls") in
  let (func_decls_filename, func_decls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_func_decls ~default:(get_current_source_filename (), "func_decls") in
  let (func_impls_filename, func_impls_section) = Stdlib.Option.value indimp_mods.indimp_mods_output_func_impls ~default:(get_current_source_filename (), "func_impls") in
  let lazy_type = lazy (gen_indimp_heap_decls (non_void_ind_names ind_names) indimp_mods) in
  let lazy_code = lazy (gen_indimp_heap_impls (non_void_ind_names ind_names) indimp_mods) in
  let type_decls () = let type_decl = Lazy.force lazy_type in Pp.string_of_ppcmds (Pp.v 0 type_decl) in
  let type_impls () = let (type_impls, _func_decls, _func_impls) = Lazy.force lazy_code in Pp.string_of_ppcmds (Pp.v 0 type_impls) in
  let func_decls () = let (_type_impls, func_decls, _func_impls) = Lazy.force lazy_code in Pp.string_of_ppcmds (Pp.v 0 func_decls) in
  let func_impls () = let (_type_impls, _func_decls, func_impls) = Lazy.force lazy_code in Pp.string_of_ppcmds (Pp.v 0 func_impls) in
  codegen_add_generation type_decls_filename (GenThunk (type_decls_section, type_decls));
  codegen_add_generation type_impls_filename (GenThunk (type_impls_section, type_impls));
  codegen_add_generation func_decls_filename (GenThunk (func_decls_section, func_decls));
  codegen_add_generation func_impls_filename (GenThunk (func_impls_section, func_impls));
  ()

let command_indimp (user_coq_type : Constrexpr.constr_expr) (indimp_mods : indimp_mods) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  (* (if ind_coq_type_registered_p coq_type then
    user_err (Pp.str "[codegen] inductive type already configured:" +++ Printer.pr_econstr_env env sigma coq_type)); *)
  match indimp_mods.indimp_mods_heap with
  | Some true ->
      generate_indimp_heap env sigma coq_type indimp_mods
  | Some false ->
      begin
        if ind_recursive_p env sigma coq_type then
          user_err (Pp.str "[codegen] IndImp(heap off) is used for recursive type:" +++ Printer.pr_econstr_env env sigma coq_type);
        (* mutual inductive types are forbidden because mostly they are used for recursive types. *)
        if ind_mutual_p env sigma coq_type then
          user_err (Pp.str "[codegen] IndImp(heap off) is used for mutually defined type:" +++ Printer.pr_econstr_env env sigma coq_type);
        generate_indimp_immediate env sigma coq_type indimp_mods
      end
  | None ->
      if ind_recursive_p env sigma coq_type || ind_mutual_p env sigma coq_type then
        generate_indimp_heap env sigma coq_type indimp_mods
      else
        generate_indimp_immediate env sigma coq_type indimp_mods

