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
(*open Globnames*)
open CErrors
open Constr
open EConstr

open Cgenutil
open State
(*open Linear*)
open Specialize

let c_type_void = { c_type_left = "void"; c_type_right = "" }
let c_type_is_void (c_type : c_typedata) : bool = (c_type = c_type_void)

let pr_codegen_indtype (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : Pp.t =
  let pp_coq_type = Printer.pr_lconstr_env env sigma ind_cfg.ind_coq_type in
  let pp_c_type =
    match ind_cfg.ind_c_type with
    | None -> Pp.mt ()
    | Some { c_type_left; c_type_right } ->
        if CString.is_empty c_type_right then
          Pp.str (quote_coq_string c_type_left)
        else
          Pp.str (quote_coq_string c_type_left) +++ Pp.str (quote_coq_string c_type_right)
  in
  let pp_swfunc =
    match ind_cfg.ind_c_swfunc with
    | None -> Pp.mt ()
    | Some swfunc -> Pp.str "swfunc" +++ Pp.str (quote_coq_string swfunc)
  in
  let pp_cstrs =
    pp_sjoinmap_ary
      (fun cstr_cfg ->
        let pp_caselabel =
          match cstr_cfg.cstr_caselabel with None -> Pp.mt () | Some caselabel -> Pp.str "case" +++ Pp.str (quote_coq_string caselabel)
        in
        let pp_accessors =
          if Array.for_all Stdlib.Option.is_none cstr_cfg.cstr_accessors then
            Pp.mt ()
          else
            Pp.str "accessor" +++
            pp_sjoinmap_ary
              (fun str_opt ->
                match str_opt with
                | None -> Pp.str "_"
                | Some accessor -> Pp.str (quote_coq_string accessor))
              cstr_cfg.cstr_accessors
        in
        let pp_deallocator =
          match cstr_cfg.cstr_deallocator with
          | None -> Pp.mt ()
          | Some deallocator -> Pp.str "deallocator" +++ Pp.str (quote_coq_string deallocator)
        in
        let pp_cfg = pp_caselabel +++ pp_accessors +++ pp_deallocator in
        if Pp.ismt pp_cfg then
          Pp.mt ()
        else
          Pp.hov 0 (Pp.str "|" +++ Id.print cstr_cfg.cstr_id +++ Pp.str "=>" +++ pp_cfg))
      ind_cfg.ind_cstr_configs
  in
  let pp_with =
    if Pp.ismt pp_cstrs then
      Pp.mt ()
    else
      Pp.str "with"
  in
  let pp =
    Pp.hv 0 (
      Pp.hov 0 (Pp.str "CodeGen IndType" +++ pp_coq_type +++ Pp.str "=>" +++ pp_c_type +++ pp_swfunc +++ pp_with) +++
      pp_cstrs ++ Pp.str ".")
  in
  pp

let codegen_print_inductive_type (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  Feedback.msg_info (pr_codegen_indtype env sigma ind_cfg)

let command_print_inductive (coq_type_list : Constrexpr.constr_expr list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if CList.is_empty coq_type_list then
    ConstrMap.iter (fun key ind_cfg -> codegen_print_inductive_type env sigma ind_cfg) (get_ind_config_map ())
  else
    coq_type_list |> List.iter (fun user_coq_type ->
      let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
      match ConstrMap.find_opt (EConstr.to_constr sigma coq_type) (get_ind_config_map ()) with
      | None -> user_err (Pp.str "[codegen] inductive type not registered:" +++
          Printer.pr_econstr_env env sigma coq_type)
      | Some ind_cfg -> codegen_print_inductive_type env sigma ind_cfg)

let get_ind_coq_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) : Declarations.mutual_inductive_body * Declarations.one_inductive_body * Names.inductive puniverses * EConstr.constr array =
  check_codegen_supported_type env sigma coq_type;
  let (f, args) = decompose_appvect sigma coq_type in
  (if not (EConstr.isInd sigma f) then
    user_err (Pp.str "[codegen] inductive type expected:" +++
    Printer.pr_econstr_env env sigma coq_type));
  let pind = EConstr.destInd sigma f in
  let ind, u = pind in
  let (mutind_body, oneind_body) as mind_specif = Inductive.lookup_mind_specif env ind in
  (mutind_body, oneind_body, pind, args)

let ind_coq_type_registered_p (sigma : Evd.evar_map) (coq_type : EConstr.t) : bool =
  let coq_type = EConstr.to_constr sigma coq_type in
  match ConstrMap.find_opt coq_type (get_ind_config_map ()) with
  | Some _ -> true
  | None -> false

let check_ind_coq_type_not_registered (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) : unit =
  if ind_coq_type_registered_p sigma coq_type then
    user_err (Pp.str "[codegen] inductive type already registered:" +++
              Printer.pr_econstr_env env sigma coq_type)

let codegen_void_type_memo = Summary.ref (ConstrMap.empty : bool ConstrMap.t) ~name:"CodegenVoidTypeMemo"

let add_codegen_void_type_memo (key, b) = codegen_void_type_memo := ConstrMap.add key b !codegen_void_type_memo

let rec coq_type_is_void_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  let coq_type = Reductionops.nf_all env sigma coq_type in
  if EConstr.Vars.closed0 sigma coq_type then
    let key = EConstr.to_constr sigma coq_type in
    match ConstrMap.find_opt key !codegen_void_type_memo with
    | Some b -> b
    | None ->
        add_codegen_void_type_memo (key, false); (* recursive occurences are considered to be non-void *)
        let b = coq_type_is_void_type1 env sigma coq_type in
        add_codegen_void_type_memo (key, b);
        b
  else
    coq_type_is_void_type1 env sigma coq_type
and coq_type_is_void_type1 (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  let open Declarations in
  let (f, args) = decompose_appvect sigma coq_type in
  if not (EConstr.isInd sigma f) then
    false (* inductive type expected *)
  else
  let pind = EConstr.destInd sigma f in
  let ind, u = pind in
  let (mutind_body, oneind_body) as mind_specif = Inductive.lookup_mind_specif env ind in
  if mutind_body.mind_nparams <> Array.length args then
    false (* unexpected number of inductive type parameters *)
  else if not (is_codegen_supported_type env sigma coq_type) then
    false (* not supported by codegen *)
  else if Array.length oneind_body.mind_consnames <> 1 then
    false (* single constructor inductive type expected *)
  else if not (arities_of_constructors sigma pind mind_specif |> Array.for_all (fun cstr_ty ->
    let (rel_ctx, ret_type) = decompose_prod_decls sigma cstr_ty in cstr_args_are_void_types env sigma rel_ctx args)) then
    false
  else
    true
and cstr_args_are_void_types (env : Environ.env) (sigma : Evd.evar_map) (nf_lc_ctx : EConstr.rel_context) (args : EConstr.t array) : bool =
  try
    ind_nf_lc_iter env sigma nf_lc_ctx (Array.to_list args)
      (fun env2 arg_ty ->
        if coq_type_is_void_type env2 sigma arg_ty then
          ()
        else
          raise Exit;
        None);
    true
  with Exit -> false

let register_empty_ind_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma coq_type in
  check_ind_coq_type_not_registered env sigma coq_type;
  let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
    Array.map (fun cstrname -> {
        cstr_id = cstrname;
        cstr_caselabel = None;
        cstr_accessors = [||];
        cstr_deallocator = None
      }) in
  let coq_type = EConstr.to_constr sigma coq_type in
  let ind_cfg = {
    ind_coq_type = coq_type;
    ind_c_type = None;
    ind_c_swfunc = None;
    ind_cstr_configs = cstr_cfgs;
  } in
  add_ind_config coq_type ind_cfg;
  ind_cfg

let lookup_ind_config (sigma : Evd.evar_map) (t : EConstr.types) : ind_config option =
  ConstrMap.find_opt (EConstr.to_constr sigma t) (get_ind_config_map ())

let get_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  match lookup_ind_config sigma t with
  | Some ind_cfg -> ind_cfg
  | None -> register_empty_ind_type env sigma t

let register_ind_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (c_type : c_typedata) : ind_config =
  let ind_cfg =
    match lookup_ind_config sigma t with
    | None -> register_empty_ind_type env sigma t
    | Some ind_cfg -> ind_cfg
  in
  match ind_cfg.ind_c_type with
  | None ->
      let ind_cfg2 = { ind_cfg with ind_c_type = Some c_type } in
      let coq_type = EConstr.to_constr sigma t in
      add_ind_config coq_type ind_cfg2;
      ind_cfg2
  | Some c_type ->
      user_err (Pp.str "[codegen] c_type already registered:" +++ Printer.pr_econstr_env env sigma t +++ Pp.str "=>" +++ pr_c_abstract_decl c_type)

let reorder_cstrs (oneind_body : Declarations.one_inductive_body) (make_default : Id.t -> 't) (cstr_of : 't -> Id.t) (s : 't list) : 't array =
  (let unexpected_cstr_ids =
    s |> List.filter_map (fun x ->
      let cstr_id = cstr_of x in
      if Array.exists (Id.equal cstr_id) oneind_body.Declarations.mind_consnames then
        None
      else
        Some cstr_id)
  in
  if not (CList.is_empty unexpected_cstr_ids) then
    user_err ( Pp.str "[codegen] unexpected constructor:" +++ pp_sjoinmap_list Id.print unexpected_cstr_ids));
  begin
    let cstr_id_counts =
      List.fold_left
        (fun m x -> let cstr_id = cstr_of x in Id.Map.add cstr_id (1 + Stdlib.Option.value (Id.Map.find_opt cstr_id m) ~default:0) m)
        Id.Map.empty
        s
    in
    let duplicated_cstr_ids =
      (Id.Map.bindings cstr_id_counts) |> List.filter_map (fun (cstr_id, n) -> if 1 < n then Some cstr_id else None)
    in
    if not (CList.is_empty duplicated_cstr_ids) then
      user_err ( Pp.str "[codegen] constructor specified multiple times:" +++ pp_sjoinmap_list Id.print duplicated_cstr_ids)
  end;
  oneind_body.Declarations.mind_consnames |> Array.map (fun consname ->
    match List.find_opt (fun v -> Id.equal consname (cstr_of v)) s with
    | None -> make_default consname
    | Some v -> v)

let generate_ind_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let c_type =
    if coq_type_is_void_type env sigma t then
      c_type_void
    else
      let printed_type = mangle_term env sigma t in
      let c_name = c_id (squeeze_white_spaces printed_type) in
      simple_c_type c_name
  in
  register_ind_type env sigma t c_type

let get_or_gen_c_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : c_typedata =
  if isProd sigma t then
    user_err (Pp.str "[codegen:get_or_gen_c_type] function type given:" +++ Printer.pr_econstr_env env sigma t)
  else
    match (get_ind_config env sigma t).ind_c_type with
    | Some c_type -> c_type
    | None ->
        match (generate_ind_type env sigma t).ind_c_type with
        | Some c_type -> c_type
        | None -> user_err (Pp.str "[codegen:bug] generate_ind_type doesn't generate c_type")

let ind_is_void_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : bool =
  if isProd sigma t then
    false
  else
    c_type_is_void (get_or_gen_c_type env sigma t)

let c_closure_type (arg_types : c_typedata list) (ret_type : c_typedata) : c_typedata =
  let arg_types =
    rcons
      (List.filter (fun c_ty -> not (c_type_is_void c_ty)) arg_types)
      { c_type_left="void *"; c_type_right="" } (* closure invocation pass the closure itself as the last argument *)
  in
  let arg_abstract_decls = List.map compose_c_abstract_decl arg_types in
  (* closure type in C is a pointer to pointer to function that is actually
     pointer to the first member of closure struct where the first member is a pointer to a function  *)
  let declarator_left = "" in
  let declarator_right = "(" ^ String.concat ", " arg_abstract_decls ^ ")" in
  compose_c_type ret_type declarator_left declarator_right

let rec c_typename (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : c_typedata =
  match EConstr.kind sigma t with
  | Prod _ -> c_type_pointer_to (c_type_pointer_to (c_closure_function_type env sigma t))
  | _ -> get_or_gen_c_type env sigma t
and c_closure_function_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : c_typedata =
  let (args, ret_type) = decompose_prod sigma t in
  let arg_types =
    List.rev_map
      (fun (x, ty) ->
        if Vars.closed0 sigma ty then
          c_typename env sigma ty
        else
          user_err (Pp.str "[codegen] dependent type given for c_typename:" +++ Printer.pr_econstr_env env sigma t))
      args
  in
  c_closure_type arg_types (get_or_gen_c_type env sigma ret_type)

let register_ind_match (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t)
     (swfunc_opt : string option) (cstr_cfgs : cstr_config list) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma coq_type in
  let ind_cfg = get_ind_config env sigma coq_type in
  (*
  (match ind_cfg.ind_c_swfunc with
  | Some _ -> user_err (
      Pp.str "[codegen] inductive match configuration already registered:" +++
      Printer.pr_econstr_env env sigma coq_type)
  | None -> ());
  *)
  let cstr_caselabel_accessors_ary = reorder_cstrs oneind_body (fun cstr_id -> { cstr_id; cstr_caselabel=None; cstr_accessors=[||]; cstr_deallocator=None }) (fun { cstr_id } -> cstr_id) cstr_cfgs in
  let f j0 cstr_cfg { cstr_id=cstr; cstr_caselabel=caselabel; cstr_accessors=accessors; cstr_deallocator=deallocator } =
    let num_members = oneind_body.Declarations.mind_consnrealargs.(j0) in
    (if num_members < Array.length accessors then
      user_err (Pp.str "[codegen] inductive match: too many member accessors:" +++
        Pp.str "needs" +++
        Pp.int oneind_body.Declarations.mind_consnrealargs.(j0) +++
        Pp.str "but" +++
        Pp.int (Array.length accessors) +++
        Pp.str "for" +++
        Id.print cstr_cfg.cstr_id +++
        Pp.str "of" +++
        Printer.pr_econstr_env env sigma coq_type));
    let accessors =
      if Array.length accessors = num_members then
        accessors
      else
        Array.init num_members (fun i -> if i < Array.length accessors then accessors.(i) else None)
    in
    let caselabel =
      match caselabel with
      | None -> None
      | Some caselabel ->
          (* delete "default" and "case " for backward compatibility. *)
          if caselabel = "default" then
            Some ""
          else if CString.is_prefix "case " caselabel then
            Some (String.sub caselabel 5 (String.length caselabel - 5))
          else
            Some caselabel
    in
    { cstr_cfg with cstr_caselabel = caselabel; cstr_accessors = accessors; cstr_deallocator = deallocator }
  in
  let swfunc_opt =
    match swfunc_opt, ind_cfg.ind_c_swfunc with
    | Some _, Some _ -> user_err (
        Pp.str "[codegen] inductive swfunc configuration already registered:" +++
        Printer.pr_econstr_env env sigma coq_type)
    | Some swfunc, None -> Some swfunc
    | None, Some swfunc -> Some swfunc
    | None, None -> None
  in
  let ind_cfg =
    { ind_cfg with
      ind_c_swfunc = swfunc_opt;
      ind_cstr_configs = CArray.map2_i f ind_cfg.ind_cstr_configs cstr_caselabel_accessors_ary }
  in
  add_ind_config (EConstr.to_constr sigma coq_type) ind_cfg;
  ind_cfg

let command_ind_type (user_coq_type : Constrexpr.constr_expr) (indtype_ind_args : c_typedata option * string option) (cstr_mods : (Id.t * cstr_mod) list) : unit =
  let cstr_cfgs =
    cstr_mods |> List.map (fun (cstr_id, { cm_caselabel; cm_accessors; cm_deallocator }) ->
      { cstr_id; cstr_caselabel = cm_caselabel; cstr_accessors = cm_accessors; cstr_deallocator = cm_deallocator })
  in
  let (c_type_opt, swfunc_opt) = indtype_ind_args in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  (match c_type_opt with
  | None -> ()
  | Some c_type -> ignore (register_ind_type env sigma coq_type c_type));
  ignore (register_ind_match env sigma coq_type swfunc_opt cstr_cfgs);
  let (indterm, params) = decompose_appvect sigma coq_type in
  let (ind, _u) as pind = destInd sigma indterm in
  let (mutind_body, oneind_body) = Inductive.lookup_mind_specif env ind in
  let cstr_interface_list = cstr_mods |> List.map (fun (cstr_id, { cm_interface }) -> (cstr_id, cm_interface)) in
  let cstr_interface_ary = reorder_cstrs oneind_body (fun cstr_id -> (cstr_id, None)) (fun (cstr_id, _) -> cstr_id) cstr_interface_list in
  cstr_interface_ary |> Array.iteri (fun j0 (cstr_id, cstr_interface) ->
    let j = j0 + 1 in
    let cstr = mkConstructUi (pind, j) in
    let params' = Array.map (fun param -> Some param) params in
    match cstr_interface with
    | None -> ()
    | Some (CiPrimitive c_name) ->
        let names = { spi_cfunc_name = Some c_name; spi_presimp_id = None; spi_simplified_id = None } in
        ignore (codegen_instance_command_primitive env sigma cstr params' (Some names))
    | Some (CiConstant c_name) ->
        let names = { spi_cfunc_name = Some c_name; spi_presimp_id = None; spi_simplified_id = None } in
        ignore (codegen_instance_command_constant env sigma cstr params' (Some names))
    | Some CiNoFunc ->
        ignore (codegen_instance_command_nofunc env sigma cstr params' None));
  ()

let generate_ind_match (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let ind_cfg0 = get_ind_config env sigma t in
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma t in
  let printed_type = mangle_term env sigma t in
  let swfunc_opt = match ind_cfg0.ind_c_swfunc with None -> Some ("sw_" ^ c_id (squeeze_white_spaces printed_type)) |  Some _ -> None in
  let numcons = Array.length oneind_body.Declarations.mind_consnames in
  let cstr_cfgs =
    List.init numcons
      (fun j0 ->
        let j = j0 + 1 in
        let cstr_cfg0 = ind_cfg0.ind_cstr_configs.(j0) in
        let consname = oneind_body.Declarations.mind_consnames.(j0) in
        let cstr = mkConstructUi (pind, j) in
        let consterm = mkApp (cstr, args) in
        let s = mangle_term env sigma consterm in
        let caselabel =
          match cstr_cfg0.cstr_caselabel with
          | None -> Some (s ^ "_tag")
          | Some caselabel -> Some caselabel
        in
        let numargs = oneind_body.Declarations.mind_consnrealargs.(j0) in
        let accessors0 = cstr_cfg0.cstr_accessors in
        let accessors =
          Array.init numargs
            (fun k ->
              match if Array.length accessors0 <= k then None else accessors0.(k) with
              | None -> Some (s ^ "_get_member_" ^ string_of_int k)
              | Some accessor -> Some accessor)
        in
        { cstr_id=consname; cstr_caselabel=caselabel; cstr_accessors=accessors; cstr_deallocator=cstr_cfg0.cstr_deallocator })
  in
  let ind_cfg = register_ind_match env sigma t swfunc_opt cstr_cfgs in
  Feedback.msg_info (Pp.v 2
    (Pp.str "[codegen] match-expression translation automatically configured:" +++
     Pp.hv 0 (pr_codegen_indtype env sigma ind_cfg)));
  ind_cfg

let case_swfunc (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : string =
  let ind_cfg = get_ind_config env sigma t in
  match ind_cfg.ind_c_swfunc with
  | Some c_swfunc -> c_swfunc
  | None ->
      match (generate_ind_match env sigma t).ind_c_swfunc with
      | Some c_swfunc -> c_swfunc
      | None -> user_err (Pp.str "[codegen:bug] generate_ind_match doesn't generate c_swfunc")

let case_cstrlabel (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) : string option =
  let ind_cfg = get_ind_config env sigma t in
  let ind_cfg =
    match ind_cfg.ind_cstr_configs.(j-1).cstr_caselabel with
    | Some _ -> ind_cfg
    | None -> generate_ind_match env sigma t
  in
  ind_cfg.ind_cstr_configs.(j-1).cstr_caselabel

let case_cstrmember (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) (k : int) : string option =
  let ind_cfg = get_ind_config env sigma t in
  let ind_cfg =
    let cstr_accessors = ind_cfg.ind_cstr_configs.(j-1).cstr_accessors in
    if Array.length cstr_accessors <= k || Stdlib.Option.is_none cstr_accessors.(k) then
      generate_ind_match env sigma t
    else
      ind_cfg
  in
  let cstr_accessors = ind_cfg.ind_cstr_configs.(j-1).cstr_accessors in
  if Array.length cstr_accessors <= k then
    None
  else
    cstr_accessors.(k)

let case_deallocator (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) : string option =
  let ind_cfg = get_ind_config env sigma t in
  let result =
    match ind_cfg.ind_cstr_configs.(j-1).cstr_deallocator with
    | None -> None
    | Some deallocator -> Some deallocator
  in
  (*
  (let pp = Pp.str "case_deallocator" +++  Printer.pr_econstr_env env sigma t +++ Id.print ind_cfg.ind_cstr_configs.(j-1).cstr_id ++ Pp.str "(j=" ++ Pp.int j ++ Pp.str ")" in
   match result with
   | None -> msg_debug_hov (pp +++ Pp.str "no-deallocator")
   | Some str -> msg_debug_hov (pp +++ Pp.str "deallocator=" ++ Pp.str str));
  *)
  result

let command_test_has_ind_config (user_coq_type : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  let ind_config_map = get_ind_config_map () in
  if ConstrMap.mem (EConstr.to_constr sigma coq_type) ind_config_map then
    ()
  else
    user_err (Pp.str "[codegen] inductive type configuration not found:" +++ Printer.pr_econstr_env env sigma coq_type)
