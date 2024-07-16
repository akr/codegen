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

let c_type_void = { c_type_left = "void"; c_type_right = "" }
let c_type_is_void (c_type : c_typedata) : bool = (c_type = c_type_void)

let codegen_print_inductive_type (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  Feedback.msg_info (Pp.str "CodeGen Inductive Type" +++
    Printer.pr_constr_env env sigma ind_cfg.coq_type +++
    Pp.str (quote_coq_string (compose_c_abstract_decl ind_cfg.c_type)) ++ Pp.str ".")

let pr_inductive_match (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : Pp.t =
  let f cstr_cfg =
    Pp.hv 2 (
      Pp.str "|" +++
      Ppconstr.pr_id cstr_cfg.coq_cstr +++
      Pp.str "=>" +++
      Pp.str (quote_coq_string cstr_cfg.c_caselabel) +++
      pp_sjoinmap_ary
        (fun accessor -> Pp.str (quote_coq_string accessor))
        cstr_cfg.c_accessors)
  in
  match ind_cfg.c_swfunc with
  | Some c_swfunc ->
      Pp.hv 2 (
        Pp.str "CodeGen Inductive Match" +++
          Pp.hv 2 (
            Printer.pr_constr_env env sigma ind_cfg.coq_type +++
            Pp.str "=>" +++
            Pp.str (quote_coq_string c_swfunc))) +++
      pp_sjoinmap_ary f ind_cfg.cstr_configs ++
      Pp.str "."
  | None -> Pp.mt ()

let codegen_print_inductive_match (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  match ind_cfg.c_swfunc with
  | Some c_swfunc -> Feedback.msg_info (pr_inductive_match env sigma ind_cfg)
  | None -> ()

let codegen_print_inductive_deallocator (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  let (f, params) = decompose_appvect sigma (EConstr.of_constr ind_cfg.coq_type) in
  let pind = EConstr.destInd sigma f in
  let deallocs =
    ind_cfg.cstr_configs |> Array.mapi (fun j0 cstr_cfg ->
      let cstr_id = cstr_cfg.coq_cstr in
      let cstr_j = j0 + 1 in
      let cstrterm = mkApp (mkConstructUi (pind, cstr_j), params) in
      let dealloc_opt = ConstrMap.find_opt (EConstr.to_constr sigma cstrterm) !cstr_deallocator_cfunc_map in
      (cstr_id, dealloc_opt))
  in
  (* CodeGen InductiveDeallocator COQ_TYPE ( with ( | CONSTRUCTOR => "C_CSTR_DEALLOCATOR" )* )?. *)
  let deallocs = Array.to_list deallocs |>
    List.filter_map (fun (cstr_id, dealloc_opt) -> match dealloc_opt with None -> None | Some dealloc -> Some (cstr_id, dealloc))
  in
  if not (CList.is_empty deallocs) then
    msg_info_hov (
      Pp.str "CodeGen InductiveDeallocator" +++
      Printer.pr_constr_env env sigma ind_cfg.coq_type +++
      (deallocs |> List.mapi (fun k (cstr_id, dealloc) -> (k, cstr_id, dealloc)) |>
       pp_sjoinmap_list (fun (k, cstr_id, dealloc) ->
         Pp.str (if k = 0 then "with" else "|") +++
         Id.print cstr_id +++ Pp.str "=>" +++ Pp.str (quote_coq_string dealloc))) ++
      Pp.str ".")

let codegen_print_inductive1 (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  codegen_print_inductive_type env sigma ind_cfg;
  codegen_print_inductive_match env sigma ind_cfg;
  codegen_print_inductive_deallocator env sigma ind_cfg

let command_print_inductive (coq_type_list : Constrexpr.constr_expr list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if CList.is_empty coq_type_list then
    ConstrMap.iter (fun key ind_cfg -> codegen_print_inductive1 env sigma ind_cfg) !ind_config_map
  else
    coq_type_list |> List.iter (fun user_coq_type ->
      let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
      match ConstrMap.find_opt (EConstr.to_constr sigma coq_type) !ind_config_map with
      | None -> user_err (Pp.str "[codegen] inductive type not registered:" +++
          Printer.pr_econstr_env env sigma coq_type)
      | Some ind_cfg -> codegen_print_inductive1 env sigma ind_cfg)

let get_ind_coq_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) : Declarations.mutual_inductive_body * Declarations.one_inductive_body * (Names.inductive * EInstance.t) * EConstr.constr array =
  let open Declarations in
  let (f, args) = decompose_appvect sigma coq_type in
  (if not (EConstr.isInd sigma f) then
    user_err (Pp.str "[codegen] inductive type expected:" +++
    Printer.pr_econstr_env env sigma coq_type));
  let pind = EConstr.destInd sigma f in
  let ind, u = pind in
  let (mutind_body, oneind_body) = Inductive.lookup_mind_specif env ind in
  (if mutind_body.mind_nparams <> Array.length args then
    user_err (Pp.str "[codegen] unexpected number of inductive type parameters:" +++
      Pp.int mutind_body.mind_nparams +++ Pp.str "expected but" +++
      Pp.int (Array.length args) +++ Pp.str "given for" +++
      Printer.pr_inductive env ind));
  (if mutind_body.mind_nparams <> mutind_body.mind_nparams_rec then
    user_err (Pp.str "[codegen] inductive type has non-uniform parameters:" +++ Printer.pr_inductive env ind));
  (if oneind_body.mind_nrealargs <> 0 then
    user_err (Pp.str "[codegen] indexed inductive type given:" +++
      Printer.pr_inductive env ind));
  (mutind_body, oneind_body, pind, args)

(* check
 * - coq_type is f args1...argN
 * - f is Ind
 * - f is not conductive
 * - f has N parameters
 * - f has no arguments
 * - ...
 *)
let check_ind_coq_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) : unit =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma coq_type in
  (if mutind_body.Declarations.mind_finite <> Declarations.Finite &&
      mutind_body.Declarations.mind_finite <> Declarations.BiFinite then
        user_err (Pp.str "[codegen] coinductive type not supported:" +++
                 Printer.pr_econstr_env env sigma coq_type));
  ignore oneind_body

let ind_coq_type_registered_p (sigma : Evd.evar_map) (coq_type : EConstr.t) : bool =
  let coq_type = EConstr.to_constr sigma coq_type in
  match ConstrMap.find_opt coq_type !ind_config_map with
  | Some _ -> true
  | None -> false

let check_ind_coq_type_not_registered (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) : unit =
  if ind_coq_type_registered_p sigma coq_type then
    user_err (Pp.str "[codegen] inductive type already registered:" +++
              Printer.pr_econstr_env env sigma coq_type)

let codegen_void_type_memo = Summary.ref (ConstrMap.empty : bool ConstrMap.t) ~name:"CodegenVoidTypeMemo"

let rec coq_type_is_void_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  let coq_type = Reductionops.nf_all env sigma coq_type in
  if EConstr.Vars.closed0 sigma coq_type then
    let key = EConstr.to_constr sigma coq_type in
    match ConstrMap.find_opt key !codegen_void_type_memo with
    | Some b -> b
    | None ->
        codegen_void_type_memo := ConstrMap.add key false !codegen_void_type_memo; (* recursive occurences are considered to be non-void *)
        let b = coq_type_is_void_type1 env sigma coq_type in
        codegen_void_type_memo := ConstrMap.add key b !codegen_void_type_memo;
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
  else if mutind_body.mind_nparams <> mutind_body.mind_nparams_rec then
    false (* inductive type has non-uniform parameters *)
  else if oneind_body.mind_nrealargs <> 0 then
    false (* indexed inductive type *)
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

let register_ind_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) (c_type : c_typedata) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma coq_type in
  check_ind_coq_type_not_registered env sigma coq_type;
  check_ind_coq_type env sigma coq_type;
  if coq_type_is_void_type env sigma coq_type then
    begin
      let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
        Array.map (fun cstrname -> {
          coq_cstr = cstrname;
          c_caselabel = "";
          c_accessors = [||] }) in
      {
        coq_type=EConstr.to_constr sigma coq_type;
        c_type=c_type_void;
        c_swfunc=None;
        cstr_configs=cstr_cfgs;
        is_void_type=true;
      }
    end
  else
    begin
      let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
        Array.map (fun cstrname -> {
          coq_cstr = cstrname;
          c_caselabel = "";
          c_accessors = [||] }) in
      let coq_type=EConstr.to_constr sigma coq_type in
      let ind_cfg = {
        coq_type=coq_type;
        c_type=c_type;
        c_swfunc=None;
        cstr_configs=cstr_cfgs;
        is_void_type=false;
      } in
      ind_config_map := ConstrMap.add coq_type ind_cfg !ind_config_map;
      ind_cfg
    end

let generate_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let printed_type = mangle_term env sigma t in
  let c_name = c_id (squeeze_white_spaces printed_type) in
  let ind_cfg = register_ind_type env sigma t (simple_c_type c_name) in
  Feedback.msg_info (Pp.v 2
    (Pp.str "[codegen] inductive type translation automatically configured:" +++
     (Pp.hv 2 (Pp.str "CodeGen Inductive Type" +++ Printer.pr_econstr_env env sigma t +++
     Pp.str "=>" +++ Pp.str (escape_as_coq_string c_name) ++ Pp.str "."))));
  ind_cfg

let lookup_ind_config (sigma : Evd.evar_map) (t : EConstr.types) : ind_config option =
  ConstrMap.find_opt (EConstr.to_constr sigma t) !ind_config_map

let get_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  match lookup_ind_config sigma t with
  | Some ind_cfg -> ind_cfg
  | None -> generate_ind_config env sigma t

let command_ind_type (user_coq_type : Constrexpr.constr_expr) (c_type : c_typedata) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  ignore (register_ind_type env sigma coq_type c_type)

let reorder_cstrs (oneind_body : Declarations.one_inductive_body) (cstr_of : 'a -> Id.t) (s : 'a list) : 'a array =
  (if List.length s <> Array.length oneind_body.Declarations.mind_consnames then
    user_err (Pp.str "[codegen] invalid number of constructors:" +++
      Pp.str "needs" +++
      Pp.int (Array.length oneind_body.Declarations.mind_consnames) +++
      Pp.str "but" +++
      Pp.int (List.length s)));
  oneind_body.Declarations.mind_consnames |> Array.map (fun consname ->
    match List.find_opt (fun v -> Id.equal consname (cstr_of v)) s with
    | None -> user_err (
      Pp.str "[codegen] constructor not found:" +++
        Id.print consname);
    | Some v -> v)

let register_ind_match (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t)
     (swfunc : string) (cstr_caselabel_accessors_list : ind_cstr_caselabel_accessors list) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma coq_type in
  let ind_cfg = get_ind_config env sigma coq_type in
  (match ind_cfg.c_swfunc with
  | Some _ -> user_err (
      Pp.str "[codegen] inductive match configuration already registered:" +++
      Printer.pr_econstr_env env sigma coq_type)
  | None -> ());
  let cstr_caselabel_accessors_ary = reorder_cstrs oneind_body (fun { cstr_id } -> cstr_id) cstr_caselabel_accessors_list in
  let f j0 cstr_cfg cstr_caselabel_accessors =
    let { cstr_id=cstr; cstr_caselabel=caselabel; cstr_accessors=accessors } = cstr_caselabel_accessors in
    (if oneind_body.Declarations.mind_consnrealdecls.(j0) <> List.length accessors then
      user_err (Pp.str "[codegen] inductive match: invalid number of member accessors:" +++
        Pp.str "needs" +++
        Pp.int oneind_body.Declarations.mind_consnrealdecls.(j0) +++
        Pp.str "but" +++
        Pp.int (List.length accessors) +++
        Pp.str "for" +++
        Id.print cstr_cfg.coq_cstr +++
        Pp.str "of" +++
        Printer.pr_econstr_env env sigma coq_type));
    let caselabel =
      (* delete "default" and "case " for backward compatibility. *)
      if caselabel = "default" then
        ""
      else if CString.is_prefix "case " caselabel then
        String.sub caselabel 5 (String.length caselabel - 5)
      else
        caselabel
    in
    { cstr_cfg with c_caselabel = caselabel; c_accessors = Array.of_list accessors }
  in
  let ind_cfg =
    { ind_cfg with
      c_swfunc = Some swfunc;
      cstr_configs = CArray.map2_i f ind_cfg.cstr_configs cstr_caselabel_accessors_ary }
  in
  ind_config_map := ConstrMap.add (EConstr.to_constr sigma coq_type) ind_cfg !ind_config_map;
  ind_cfg

let generate_ind_match (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma t in
  let printed_type = mangle_term env sigma t in
  let swfunc = "sw_" ^ c_id (squeeze_white_spaces printed_type) in
  let numcons = Array.length oneind_body.Declarations.mind_consnames in
  let cstr_caselabel_accessors_list =
    List.init numcons
      (fun j0 ->
        let j = j0 + 1 in
        let consname = oneind_body.Declarations.mind_consnames.(j0) in
        let cstr = mkConstructUi (pind, j) in
        let consterm = mkApp (cstr, args) in
        let s = mangle_term env sigma consterm in
        let caselabel =
          if j = 1 then "default" else "case " ^ s ^ "_tag"
        in
        let numargs = oneind_body.Declarations.mind_consnrealargs.(j0) in
        let accessors =
          List.init numargs
            (fun k -> s ^ "_get_member_" ^ string_of_int k)
        in
        { cstr_id=consname; cstr_caselabel=caselabel; cstr_accessors=accessors })
  in
  let ind_cfg = register_ind_match env sigma t swfunc cstr_caselabel_accessors_list in
  Feedback.msg_info (Pp.v 2
    (Pp.str "[codegen] match-expression translation automatically configured:" +++
     Pp.hv 0 (pr_inductive_match env sigma ind_cfg)));
  ind_cfg

let ind_is_void_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : bool =
  if isProd sigma t then
    false
  else
    (get_ind_config env sigma t).is_void_type

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
  | _ -> (get_ind_config env sigma t).c_type
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
  c_closure_type arg_types (get_ind_config env sigma ret_type).c_type

let case_swfunc (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : string =
  let ind_cfg = get_ind_config env sigma t in
  match ind_cfg.c_swfunc with
  | Some c_swfunc -> c_swfunc
  | None ->
      match (generate_ind_match env sigma t).c_swfunc with
      | Some c_swfunc -> c_swfunc
      | None -> user_err (Pp.str "[codegen:bug] generate_ind_match doesn't generate c_swfunc")

let case_cstrlabel (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) : string =
  let ind_cfg = get_ind_config env sigma t in
  let ind_cfg =
    match ind_cfg.c_swfunc with
    | Some _ -> ind_cfg
    | None -> generate_ind_match env sigma t
  in
  ind_cfg.cstr_configs.(j-1).c_caselabel

let case_cstrmember (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) (k : int) : string =
  let ind_cfg = get_ind_config env sigma t in
  let ind_cfg =
    match ind_cfg.c_swfunc with
    | Some _ -> ind_cfg
    | None -> generate_ind_match env sigma t
  in
  ind_cfg.cstr_configs.(j-1).c_accessors.(k)

let command_ind_match (user_coq_type : Constrexpr.constr_expr) (swfunc : string)
    (cstr_caselabel_accessors_list : ind_cstr_caselabel_accessors list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  ignore (register_ind_match env sigma coq_type swfunc cstr_caselabel_accessors_list)

let command_deallocator (user_coq_type : Constrexpr.constr_expr) (dealloc_cstr_deallocator_list : dealloc_cstr_deallocator list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  let (mutind_body, oneind_body, pind, params) = get_ind_coq_type env sigma coq_type in
  let dealloc_cstr_deallocator_ary = reorder_cstrs oneind_body (fun { dealloc_cstr_id } -> dealloc_cstr_id) dealloc_cstr_deallocator_list in
  dealloc_cstr_deallocator_ary |> Array.iteri (fun j0 { dealloc_cstr_id; dealloc_cstr_deallocator } ->
    let j = j0 + 1 in
    let cstr_term = EConstr.to_constr sigma (mkApp (mkConstructUi (pind, j), params)) in
    cstr_deallocator_cfunc_map := ConstrMap.add cstr_term dealloc_cstr_deallocator !cstr_deallocator_cfunc_map)
