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

let nf_interp_type (env : Environ.env) (sigma : Evd.evar_map) (t : Constrexpr.constr_expr) : Evd.evar_map * Constr.t =
  let (sigma, t) = Constrintern.interp_type_evars env sigma t in
  let t = Reductionops.nf_all env sigma t in
  let t = EConstr.to_constr sigma t in
  (sigma, t)

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

let codegen_print_inductive1 (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  codegen_print_inductive_type env sigma ind_cfg;
  codegen_print_inductive_match env sigma ind_cfg

let command_print_inductive (coq_type_list : Constrexpr.constr_expr list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if CList.is_empty coq_type_list then
    ConstrMap.iter (fun key ind_cfg -> codegen_print_inductive1 env sigma ind_cfg) !ind_config_map
  else
    coq_type_list |> List.iter (fun user_coq_type ->
      let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
      match ConstrMap.find_opt coq_type !ind_config_map with
      | None -> user_err (Pp.str "[codegen] inductive type not registered:" +++
          Printer.pr_constr_env env sigma coq_type)
      | Some ind_cfg -> codegen_print_inductive1 env sigma ind_cfg)

let get_ind_coq_type (env : Environ.env) (coq_type : Constr.t) : MutInd.t * Declarations.mutual_inductive_body * int * Declarations.one_inductive_body * Constr.constr array * UVars.Instance.t =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (f, args) = Constr.decompose_app coq_type in
  (if not (Constr.isInd f) then
    user_err (Pp.str "[codegen] inductive type expected:" +++
    Printer.pr_constr_env env sigma coq_type));
  let ind, u = Constr.destInd f in
  let (mutind, i) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  (mutind, mutind_body, i, oneind_body, args, u)

(* check
 * - coq_type is f args1...argN
 * - f is Ind
 * - f is not conductive
 * - f has N parameters
 * - f has no arguments
 * - ...
 *)
let check_ind_coq_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : Constr.t) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (mutind, mutind_body, i, oneind_body, args, u) = get_ind_coq_type env coq_type in
  (if mutind_body.Declarations.mind_finite <> Declarations.Finite &&
      mutind_body.Declarations.mind_finite <> Declarations.BiFinite then
        user_err (Pp.str "[codegen] coinductive type not supported:" +++
                 Printer.pr_constr_env env sigma coq_type));
  ignore oneind_body

let ind_coq_type_registered_p (coq_type : Constr.t) : bool =
  match ConstrMap.find_opt coq_type !ind_config_map with
  | Some _ -> true
  | None -> false

let check_ind_coq_type_not_registered (coq_type : Constr.t) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if ind_coq_type_registered_p coq_type then
    user_err (Pp.str "[codegen] inductive type already registered:" +++
              Printer.pr_constr_env env sigma coq_type)

let check_void_type (env : Environ.env) (sigma : Evd.evar_map) (mind_body : Declarations.mutual_inductive_body) (ty : Constr.types) : unit =
  let open Declarations in
  (if Array.length mind_body.mind_packets <> 1 then
    user_err (Pp.str "[codegen] non-mutual inductive type expected for void type:" +++ Printer.pr_constr_env env sigma ty));
  (if mind_body.mind_nparams <> 0 then
    (* This "no parameters" constraint is not mandatory.
       However it makes us easy to determine constructor invocation in code generation
       because constructor with parameters is wrapped as a constant.  *)
    user_err (Pp.str "[codegen] void type must not have no inductive type parameters:" +++ Printer.pr_constr_env env sigma ty));
  let oind_body = mind_body.mind_packets.(0) in
  (if oind_body.mind_nrealargs <> 0 then
    user_err (Pp.str "[codegen] non-indexed type expected for void type:" +++ Printer.pr_constr_env env sigma ty));
  (if Array.length oind_body.mind_consnames <> 1 then
    user_err (Pp.str "[codegen] single constructor inductive type expected for void type:" +++ Printer.pr_constr_env env sigma ty +++
    Pp.str "has" +++ Pp.int (Array.length oind_body.mind_consnames) +++ Pp.str "constructors"));
  (if oind_body.mind_consnrealargs.(0) <> 0 then
    user_err (Pp.str "[codegen] no-argument constructor expected for void type:" +++
      Id.print oind_body.mind_consnames.(0) +++
      Pp.str "of" +++
      Printer.pr_constr_env env sigma ty))

let register_ind_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : Constr.t) (c_type : c_typedata) : ind_config =
  let (mutind, mutind_body, i, oneind_body, args, u) = get_ind_coq_type env coq_type in
  check_ind_coq_type_not_registered coq_type;
  check_ind_coq_type env sigma coq_type;
  let is_void_type = c_type_is_void c_type in
  (if is_void_type then
    check_void_type env sigma mutind_body coq_type);
  let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
    Array.map (fun cstrname -> {
      coq_cstr = cstrname;
      c_caselabel = "";
      c_accessors = [||] }) in
  let ind_cfg = {
    coq_type=coq_type;
    c_type=c_type;
    c_swfunc=None;
    cstr_configs=cstr_cfgs;
    is_void_type=is_void_type;
  } in
  ind_config_map := ConstrMap.add coq_type ind_cfg !ind_config_map;
  ind_cfg

let generate_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let printed_type = mangle_term env sigma t in
  let c_name = c_id (squeeze_white_spaces printed_type) in
  let ind_cfg = register_ind_type env sigma (EConstr.to_constr sigma t) (simple_c_type c_name) in
  Feedback.msg_info (Pp.v 2
    (Pp.str "[codegen] inductive type translation automatically configured:" +++
     (Pp.hv 2 (Pp.str "CodeGen Inductive Type" +++ Printer.pr_econstr_env env sigma t +++
     Pp.str "=>" +++ Pp.str (escape_as_coq_string c_name) ++ Pp.str "."))));
  ind_cfg

let lookup_ind_config (t : Constr.types) : ind_config option =
  ConstrMap.find_opt t !ind_config_map

let get_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  match lookup_ind_config (EConstr.to_constr sigma t) with
  | Some ind_cfg -> ind_cfg
  | None -> generate_ind_config env sigma t

let command_ind_type (user_coq_type : Constrexpr.constr_expr) (c_type_left : string) (c_type_right : string) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  ignore (register_ind_type env sigma coq_type { c_type_left; c_type_right })

let register_ind_match (env : Environ.env) (sigma : Evd.evar_map) (coq_type : Constr.t)
     (swfunc : string) (cstr_caselabel_accessors_list : ind_cstr_caselabel_accessors list) : ind_config =
  let (mutind, mutind_body, i, oneind_body, args, u) = get_ind_coq_type env coq_type in
  let ind_cfg = get_ind_config env sigma (EConstr.of_constr coq_type) in
  (match ind_cfg.c_swfunc with
  | Some _ -> user_err (
      Pp.str "[codegen] inductive match configuration already registered:" +++
      Printer.pr_constr_env env sigma coq_type)
  | None -> ());
  (if List.length cstr_caselabel_accessors_list <> Array.length oneind_body.Declarations.mind_consnames then
    user_err (Pp.str "[codegen] inductive match: invalid number of constructors:" +++
      Pp.str "needs" +++
      Pp.int (Array.length oneind_body.Declarations.mind_consnames) +++
      Pp.str "but" +++
      Pp.int (List.length cstr_caselabel_accessors_list)));
  let f j0 cstr_cfg =
    let consname = oneind_body.Declarations.mind_consnames.(j0) in
    let p (cstr, caselabel, accessors) = Id.equal consname cstr in
    let cstr_caselabel_accessors_opt = List.find_opt p cstr_caselabel_accessors_list in
    let (cstr, caselabel, accessors) = (match cstr_caselabel_accessors_opt with
      | None -> user_err (
        Pp.str "[codegen] inductive match: constructor not found:" +++
        Id.print consname);
      | Some cstr_caselabel_accessors -> cstr_caselabel_accessors) in
    (if oneind_body.Declarations.mind_consnrealdecls.(j0) <> List.length accessors then
      user_err (Pp.str "[codegen] inductive match: invalid number of member accessors:" ++
      Pp.str "needs" +++
      Pp.int oneind_body.Declarations.mind_consnrealdecls.(j0) +++
      Pp.str "but" +++
      Pp.int (List.length accessors) +++
      Pp.str "for" +++
      Id.print cstr_cfg.coq_cstr +++
      Pp.str "of" +++
      Printer.pr_constr_env env sigma coq_type));
    { cstr_cfg with c_caselabel = caselabel; c_accessors = Array.of_list accessors }
  in
  let ind_cfg =
    { ind_cfg with
      c_swfunc = Some swfunc;
      cstr_configs = Array.mapi f ind_cfg.cstr_configs }
  in
  ind_config_map := ConstrMap.add coq_type ind_cfg !ind_config_map;
  ind_cfg

let generate_ind_match (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let (mutind, mutind_body, i, oneind_body, args, u) = get_ind_coq_type env (EConstr.to_constr sigma t) in
  let u' = EInstance.make u in
  let printed_type = mangle_term env sigma t in
  let swfunc = "sw_" ^ c_id (squeeze_white_spaces printed_type) in
  let numcons = Array.length oneind_body.Declarations.mind_consnames in
  let cstr_caselabel_accessors_list =
    List.init numcons
      (fun j0 ->
        let j = j0 + 1 in
        let consname = oneind_body.Declarations.mind_consnames.(j0) in
        let cstr = mkConstructU (((mutind, i), j), u') in
        let args = Array.map EConstr.of_constr args in
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
        (consname, caselabel, accessors))
  in
  let ind_cfg = register_ind_match env sigma (EConstr.to_constr sigma t) swfunc cstr_caselabel_accessors_list in
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

let coq_type_is_void (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : bool =
  match EConstr.kind sigma t with
  | Prod _ -> false
  | _ ->
      match lookup_ind_config (EConstr.to_constr sigma t) with
      | Some ind_cfg -> c_type_is_void ind_cfg.c_type
      | None -> false (* The Coq type is not registered (yet).  We consider it non-void.  It may be registed as void later, though. *)

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
