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
    Printer.pr_constr_env env sigma ind_cfg.ind_coq_type +++
    Pp.str (quote_coq_string (compose_c_abstract_decl ind_cfg.ind_c_type)) ++ Pp.str ".")

let pr_inductive_match (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : Pp.t =
  let f cstr_cfg =
    Pp.hv 2 (
      Pp.str "|" +++
      Ppconstr.pr_id cstr_cfg.cstr_id +++
      Pp.str "=>" +++
      (match cstr_cfg.cstr_caselabel with
       | None -> Pp.mt ()
       | Some s -> Pp.str "case" +++ Pp.str (quote_coq_string s)) +++
      (pp_sjoinmap_ary
        (fun accessor ->
          match accessor with
          | None -> Pp.str "_"
          | Some accessor -> Pp.str (quote_coq_string accessor))
        cstr_cfg.cstr_accessors) +++
      (match cstr_cfg.cstr_deallocator with
       | None -> Pp.mt ()
       | Some string_opt_lazy ->
           if Lazy.is_val string_opt_lazy then
             match Lazy.force string_opt_lazy with
             | None -> Pp.mt ()
             | Some s -> Pp.str "deallocator" +++ Pp.str (quote_coq_string s)
           else
             Pp.str "deallocator" +++ Pp.str "(lazy)"))
  in
  match ind_cfg.ind_c_swfunc with
  | Some c_swfunc ->
      Pp.hv 2 (
        Pp.str "CodeGen Inductive Match" +++
          Pp.hv 2 (
            Printer.pr_constr_env env sigma ind_cfg.ind_coq_type +++
            Pp.str "=>" +++
            Pp.str (quote_coq_string c_swfunc))) +++
      pp_sjoinmap_ary f ind_cfg.ind_cstr_configs ++
      Pp.str "."
  | None -> Pp.mt ()

let codegen_print_inductive_match (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  match ind_cfg.ind_c_swfunc with
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
      match ConstrMap.find_opt (EConstr.to_constr sigma coq_type) !ind_config_map with
      | None -> user_err (Pp.str "[codegen] inductive type not registered:" +++
          Printer.pr_econstr_env env sigma coq_type)
      | Some ind_cfg -> codegen_print_inductive1 env sigma ind_cfg)

let get_ind_coq_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) : Declarations.mutual_inductive_body * Declarations.one_inductive_body * Names.inductive puniverses * EConstr.constr array =
  let open Declarations in
  let (f, args) = decompose_appvect sigma coq_type in
  (if not (EConstr.isInd sigma f) then
    user_err (Pp.str "[codegen] inductive type expected:" +++
    Printer.pr_econstr_env env sigma coq_type));
  let pind = EConstr.destInd sigma f in
  let ind, u = pind in
  let (mutind_body, oneind_body) as mind_specif = Inductive.lookup_mind_specif env ind in
  (if mutind_body.mind_nparams <> Array.length args then
    user_err (Pp.str "[codegen] unexpected number of inductive type parameters:" +++
      Pp.int mutind_body.mind_nparams +++ Pp.str "expected but" +++
      Pp.int (Array.length args) +++ Pp.str "given for" +++
      Printer.pr_inductive env ind));
  check_codegen_supported_ind mind_specif;
  (mutind_body, oneind_body, pind, args)

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
  else if not (is_codegen_supported_ind mind_specif) then
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

let register_ind_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.t) (c_type : c_typedata) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma coq_type in
  check_ind_coq_type_not_registered env sigma coq_type;
  if coq_type_is_void_type env sigma coq_type then
    begin
      let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
        Array.map (fun cstrname -> {
            cstr_id = cstrname;
            cstr_caselabel = None;
            cstr_accessors = [||];
            cstr_deallocator = None;
          }) in
      {
        ind_coq_type=EConstr.to_constr sigma coq_type;
        ind_c_type=c_type_void;
        ind_c_swfunc=None;
        ind_cstr_configs=cstr_cfgs;
      }
    end
  else
    begin
      let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
        Array.map (fun cstrname -> {
            cstr_id = cstrname;
            cstr_caselabel = None;
            cstr_accessors = [||];
            cstr_deallocator = None
          }) in
      let coq_type=EConstr.to_constr sigma coq_type in
      let ind_cfg = {
        ind_coq_type=coq_type;
        ind_c_type=c_type;
        ind_c_swfunc=None;
        ind_cstr_configs=cstr_cfgs;
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
     (swfunc : string) (cstr_cfgs : cstr_config list) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma coq_type in
  let ind_cfg = get_ind_config env sigma coq_type in
  (*
  (match ind_cfg.ind_c_swfunc with
  | Some _ -> user_err (
      Pp.str "[codegen] inductive match configuration already registered:" +++
      Printer.pr_econstr_env env sigma coq_type)
  | None -> ());
  *)
  let cstr_caselabel_accessors_ary = reorder_cstrs oneind_body (fun { cstr_id } -> cstr_id) cstr_cfgs in
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
  let ind_cfg =
    { ind_cfg with
      ind_c_swfunc = Some swfunc;
      ind_cstr_configs = CArray.map2_i f ind_cfg.ind_cstr_configs cstr_caselabel_accessors_ary }
  in
  ind_config_map := ConstrMap.add (EConstr.to_constr sigma coq_type) ind_cfg !ind_config_map;
  ind_cfg

let generate_ind_match (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let (mutind_body, oneind_body, pind, args) = get_ind_coq_type env sigma t in
  let printed_type = mangle_term env sigma t in
  let swfunc = "sw_" ^ c_id (squeeze_white_spaces printed_type) in
  let numcons = Array.length oneind_body.Declarations.mind_consnames in
  let cstr_cfgs =
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
          Array.init numargs
            (fun k -> Some (s ^ "_get_member_" ^ string_of_int k))
        in
        { cstr_id=consname; cstr_caselabel=(Some caselabel); cstr_accessors=accessors; cstr_deallocator=None })
  in
  let ind_cfg = register_ind_match env sigma t swfunc cstr_cfgs in
  Feedback.msg_info (Pp.v 2
    (Pp.str "[codegen] match-expression translation automatically configured:" +++
     Pp.hv 0 (pr_inductive_match env sigma ind_cfg)));
  ind_cfg

let ind_is_void_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : bool =
  if isProd sigma t then
    false
  else
    c_type_is_void (get_ind_config env sigma t).ind_c_type

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
  | _ -> (get_ind_config env sigma t).ind_c_type
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
  c_closure_type arg_types (get_ind_config env sigma ret_type).ind_c_type

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
    match ind_cfg.ind_c_swfunc with
    | Some _ -> ind_cfg
    | None -> generate_ind_match env sigma t
  in
  ind_cfg.ind_cstr_configs.(j-1).cstr_caselabel

let case_cstrmember (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) (k : int) : string option =
  let ind_cfg = get_ind_config env sigma t in
  let ind_cfg =
    match ind_cfg.ind_c_swfunc with
    | Some _ -> ind_cfg
    | None -> generate_ind_match env sigma t
  in
  ind_cfg.ind_cstr_configs.(j-1).cstr_accessors.(k)

let case_deallocator (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) : string option =
  let ind_cfg = get_ind_config env sigma t in
  let ind_cfg =
    match ind_cfg.ind_c_swfunc with
    | Some _ -> ind_cfg
    | None -> generate_ind_match env sigma t
  in
  let result =
    match ind_cfg.ind_cstr_configs.(j-1).cstr_deallocator with
    | None -> None
    | Some string_opt_lazy -> Lazy.force string_opt_lazy
  in
  (*
  (let pp = Pp.str "case_deallocator" +++  Printer.pr_econstr_env env sigma t +++ Id.print ind_cfg.ind_cstr_configs.(j-1).cstr_id ++ Pp.str "(j=" ++ Pp.int j ++ Pp.str ")" in
   match result with
   | None -> msg_debug_hov (pp +++ Pp.str "no-deallocator")
   | Some str -> msg_debug_hov (pp +++ Pp.str "deallocator=" ++ Pp.str str));
  *)
  result

let command_ind_match (user_coq_type : Constrexpr.constr_expr) (swfunc : string)
    (cstr_cfgs : cstr_config list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  ignore (register_ind_match env sigma coq_type swfunc cstr_cfgs)
