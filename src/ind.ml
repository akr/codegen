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
open Pp
open CErrors

open Cgenutil
(*open Linear*)

let quote_coq_string s =
  let buf = Buffer.create (String.length s + 2) in
  let rec f i =
    match String.index_from_opt s i '"' with
    | None ->
        Buffer.add_substring buf s i (String.length s - i)
    | Some j ->
        Buffer.add_substring buf s i (j - i);
        Buffer.add_string buf "\"\"";
        f (j+1)
  in
  Buffer.add_char buf '"';
  f 0;
  Buffer.add_char buf '"';
  Buffer.contents buf

let nf_interp_constr env sigma t =
  let (sigma, t) = Constrintern.interp_constr_evars env sigma t in
  let t = Reductionops.nf_all env sigma t in
  let t = EConstr.to_constr sigma t in
  (sigma, t)

module ConstrMap = Map.Make(Constr)
let ind_config_map = Summary.ref (ConstrMap.empty : ind_config ConstrMap.t) ~name:"CodegenIndInfo"

let codegen_print_inductive_type env sigma ind_cfg =
  Feedback.msg_info (str "CodeGen Inductive Type" ++ spc () ++
    Printer.pr_constr_env env sigma ind_cfg.coq_type ++ spc () ++
    str (quote_coq_string ind_cfg.c_type) ++ str ".")

let codegen_print_inductive_constructor env sigma ind_cfg cstr_cfg =
  match cstr_cfg.c_cstr with
  | Some c_cstr ->
    Feedback.msg_info (str "CodeGen Inductive Constructor" ++ spc () ++
      Printer.pr_constr_env env sigma ind_cfg.coq_type ++ spc () ++
      Ppconstr.pr_id cstr_cfg.coq_cstr ++ spc () ++
      str (quote_coq_string c_cstr) ++ str ".")
  | None -> ()

let codegen_print_inductive_match env sigma ind_cfg =
  let f cstr_cfg =
     Ppconstr.pr_id cstr_cfg.coq_cstr ++ spc () ++
     str (quote_coq_string cstr_cfg.c_caselabel) ++ pp_prejoin_ary (spc ())
       (Array.map (fun accessor -> str (quote_coq_string accessor))
         cstr_cfg.c_accessors)
  in
  match ind_cfg.c_swfunc with
  | Some c_swfunc ->
      Feedback.msg_info (str "CodeGen Inductive Match" ++ spc () ++
        Printer.pr_constr_env env sigma ind_cfg.coq_type ++ spc () ++
        str (quote_coq_string c_swfunc) ++ pp_prejoin_ary (spc ())
          (Array.map f ind_cfg.cstr_configs))
  | None -> ()

let codegen_print_inductive1 env sigma ind_cfg =
  codegen_print_inductive_type env sigma ind_cfg;
  Array.iter (codegen_print_inductive_constructor env sigma ind_cfg)
    ind_cfg.cstr_configs;
  codegen_print_inductive_match env sigma ind_cfg

let codegen_print_inductive coq_type_list =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if coq_type_list = [] then
    ConstrMap.iter (fun key ind_cfg -> codegen_print_inductive1 env sigma ind_cfg) !ind_config_map
  else
    coq_type_list |> List.iter (fun user_coq_type ->
      let (sigma, coq_type) = nf_interp_constr env sigma user_coq_type in
      match ConstrMap.find_opt coq_type !ind_config_map with
      | None -> user_err (Pp.str "inductive type not registered:" ++
          Pp.spc () ++ Printer.pr_constr_env env sigma coq_type)
      | Some ind_cfg -> codegen_print_inductive1 env sigma ind_cfg)

let get_ind_coq_type env coq_type =
  let (f, args) = Constr.decompose_app coq_type in
  (if not (Constr.isInd f) then raise (CodeGenError "not an inductive type"));
  let ind = Univ.out_punivs (Constr.destInd f) in
  let (mutind, i) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  (mutind_body, i, oneind_body, args)

(* check
 * - coq_type is f args1...argN
 * - f is Ind
 * - f is not conductive
 * - f has N parameters
 * - f has no arguments
 * - ...
 *)
let check_ind_coq_type env sigma coq_type =
  let (mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  (if mutind_body.Declarations.mind_finite <> Declarations.Finite &&
      mutind_body.Declarations.mind_finite <> Declarations.BiFinite then
       raise (CodeGenError "coinductive type not supported"));
  (if mutind_body.Declarations.mind_nparams <>
     mutind_body.Declarations.mind_nparams_rec then
       raise (CodeGenError "inductive type has a recursively non-uniform parameter"));
  ignore oneind_body

let ind_coq_type_registered_p coq_type =
  match ConstrMap.find_opt coq_type !ind_config_map with
  | Some _ -> true
  | None -> false

let check_ind_coq_type_not_registered coq_type =
  if ind_coq_type_registered_p coq_type then
    raise (CodeGenError "inductive type not registered")

let get_ind_config coq_type =
  match ConstrMap.find_opt coq_type !ind_config_map with
  | Some ind_cfg -> ind_cfg
  | None -> raise (CodeGenError "inductive type already registered")

let register_ind_type (user_coq_type : Constrexpr.constr_expr) (c_type : string) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_constr env sigma user_coq_type in
  let (mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  check_ind_coq_type_not_registered coq_type;
  check_ind_coq_type env sigma coq_type;
  let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
    Array.map (fun cstrname -> {
      coq_cstr = cstrname;
      c_cstr = None;
      c_caselabel = "";
      c_accessors = [||] }) in
  let ent = {
    coq_type=coq_type;
    c_type=c_type;
    c_swfunc=None;
    cstr_configs=cstr_cfgs } in
  ind_config_map := ConstrMap.add coq_type ent !ind_config_map

let register_ind_cstr1 (user_coq_type : Constrexpr.constr_expr) (coq_cstr : Id.t)
    (c_cstr : string) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_constr env sigma user_coq_type in
  let (mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  let ind_cfg = get_ind_config coq_type in
  let j = match array_find_index_opt (Id.equal coq_cstr) oneind_body.Declarations.mind_consnames with
    | Some j -> j
    | None -> user_err (
        Pp.str "inductive type constructor not found:" ++ Pp.spc () ++
        Id.print coq_cstr ++ Pp.spc () ++
        Pp.str "for" ++ Pp.spc () ++
        Id.print oneind_body.Declarations.mind_typename)
  in
  let cstr_cfg = Array.get ind_cfg.cstr_configs j in
  (match cstr_cfg.c_cstr with
  | Some _ -> user_err (
      Pp.str "inductive type constructor already registered:" ++
      Id.print coq_cstr ++ Pp.spc () ++
      Pp.str "for" ++ Pp.spc () ++
      Id.print oneind_body.Declarations.mind_typename)
  | None -> ());
  ind_config_map := ConstrMap.add coq_type
    { ind_cfg with
      cstr_configs = array_copy_set ind_cfg.cstr_configs j { cstr_cfg with c_cstr = Some c_cstr } }
    !ind_config_map

let register_ind_cstr (user_coq_type : Constrexpr.constr_expr) (cstr_namepair_list : ind_constructor list) =
  List.iter (fun { ic_coq_cstr = coq_cstr; ic_c_cstr = c_cstr } -> register_ind_cstr1 user_coq_type coq_cstr c_cstr) cstr_namepair_list

let register_ind_match (user_coq_type : Constrexpr.constr_expr) (swfunc : string)
    (cstr_caselabel_accessors_list : ind_cstr_caselabel_accessors list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_constr env sigma user_coq_type in
  let (mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  let ind_cfg = get_ind_config coq_type in
  (match ind_cfg.c_swfunc with
  | Some _ -> raise (CodeGenError "inductive match configuration already registered")
  | None -> ());
  (if List.length cstr_caselabel_accessors_list <> Array.length oneind_body.Declarations.mind_consnames then
    raise (CodeGenError "inductive match: invalid number of constructors"));
  let f j cstr_cfg =
    let consname = Array.get oneind_body.Declarations.mind_consnames j in
    let p (cstr, caselabel, accessors) = Id.equal consname cstr in
    let cstr_caselabel_accessors_opt = List.find_opt p cstr_caselabel_accessors_list in
    let (cstr, caselabel, accessors) = (match cstr_caselabel_accessors_opt with
      | None -> raise (CodeGenError "inductive match: constructor not found");
      | Some cstr_caselabel_accessors -> cstr_caselabel_accessors) in
    (if Array.get oneind_body.Declarations.mind_consnrealdecls j <> List.length accessors then
      raise (CodeGenError "inductive match: invalid number of field accessors"));
    { cstr_cfg with c_caselabel = caselabel; c_accessors = Array.of_list accessors }
  in
  ind_config_map := ConstrMap.add coq_type
    { ind_cfg with
      c_swfunc = Some swfunc;
      cstr_configs = Array.mapi f ind_cfg.cstr_configs }
    !ind_config_map

