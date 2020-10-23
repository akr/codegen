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
open State
(*open Linear*)

let quote_coq_string (s : string) : string =
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

let nf_interp_type (env : Environ.env) (sigma : Evd.evar_map) (t : Constrexpr.constr_expr) : Evd.evar_map * Constr.t =
  let (sigma, t) = Constrintern.interp_type_evars env sigma t in
  let t = Reductionops.nf_all env sigma t in
  let t = EConstr.to_constr sigma t in
  (sigma, t)

let codegen_print_inductive_type (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  Feedback.msg_info (str "CodeGen Inductive Type" ++ spc () ++
    Printer.pr_constr_env env sigma ind_cfg.coq_type ++ spc () ++
    str (quote_coq_string ind_cfg.c_type) ++ str ".")

let codegen_print_inductive_match (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
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

let codegen_print_inductive1 (env : Environ.env) (sigma : Evd.evar_map) (ind_cfg : ind_config) : unit =
  codegen_print_inductive_type env sigma ind_cfg;
  codegen_print_inductive_match env sigma ind_cfg

let command_print_inductive (coq_type_list : Constrexpr.constr_expr list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if coq_type_list = [] then
    ConstrMap.iter (fun key ind_cfg -> codegen_print_inductive1 env sigma ind_cfg) !ind_config_map
  else
    coq_type_list |> List.iter (fun user_coq_type ->
      let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
      match ConstrMap.find_opt coq_type !ind_config_map with
      | None -> user_err (Pp.str "[codegen] inductive type not registered:" ++
          Pp.spc () ++ Printer.pr_constr_env env sigma coq_type)
      | Some ind_cfg -> codegen_print_inductive1 env sigma ind_cfg)

let get_ind_coq_type (env : Environ.env) (coq_type : Constr.t) : MutInd.t * Declarations.mutual_inductive_body * int * Declarations.one_inductive_body * Constr.constr list =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (f, args) = Constr.decompose_app coq_type in
  (if not (Constr.isInd f) then
    user_err (Pp.str "[codegen] inductive type expected:" ++ Pp.spc () ++
    Printer.pr_constr_env env sigma coq_type));
  let ind = Univ.out_punivs (Constr.destInd f) in
  let (mutind, i) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  (mutind, mutind_body, i, oneind_body, args)

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
  let (mutind, mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  (if mutind_body.Declarations.mind_finite <> Declarations.Finite &&
      mutind_body.Declarations.mind_finite <> Declarations.BiFinite then
        user_err (Pp.str "[codegen] coinductive type not supported:" ++ Pp.spc () ++
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
    user_err (Pp.str "[codegen] inductive type already registered:" ++ Pp.spc () ++
              Printer.pr_constr_env env sigma coq_type)

let get_ind_config (coq_type : Constr.t) : ind_config =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match ConstrMap.find_opt coq_type !ind_config_map with
  | Some ind_cfg -> ind_cfg
  | None ->
      user_err (Pp.str "[codegen] inductive type not registered:" ++ Pp.spc () ++
      Printer.pr_constr_env env sigma coq_type)

let register_ind_type (env : Environ.env) (sigma : Evd.evar_map) (coq_type : Constr.t) (c_type : string) : ind_config =
  let (mutind, mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  check_ind_coq_type_not_registered coq_type;
  check_ind_coq_type env sigma coq_type;
  let cstr_cfgs = oneind_body.Declarations.mind_consnames |>
    Array.map (fun cstrname -> {
      coq_cstr = cstrname;
      c_caselabel = "";
      c_accessors = [||] }) in
  let ind_cfg = {
    coq_type=coq_type;
    c_type=c_type;
    c_swfunc=None;
    cstr_configs=cstr_cfgs } in
  ind_config_map := ConstrMap.add coq_type ind_cfg !ind_config_map;
ind_cfg

let command_ind_type (user_coq_type : Constrexpr.constr_expr) (c_type : string) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  ignore (register_ind_type env sigma coq_type c_type)

let register_ind_match (env : Environ.env) (sigma : Evd.evar_map) (coq_type : Constr.t)
     (swfunc : string) (cstr_caselabel_accessors_list : ind_cstr_caselabel_accessors list) : ind_config =
  let (mutind, mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  let ind_cfg = get_ind_config coq_type in
  (match ind_cfg.c_swfunc with
  | Some _ -> user_err (
      Pp.str "[codegen] inductive match configuration already registered:" ++ Pp.spc () ++
      Printer.pr_constr_env env sigma coq_type)
  | None -> ());
  (if List.length cstr_caselabel_accessors_list <> Array.length oneind_body.Declarations.mind_consnames then
    user_err (Pp.str "[codegen] inductive match: invalid number of constructors:" ++ Pp.spc () ++
      Pp.str "needs" ++ Pp.spc () ++
      Pp.int (Array.length oneind_body.Declarations.mind_consnames) ++ Pp.spc () ++
      Pp.str "but" ++ Pp.spc () ++
      Pp.int (List.length cstr_caselabel_accessors_list)));
  let f j cstr_cfg =
    let consname = Array.get oneind_body.Declarations.mind_consnames j in
    let p (cstr, caselabel, accessors) = Id.equal consname cstr in
    let cstr_caselabel_accessors_opt = List.find_opt p cstr_caselabel_accessors_list in
    let (cstr, caselabel, accessors) = (match cstr_caselabel_accessors_opt with
      | None -> user_err (
        Pp.str "[codegen] inductive match: constructor not found:" ++ Pp.spc () ++
        Id.print consname);
      | Some cstr_caselabel_accessors -> cstr_caselabel_accessors) in
    (if Array.get oneind_body.Declarations.mind_consnrealdecls j <> List.length accessors then
      user_err (Pp.str "[codegen] inductive match: invalid number of member accessors:" ++
      Pp.str "needs" ++ Pp.spc () ++
      Pp.int (Array.get oneind_body.Declarations.mind_consnrealdecls j) ++ Pp.spc () ++
      Pp.str "but" ++ Pp.spc () ++
      Pp.int (List.length accessors) ++ Pp.spc () ++
      Pp.str "for" ++ Pp.spc () ++
      Id.print cstr_cfg.coq_cstr ++ Pp.spc () ++
      Pp.str "of" ++ Pp.spc () ++
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

let command_ind_match (user_coq_type : Constrexpr.constr_expr) (swfunc : string)
    (cstr_caselabel_accessors_list : ind_cstr_caselabel_accessors list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  ignore (register_ind_match env sigma coq_type swfunc cstr_caselabel_accessors_list)

