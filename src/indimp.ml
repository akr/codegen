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
open State
open Induc
open Specialize
open Snippet

let ind_recursive_p (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  (*msg_info_hov (Pp.str "[codegen] ind_recursive_p:" +++ Printer.pr_econstr_env env sigma coq_type);*)
  let open Declarations in
  let (f, params) = decompose_appvect sigma coq_type in
  let (ind, _) = destInd sigma f in
  let (mutind, _) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  let ntypes = mutind_body.mind_ntypes in
  let exception RecursionFound in
  try
    for i = 0 to ntypes - 1 do
      let oneind_body = mutind_body.mind_packets.(i) in
      let numcstr = Array.length oneind_body.mind_consnames in
      for j0 = 0 to numcstr - 1 do
        (*msg_info_hov (Pp.str "[codegen] ind_recursive_p i=" ++
                           Pp.int i ++
                           Pp.str "(" ++ Id.print oneind_body.mind_typename ++ Pp.str ")" +++
                           Pp.str "j0=" ++ Pp.int j0 ++
                           Pp.str "(" ++ Id.print oneind_body.mind_consnames.(j0) ++ Pp.str ")");*)
        let (ctxt, rettype) = inductive_abstract_constructor_type_relatively_to_inductive_types_context_nflc
          mutind_body.mind_ntypes mutind oneind_body.mind_nf_lc.(j0) in
        ignore
          (Context.Rel.fold_outside
            (fun decl k ->
              (match decl with
              | Context.Rel.Declaration.LocalAssum (name, ty) ->
                  let ty = EConstr.of_constr ty in
                  if Array.mem true (free_variables_without env sigma ntypes k ty) then
                    raise RecursionFound
              | Context.Rel.Declaration.LocalDef (name, expr, ty) ->
                  let expr = EConstr.of_constr expr in
                  let ty = EConstr.of_constr ty in
                  if Array.mem true (free_variables_without env sigma ntypes k expr) then
                    raise RecursionFound;
                  if Array.mem true (free_variables_without env sigma ntypes k ty) then
                    raise RecursionFound);
              k+1)
            ctxt
            ~init:0)
      done
    done;
    (*msg_info_hov (Pp.str "[codegen] ind_recursive_p: recursion not found");*)
    false
  with RecursionFound ->
    (*msg_info_hov (Pp.str "[codegen] ind_recursive_p: recursion found");*)
    true

let ind_mutual_p (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  (*msg_info_hov (Pp.str "[codegen] ind_mutual_p:" +++ Printer.pr_econstr_env env sigma coq_type);*)
  let open Declarations in
  let (f, params) = decompose_appvect sigma coq_type in
  let (ind, _) = destInd sigma f in
  let (mutind, _) = ind in
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
      let cstr_id = oib.mind_consnames.(j0) in
      if Hashtbl.mem h cstr_id then
        user_err (Pp.str "[codegen] constructor name conflict:" +++ Id.print cstr_id);
      Hashtbl.add h cstr_id true
    done
  done

type member_names = {
  member_type_lazy: c_typedata option Lazy.t;
  member_name: string;
  member_accessor: string;
}

type cstr_names = {
  cstr_j: int;
  cstr_id: Id.t;
  cstr_name: string;
  cstr_enum_const: string;
  cstr_struct_tag: string;
  cstr_umember: string; (* union member name *)
  cstr_members: member_names list;
}

type ind_names = {
  ind_pind: inductive * EInstance.t;
  ind_params: EConstr.t array;
  ind_name: string;
  ind_struct_tag: string;
  ind_enum_tag: string;
  ind_swfunc: string;
  ind_cstrs: cstr_names array;
}

let pr_member_names (env : Environ.env) (sigma : Evd.evar_map) (member_names : member_names) : Pp.t =
  Pp.v 2 (Pp.str "{" +++
    Pp.hov 2 (Pp.str "member_type:" +++ (if Lazy.is_val member_names.member_type_lazy then
        match member_names.member_type_lazy with
        | lazy None -> Pp.str "void"
        | lazy (Some c_type) -> pr_c_abstract_decl c_type
      else
        Pp.str "(lazy)")) +++
    Pp.hov 2 (Pp.str "member_name:" +++ Pp.qstring member_names.member_name) +++
    Pp.hov 2 (Pp.str "member_accessor:" +++ Pp.qstring member_names.member_accessor) ++ Pp.brk (0,-2) ++
  Pp.str "}")

let pr_cstr_names (env : Environ.env) (sigma : Evd.evar_map) (cstr_names : cstr_names) : Pp.t =
  Pp.v 2 (Pp.str "{" +++
    Pp.hov 2 (Pp.str "cstr_j:" +++ Pp.int cstr_names.cstr_j) +++
    Pp.hov 2 (Pp.str "cstr_id:" +++ Id.print cstr_names.cstr_id) +++
    Pp.hov 2 (Pp.str "cstr_name:" +++ Pp.qstring cstr_names.cstr_name) +++
    Pp.hov 2 (Pp.str "cstr_enum_const:" +++ Pp.qstring cstr_names.cstr_enum_const) +++
    Pp.hov 2 (Pp.str "cstr_struct_tag:" +++ Pp.qstring cstr_names.cstr_struct_tag) +++
    Pp.hov 2 (Pp.str "cstr_umember:" +++ Pp.qstring cstr_names.cstr_umember) +++
    pp_sjoinmap_list (pr_member_names env sigma) cstr_names.cstr_members ++ Pp.brk (0,-2) ++
  Pp.str "}")

let pr_ind_names (env : Environ.env) (sigma : Evd.evar_map) (ind_names : ind_names) : Pp.t =
  Pp.v 2 (Pp.str "{" +++
    Pp.hov 2 (Pp.str "ind_pind:" +++ Printer.pr_inductive env (fst ind_names.ind_pind)) +++
    Pp.hov 2 (Pp.str "ind_params:" +++ pp_sjoinmap_ary (Printer.pr_econstr_env env sigma) ind_names.ind_params) +++
    Pp.hov 2 (Pp.str "ind_name:" +++ Pp.qstring ind_names.ind_name) +++
    Pp.hov 2 (Pp.str "ind_struct_tag:" +++ Pp.qstring ind_names.ind_struct_tag) +++
    Pp.hov 2 (Pp.str "ind_enum_tag:" +++ Pp.qstring ind_names.ind_enum_tag) +++
    Pp.hov 2 (Pp.str "ind_swfunc:" +++ Pp.qstring ind_names.ind_swfunc) +++
    pp_sjoinmap_ary (pr_cstr_names env sigma) ind_names.ind_cstrs ++ Pp.brk (0,-2) ++
  Pp.str "}")

type nvmember_names = {
  nvmember_type: c_typedata;
  nvmember_name: string;
  nvmember_accessor: string;
}

let non_void_cstr_members (cstr_members : member_names list) : nvmember_names list =
  cstr_members |> List.filter_map (fun { member_type_lazy; member_name; member_accessor } ->
    match member_type_lazy with
    | lazy None -> None
    | lazy (Some member_type) -> Some {nvmember_type=member_type;
                                       nvmember_name=member_name;
                                       nvmember_accessor=member_accessor})

(* Generate automatic generated names.  No user configuration considered. *)
let generate_indimp_names (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : ind_names =
  let (f, args) = decompose_appvect sigma coq_type in
  let params = args in (* xxx: args should be parameters of inductive type *)
  let pind = destInd sigma f in
  let ((mutind, i), u) = pind in
  let mutind_body = Environ.lookup_mind mutind env in
  check_ind_id_conflict mutind_body;
  let open Declarations in
  let oneind_body = mutind_body.mind_packets.(i) in
  let global_prefix = global_gensym () in
  let i_suffix = "_" ^ Id.to_string oneind_body.mind_typename in
  let ind_name = global_prefix ^ "_type" ^ i_suffix in
  let ind_struct_tag = global_prefix ^ "_istruct" ^ i_suffix in
  let ind_enum_tag = global_prefix ^ "_enum" ^ i_suffix in
  let ind_swfunc = global_prefix ^ "_sw" ^ i_suffix in
  let ind_cstrs =
    oneind_body.mind_consnames |> Array.mapi (fun j0 cstr_id ->
      let cstr_j = j0 + 1 in
      (*msg_debug_hov (Printer.pr_econstr_env env sigma coq_type);*)
      let cstrterm = mkApp (mkConstructUi (pind, cstr_j), params) in
      (*msg_debug_hov (Printer.pr_econstr_env env sigma cstrterm);*)
      let cstrtype = Reductionops.nf_all env sigma (Retyping.get_type_of env sigma cstrterm) in
      let (revargs, result_type) = decompose_prod sigma cstrtype in
      let j_suffix = "_" ^ Id.to_string cstr_id in
      let cstr_name = global_prefix ^ "_cstr" ^ j_suffix  in
      let cstr_enum_const = global_prefix ^ "_tag" ^ j_suffix in
      let cstr_struct_tag = global_prefix ^ "_cstruct" ^ j_suffix in
      let cstr_umember = global_prefix ^ "_umember" ^ j_suffix in
      let cstr_members =
        (List.rev revargs) |> List.mapi (fun k (arg_name, arg_type) ->
          (if not (EConstr.Vars.closed0 sigma arg_type) then
            user_err_hov (Pp.str "[codegen] dependent constructor argument:" +++
              Pp.pr_nth (k+1) +++ Pp.str "argument of" +++
              Printer.pr_econstr_env env sigma cstrterm +++ Pp.str "is" +++
              Printer.pr_econstr_env env sigma arg_type));
          let k_suffix =
            string_of_int (k+1) ^ "_" ^ Id.to_string cstr_id ^
            match Context.binder_name arg_name with
            | Name.Anonymous -> ""
            | Name.Name id -> "_" ^ c_id (Id.to_string id)
          in
          let member_name = global_prefix ^ "_member" ^ k_suffix in
          let member_accessor = global_prefix ^ "_get" ^ k_suffix in
          let member_type_lazy = lazy (if coq_type_is_void env sigma arg_type then None else Some (c_typename env sigma arg_type)) in
          { member_type_lazy; member_name; member_accessor })
      in
      { cstr_j; cstr_id; cstr_name; cstr_enum_const; cstr_struct_tag; cstr_umember; cstr_members })
  in
  let result = { ind_pind=pind; ind_params=params; ind_name; ind_struct_tag; ind_enum_tag; ind_swfunc; ind_cstrs } in
  msg_info_v (pr_ind_names env sigma result);
  result

(* Merge generated names and user configuration.  Register generated names if no user configuration. *)
let register_indimp (env : Environ.env) (sigma : Evd.evar_map) (ind_names : ind_names) : Environ.env * ind_names =
  let { ind_pind=pind; ind_params=params } = ind_names in
  let coq_type_i = mkApp (mkIndU pind, params) in
  let ind_cfg_opt = lookup_ind_config sigma coq_type_i in
  (* Merge information from CodeGen InductiveType COQ_TYPE => "C_TYPE" *)
  let ind_names =
    let ind_name =
      match ind_cfg_opt with
      | Some ind_cfg ->
          if is_simple_c_type ind_cfg.c_type then
            ind_cfg.c_type.c_type_left
          else
            user_err_hov (Pp.str "[codegen] inductive type already configured with complex C type:" +++ pr_c_abstract_decl ind_cfg.c_type)
      | None ->
          let c_type = simple_c_type ind_names.ind_name in
          ignore (register_ind_type env sigma coq_type_i c_type);
          ind_names.ind_name
    in
    { ind_names with ind_name }
  in
  (* Merge information from CodeGen InductiveMatch COQ_TYPE => "C_SWFUNC" ( | CONSTRUCTOR => "C_CASELABEL" "C_ACCESSOR"* )* *)
  let ind_names =
    match ind_cfg_opt with
    | Some { c_swfunc=Some swfunc; cstr_configs=cstr_cfgs } ->
        { ind_names with
          ind_swfunc=swfunc;
          ind_cstrs=
            ind_names.ind_cstrs |> Array.map (fun cstr_names ->
              let cstr_cfg =
                match cstr_cfgs |> array_find_opt (fun { coq_cstr } -> Id.equal coq_cstr cstr_names.cstr_id) with
                | None -> user_err_hov (Pp.str "[codegen] constuctor configuration not found:" +++ Id.print cstr_names.cstr_id)
                | Some cstr_cfg -> cstr_cfg
              in
              (* xxx: check c_caselabel is not empty string *)
              { cstr_names with
                cstr_enum_const=cstr_cfg.c_caselabel;
                cstr_members=
                  List.map2 (fun member_names accessor -> { member_names with member_accessor = accessor })
                    cstr_names.cstr_members (Array.to_list cstr_cfg.c_accessors) }) }
    | _ ->
        let cstr_caselabel_accessors_ary =
          ind_names.ind_cstrs |> Array.map (fun { cstr_id; cstr_enum_const; cstr_members } ->
            let caselabel = cstr_enum_const in
            let accessors = List.map (fun { member_accessor } -> member_accessor) cstr_members in
            { cstr_id; cstr_caselabel=caselabel; cstr_accessors=accessors })
        in
        let cstr_caselabel_accessors_list = Array.to_list cstr_caselabel_accessors_ary in
        ignore (register_ind_match env sigma coq_type_i ind_names.ind_swfunc cstr_caselabel_accessors_list);
        ind_names
  in
  (* Merge information from CodeGen Primitive CONSTRUCTOR PARAMS => "CSTR_NAME" *)
  let (env, ind_names) =
    let (env, ind_cstrs) =
      let params0 = CArray.map_to_list (EConstr.to_constr sigma) params in
      CArray.fold_left_map
        (fun env cstr_names ->
          let { cstr_j; cstr_id; cstr_name; cstr_enum_const; cstr_members } = cstr_names in
          let cstrterm = mkConstructUi (pind, cstr_j) in
          let cstrterm0 = EConstr.to_constr sigma cstrterm in
          ignore (codegen_define_or_check_static_arguments env sigma cstrterm0 (List.init (Array.length params) (fun _ -> SorD_S)));
          let presimp = EConstr.to_constr sigma (mkApp (cstrterm, params)) in
          match ConstrMap.find_opt presimp !gallina_instance_map with
          | None ->
              let spi = { spi_cfunc_name = Some cstr_name; spi_presimp_id = None; spi_simplified_id = None } in
              let (env, sp_inst) = codegen_define_instance env sigma CodeGenPrimitive cstrterm0 params0 (Some spi) in
              (env, cstr_names)
          | Some (sp_cfg, { sp_cfunc_name = cstr_name; sp_icommand }) ->
              (* xxx: check name is valid identifier for C *)
              if sp_icommand <> CodeGenPrimitive then
                user_err_hov (Pp.str "[codegen] CodeGen IndImp needs that constructors declared by CodeGen Primitive:" +++ Id.print cstr_id);
              let (cstr_enum_const, cstr_members) =
                match ind_cfg_opt with
                | Some { c_swfunc=Some _; cstr_configs=cstr_cfgs } ->
                    (match array_find_opt (fun { coq_cstr } -> Id.equal coq_cstr cstr_id ) cstr_cfgs with
                    | Some { c_caselabel; c_accessors } ->
                        let cstr_members =
                          List.map2 (fun member_names c_accessor -> { member_names with member_accessor=c_accessor })
                            cstr_members (Array.to_list c_accessors)
                        in
                        (c_caselabel, cstr_members)
                    | None -> (cstr_enum_const, cstr_members))
                | _ -> (cstr_enum_const, cstr_members)
              in
              let cstr_names = { cstr_names with cstr_name; cstr_enum_const; cstr_members } in
              (env, cstr_names))
        env ind_names.ind_cstrs
    in
    (env, { ind_names with ind_cstrs })
  in
  (env, ind_names)

let gen_indimp_immediate_impl (ind_names : ind_names) : string =
  let { ind_name; ind_struct_tag; ind_enum_tag; ind_swfunc; ind_cstrs } = ind_names in
  let constant_constructor_only =
    ind_cstrs |> Array.for_all (fun { cstr_members } ->
      let nv_cstr_members = non_void_cstr_members cstr_members in
      CList.is_empty nv_cstr_members)
  in
  let single_constructor = Array.length ind_cstrs = 1 in
  let pp_enum =
    if single_constructor then
      Pp.mt ()
    else
      Pp.hov 0 (
        (Pp.str "enum" +++ Pp.str ind_enum_tag +++
        hovbrace (
          pp_joinmap_ary (Pp.str "," ++ Pp.spc ()) (fun { cstr_enum_const } -> Pp.str cstr_enum_const) ind_cstrs) ++
          Pp.str ";"))
  in
  let member_decls =
    ind_cstrs |> Array.map (fun { cstr_members } ->
      let nv_cstr_members = non_void_cstr_members cstr_members in
      nv_cstr_members |> pp_sjoinmap_list (fun {nvmember_type; nvmember_name} ->
        Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name) ++ Pp.str ";")))
  in
  let ind_cstrs_with_decls =
    Array.map2
      (fun ind_cstr member_decl -> (ind_cstr, member_decl))
      ind_cstrs member_decls
  in
  let ind_cstrs_with_decls = Array.to_list ind_cstrs_with_decls in
  let pp_cstr_struct_defs =
    if constant_constructor_only || single_constructor then
      Pp.mt ()
    else
      pp_sjoin_list
        (ind_cstrs_with_decls |> List.filter_map (fun ({ cstr_struct_tag; cstr_members }, member_decl) ->
          let nv_cstr_members = non_void_cstr_members cstr_members in
          if CList.is_empty nv_cstr_members then
            None
          else
            Some (
              Pp.hov 0 (Pp.str "struct" +++ Pp.str cstr_struct_tag) +++
              vbrace member_decl ++
              Pp.str ";")))
  in
  let pp_typedef =
    Pp.v 0 (
      Pp.str "typedef struct" +++ Pp.str ind_struct_tag +++
      vbrace (
        (if single_constructor then
          Pp.mt ()
        else
          Pp.hov 0 (Pp.str "enum" +++ Pp.str ind_enum_tag +++ Pp.str "tag;")) +++
        (if constant_constructor_only then
          Pp.mt ()
        else if single_constructor then
          Pp.v 0
            (let (ind_cstr, member_decl) = List.hd ind_cstrs_with_decls in
            member_decl)
        else
          Pp.v 0 (Pp.str "union" +++
                  vbrace (
                    pp_sjoin_list
                      (ind_cstrs_with_decls |> List.filter_map (fun ({ cstr_struct_tag; cstr_umember; cstr_members }, member_decl) ->
                        let nv_cstr_members = non_void_cstr_members cstr_members in
                        if CList.is_empty nv_cstr_members then
                          None
                        else
                          Some (
                            Pp.hov 0 (Pp.str "struct" +++
                                      Pp.str cstr_struct_tag +++
                                      Pp.str cstr_umember ++
                                      Pp.str ";"))))) ++
                  Pp.str " as;"))
      ) ++ Pp.str (" " ^ ind_name ^ ";"))
  in
  let pp_swfunc =
    if single_constructor then
      Pp.mt ()
    else
      Pp.h (
        Pp.str "#define" +++
        Pp.str ind_swfunc ++ Pp.str "(x)" +++
        Pp.str "((x).tag)")
  in
  let pp_accessors =
    ind_cstrs |> pp_sjoinmap_ary (fun { cstr_umember; cstr_members } ->
      let nv_cstr_members = non_void_cstr_members cstr_members in
      nv_cstr_members |> pp_sjoinmap_list (fun {nvmember_name; nvmember_accessor} ->
        Pp.h (Pp.str "#define" +++
              Pp.str nvmember_accessor ++
              Pp.str "(x)" +++
              (if single_constructor then
                Pp.str ("((x)." ^ nvmember_name ^ ")")
              else
                Pp.str ("((x).as." ^ cstr_umember ^ "." ^ nvmember_name ^ ")")))))
  in
  let pp_cstr =
    ind_cstrs |> pp_sjoinmap_ary (fun { cstr_name; cstr_enum_const; cstr_umember; cstr_members } ->
      let nv_cstr_members = non_void_cstr_members cstr_members in
      let args =
        pp_joinmap_list (Pp.str "," ++ Pp.spc ())
          (fun {nvmember_name} -> Pp.str nvmember_name)
          nv_cstr_members
      in
      Pp.h (Pp.str "#define" +++
              Pp.str cstr_name ++
              Pp.str "(" ++ args ++ Pp.str ")" +++
              Pp.str "(" ++
              Pp.str ("(" ^ ind_name ^ ")") ++
              (if single_constructor then
                hbrace args
              else
                hbrace (
                  let union_init =
                    Pp.str ("." ^ cstr_umember) +++
                    Pp.str "=" +++
                    hbrace args
                  in
                  if CList.is_empty nv_cstr_members then
                    Pp.str cstr_enum_const
                  else
                    (Pp.str cstr_enum_const ++ Pp.str "," +++ hbrace union_init))) ++
              Pp.str ")"))
  in
  let pp =
    Pp.v 0 (
      pp_enum +++
      pp_cstr_struct_defs +++
      pp_typedef +++
      pp_swfunc +++
      pp_accessors +++
      pp_cstr +++
      Pp.mt ()
    )
  in
  (*msg_debug_hov (Pp.str (Pp.db_string_of_pp pp));*)
  (*msg_info_hov pp;*)
  Pp.string_of_ppcmds pp

let gen_indimp_heap_decls (ind_names : ind_names) : string =
  let pp_ind_types =
    let { ind_name; ind_struct_tag } = ind_names in
    Pp.hov 0 (
      Pp.str "typedef" +++
      Pp.str "struct" +++
      Pp.str ind_struct_tag +++
      Pp.str "*" ++
      Pp.str ind_name ++
      Pp.str ";")
  in
  let pp_decls = Pp.v 0 pp_ind_types in
  Pp.string_of_ppcmds pp_decls

let gen_indimp_heap_impls_single_constructor (ind_names : ind_names) : string =
  let { ind_name; ind_struct_tag; ind_enum_tag; ind_swfunc; ind_cstrs } = ind_names in
  let ind_cstr = ind_cstrs.(0) in
  let pp_ind_impls =
    let member_decl =
      let { cstr_members } = ind_cstr in
      let nv_cstr_members = non_void_cstr_members cstr_members in
      pp_sjoinmap_list
        (fun {nvmember_type; nvmember_name} ->
          Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name) ++ Pp.str ";"))
        nv_cstr_members
    in
    let pp_ind_struct_def =
      Pp.hov 0 (Pp.str "struct" +++ Pp.str ind_struct_tag) +++
      vbrace member_decl ++
      Pp.str ";"
    in
    let pp_accessors =
      (* #define list_cons_get1(x) (((struct list_cons_struct * )(x))->head) *)
      let { cstr_members } = ind_cstr in
      let nv_cstr_members = non_void_cstr_members cstr_members in
      pp_sjoinmap_list
        (fun {nvmember_name; nvmember_accessor} ->
          Pp.h (Pp.str "#define" +++
                Pp.str nvmember_accessor ++
                Pp.str "(x)" +++
                Pp.str ("((x)->" ^ nvmember_name ^ ")")))
        nv_cstr_members
    in
    let pp_cstr =
      (*
        static list_t list_cons(bool head, list_t tail) {
          struct list_cons_struct *p;
          if (!(p = malloc(sizeof(struct list_cons_struct)))) abort();
          p->tag = list_cons_tag;
          p->head = head;
          p->tail = tail;
          return (list_t)p;
        }
      *)
      let { cstr_name; cstr_enum_const; cstr_members } = ind_cstr in
      let nv_cstr_members = non_void_cstr_members cstr_members in
      let fargs =
        if CList.is_empty nv_cstr_members then
          Pp.str "void"
        else
          pp_joinmap_list (Pp.str "," ++ Pp.spc ())
            (fun {nvmember_type; nvmember_name} ->
              Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name)))
            nv_cstr_members
      in
      Pp.v 0 (Pp.hov 2 (
                Pp.str "static" +++
                Pp.str ind_name +++
                Pp.str cstr_name ++
                Pp.str "(" ++ fargs ++ Pp.str ")") +++
              vbrace (
                Pp.hov 0 (Pp.str ind_name +++ Pp.str "p;") +++
                Pp.hov 0 (Pp.str ("if (!(p = malloc(sizeof(*p)))) abort();")) +++
                pp_sjoinmap_list
                  (fun {nvmember_name} ->
                    Pp.hov 0 (Pp.str "p->" ++ Pp.str nvmember_name +++ Pp.str "=" +++ Pp.str nvmember_name ++ Pp.str ";"))
                  nv_cstr_members +++
                Pp.hov 0 (Pp.str "return p;")))
    in
    pp_ind_struct_def +++ pp_accessors +++ pp_cstr
  in
  let pp_impls = Pp.v 0 pp_ind_impls in
  (*msg_debug_hov (Pp.str (Pp.db_string_of_pp pp));*)
  (*msg_info_hov pp;*)
  Pp.string_of_ppcmds pp_impls

let gen_indimp_heap_impls_generic (ind_names : ind_names) : string =
  let pp_ind_impls =
    let { ind_name; ind_struct_tag; ind_enum_tag; ind_swfunc; ind_cstrs } = ind_names in
    let pp_enum_decl =
      Pp.hov 0 (
        (Pp.str "enum" +++ Pp.str ind_enum_tag +++
        hovbrace (
          pp_joinmap_ary (Pp.str "," ++ Pp.spc ()) (fun { cstr_enum_const } -> Pp.str cstr_enum_const) ind_cstrs) ++
          Pp.str ";"))
    in
    let pp_ind_struct_def =
      Pp.hov 0 (Pp.str "struct" +++ Pp.str ind_struct_tag) +++
        vbrace (Pp.hov 0 (Pp.str ("enum " ^ ind_enum_tag) +++ Pp.str "tag;")) ++
        Pp.str ";"
    in
    let pp_swfunc =
      Pp.h (
        Pp.str "#define" +++
        Pp.str ind_swfunc ++ Pp.str "(x)" +++
        Pp.str "((x)->tag)")
    in
    let member_decls =
      ind_cstrs |> Array.map (fun { cstr_members } ->
        let nv_cstr_members = non_void_cstr_members cstr_members in
        Pp.hov 0 (Pp.str ("enum " ^ ind_enum_tag) +++ Pp.str "tag;") +++
        pp_sjoinmap_list
          (fun {nvmember_type; nvmember_name} ->
            Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name) ++ Pp.str ";"))
          nv_cstr_members)
    in
    let ind_cstrs_with_decls =
      Array.map2
        (fun ind_cstr member_decl -> (ind_cstr, member_decl))
        ind_cstrs member_decls
    in
    let pp_cstr_struct_defs =
      ind_cstrs_with_decls |> pp_sjoinmap_ary (fun ({ cstr_struct_tag }, member_decl) ->
        Pp.hov 0 (Pp.str "struct" +++ Pp.str cstr_struct_tag) +++
        vbrace member_decl ++
        Pp.str ";")
    in
    let pp_accessors =
      (* #define list_cons_get1(x) (((struct list_cons_struct * )(x))->head) *)
      ind_cstrs |> pp_sjoinmap_ary (fun { cstr_struct_tag; cstr_members } ->
          let nv_cstr_members = non_void_cstr_members cstr_members in
          pp_sjoinmap_list
            (fun {nvmember_name; nvmember_accessor} ->
              Pp.h (Pp.str "#define" +++
                    Pp.str nvmember_accessor ++
                    Pp.str "(x)" +++
                    Pp.str ("(((struct " ^ cstr_struct_tag ^ " *)(x))->" ^ nvmember_name ^ ")")))
            nv_cstr_members)
    in
    let pp_cstr =
      (*
        static list_t list_cons(bool head, list_t tail) {
          struct list_cons_struct *p;
          if (!(p = malloc(sizeof(struct list_cons_struct)))) abort();
          p->tag = list_cons_tag;
          p->head = head;
          p->tail = tail;
          return (list_t)p;
        }
      *)
      ind_cstrs |> pp_sjoinmap_ary (fun { cstr_name; cstr_enum_const; cstr_struct_tag; cstr_members } ->
        let nv_cstr_members = non_void_cstr_members cstr_members in
        let fargs =
          if CList.is_empty nv_cstr_members then
            Pp.str "void"
          else
            pp_joinmap_list (Pp.str "," ++ Pp.spc ())
              (fun {nvmember_type; nvmember_name} ->
                Pp.hov 0 (pr_c_decl nvmember_type (Pp.str nvmember_name)))
              nv_cstr_members
        in
        Pp.v 0 (Pp.hov 2 (
                  Pp.str "static" +++
                  Pp.str ind_name +++
                  Pp.str cstr_name ++
                  Pp.str "(" ++ fargs ++ Pp.str ")") +++
                vbrace (
                  Pp.hov 0 (Pp.str "struct" +++ Pp.str cstr_struct_tag +++ Pp.str "*p;") +++
                  Pp.hov 0 (Pp.str ("if (!(p = malloc(sizeof(*p)))) abort();")) +++
                  Pp.hov 0 (Pp.str "p->tag =" +++ Pp.str cstr_enum_const ++ Pp.str ";") +++
                  pp_sjoinmap_list
                    (fun {nvmember_name} ->
                      Pp.hov 0 (Pp.str "p->" ++ Pp.str nvmember_name +++ Pp.str "=" +++ Pp.str nvmember_name ++ Pp.str ";"))
                    nv_cstr_members +++
                  Pp.hov 0 (Pp.str "return" +++ Pp.str ("(" ^ ind_name ^ ")p;")))))
    in
    pp_enum_decl +++ pp_ind_struct_def +++ pp_cstr_struct_defs +++ pp_swfunc +++ pp_accessors +++ pp_cstr
  in
  let pp_impls = Pp.v 0 pp_ind_impls in
  (*msg_debug_hov (Pp.str (Pp.db_string_of_pp pp));*)
  (*msg_info_hov pp;*)
  Pp.string_of_ppcmds pp_impls

let gen_indimp_heap_impls (ind_names : ind_names) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let { ind_pind; ind_params; ind_name; ind_struct_tag; ind_enum_tag; ind_swfunc; ind_cstrs } = ind_names in
  ind_cstrs |> Array.iter (fun cstr_names ->
    let cstr_key = EConstr.to_constr sigma (mkApp (mkConstructUi (ind_pind, cstr_names.cstr_j), ind_params)) in
    cstr_deallocator_cfunc_map := ConstrMap.add cstr_key "free" !cstr_deallocator_cfunc_map);
  let single_constructor = Array.length ind_cstrs = 1 in
  if single_constructor then
    gen_indimp_heap_impls_single_constructor ind_names
  else
    gen_indimp_heap_impls_generic ind_names

let generate_indimp_immediate (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : unit =
  msg_info_hov (Pp.str "[codegen] generate_indimp_immediate:" +++ Printer.pr_econstr_env env sigma coq_type);
  let ind_names = generate_indimp_names env sigma coq_type in
  let env, ind_names = register_indimp env sigma ind_names in
  ignore env;
  add_thunk "type_impls" (fun () -> gen_indimp_immediate_impl ind_names)

let generate_indimp_heap (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : unit =
  msg_info_hov (Pp.str "[codegen] generate_indimp_heap:" +++ Printer.pr_econstr_env env sigma coq_type);
  let ind_names = generate_indimp_names env sigma coq_type in
  let env, ind_names = register_indimp env sigma ind_names in
  ignore env;
  add_thunk "type_decls" (fun () -> gen_indimp_heap_decls ind_names);
  add_thunk "type_impls" (fun () -> gen_indimp_heap_impls ind_names)

let command_indimp ?(force_heap = false) (user_coq_type : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  (* (if ind_coq_type_registered_p coq_type then
    user_err (Pp.str "[codegen] inductive type already configured:" +++ Printer.pr_constr_env env sigma coq_type)); *)
  if force_heap || ind_recursive_p env sigma coq_type || ind_mutual_p env sigma coq_type then
    generate_indimp_heap env sigma coq_type
  else
    generate_indimp_immediate env sigma coq_type

