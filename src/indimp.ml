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
open Pp
open CErrors
open EConstr

open Cgenutil
open State
open Induc
open Specialize
open Genc
open Snippet

let ind_recursive_p (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : bool =
  (*msg_info_hov (Pp.str "[codegen] ind_recursive_p:" +++ Printer.pr_econstr_env env sigma coq_type);*)
  let open Declarations in
  let (f, params) = decompose_app sigma coq_type in
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
        let (ctxt, rettype) = oneind_body.mind_nf_lc.(j0) in
        ignore
          (Context.Rel.fold_outside
            (fun decl k ->
              (match decl with
              | Context.Rel.Declaration.LocalAssum (name, ty) ->
                  let ty = EConstr.of_constr ty in
                  if Array.mem true (free_variables_without sigma ntypes k ty) then
                    raise RecursionFound
              | Context.Rel.Declaration.LocalDef (name, expr, ty) ->
                  let expr = EConstr.of_constr expr in
                  let ty = EConstr.of_constr ty in
                  if Array.mem true (free_variables_without sigma ntypes k expr) then
                    raise RecursionFound;
                  if Array.mem true (free_variables_without sigma ntypes k ty) then
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
  let (f, params) = decompose_app sigma coq_type in
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

let generate_indimp_names (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) :
    ((*mutind*)MutInd.t *
     (*params*)EConstr.t array *
     ((*ind type name*)string *
      (*enum tag*)string *
      (*C switch function*)string *
      ((*cstr ID*)Id.t *
       (*cstr function name*)string *
       (*cstr enum tag*)string *
       (*cstr struct tag*)string *
       (*cstr union member name*)string *
       ((*member type*)string *
        (*member name*)string *
        (*accessor name*)string) list) list) list) =
  let global_prefix = global_gensym () in
  let (f, args) = decompose_app sigma coq_type in
  let params = CArray.rev_of_list args in (* xxx: args should be parameters of inductive type *)
  let (ind, _) = destInd sigma f in
  let (mutind, _) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  check_ind_id_conflict mutind_body;
  let open Declarations in
  let ind_typenames =
    Array.mapi
      (fun i oneind_body ->
        let ind_id = oneind_body.mind_typename in
        let i_suffix = "_" ^ Id.to_string ind_id in
        let ind_typename = global_prefix ^ "_type" ^ i_suffix in
        let ind1 = Constr.mkInd (mutind, i) in
        let coq_type1 = Constr.mkApp (ind1, Array.map (EConstr.to_constr sigma) params) in
        ignore (register_ind_type env sigma coq_type1 ind_typename);
        ind_typename)
      mutind_body.mind_packets
  in
  let ind_names =
    List.mapi
      (fun i ind_typename ->
        let ind = (mutind, i) in
        let oneind_body = mutind_body.mind_packets.(i) in
        let ind_id = oneind_body.mind_typename in
        let i_suffix = "_" ^ Id.to_string ind_id in
        let enum_tag = global_prefix ^ "_enum" ^ i_suffix in
        let swfunc = global_prefix ^ "_sw" ^ i_suffix in
        let numcstr = Array.length oneind_body.mind_consnames in
        let cstr_and_members =
          List.init numcstr
            (fun j0 ->
              let j = j0 + 1 in
              (*msg_debug_hov (Printer.pr_econstr_env env sigma coq_type);*)
              let cstrterm = mkApp ((mkConstruct (ind, j)), params) in
              (*msg_debug_hov (Printer.pr_econstr_env env sigma cstrterm);*)
              let cstrtype = Retyping.get_type_of env sigma cstrterm in
              let (args, result_type) = decompose_prod sigma cstrtype in
              let cstrid = oneind_body.mind_consnames.(j0) in
              let j_suffix = "_" ^ Id.to_string cstrid in
              let cstrname = global_prefix ^ "_cstr" ^ j_suffix  in
              let cstr_enum_name = global_prefix ^ "_tag" ^ j_suffix in
              let cstr_struct = global_prefix ^ "_struct" ^ j_suffix in
              let cstr_umember = global_prefix ^ "_umember" ^ j_suffix in
              let members_and_accessors =
                List.mapi
                  (fun k (arg_name, arg_type) ->
                    let member_type = c_typename env sigma arg_type in
                    let k_suffix =
                      string_of_int (k+1) ^ "_" ^ Id.to_string cstrid ^
                      match Context.binder_name arg_name with
                      | Name.Anonymous -> ""
                      | Name.Name id -> "_" ^ c_id (Id.to_string id)
                    in
                    let member_name = global_prefix ^ "_member" ^ k_suffix in
                    let accessor = global_prefix ^ "_get" ^ k_suffix in
                    (member_type, member_name, accessor))
                  (List.rev args)
              in
              (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors))
        in
        (ind_typename, enum_tag, swfunc, cstr_and_members))
      (Array.to_list ind_typenames)
  in
  (mutind, params, ind_names)

let generate_indimp_immediate (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : unit =
  msg_info_hov (Pp.str "[codegen] generate_indimp_immediate:" +++ Printer.pr_econstr_env env sigma coq_type);
  let (mutind, params, ind_names) = generate_indimp_names env sigma coq_type in
  if List.length ind_names <> 1 then
    user_err (Pp.str "[codegen:bug] generate_indimp_immediate is called for mutual inductive type:" +++ Printer.pr_econstr_env env sigma coq_type);
  let (ind_typename, enum_tag, swfunc, cstr_and_members) = List.hd ind_names in
  let ind = (mutind, 0) in
  let cstr_caselabel_accessors_list =
    List.mapi
      (fun j (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
        let caselabel = if j = 0 then "default" else "case " ^ cstr_enum_name in
        let accessors = List.map (fun (member_type, member_name, accessor) -> accessor) members_and_accessors in
        (cstrid, caselabel, accessors))
      cstr_and_members
  in
  ignore (register_ind_match env sigma (EConstr.to_constr sigma coq_type) swfunc cstr_caselabel_accessors_list);
  let env =
    CList.fold_left_i
      (fun j env (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
        let cstrterm0 = EConstr.to_constr sigma (mkConstruct (ind, j)) in
        let params' = Array.map (EConstr.to_constr sigma) params in
        ignore (codegen_define_or_check_static_arguments env sigma cstrterm0 (List.init (Array.length params) (fun _ -> SorD_S)));
        let (env, sp_inst) = codegen_define_instance env sigma CodeGenPrimitive cstrterm0 (Array.to_list params') (Some { spi_cfunc_name = Some cstrname; spi_presimp_id = None; spi_simplified_id = None }) in
        env)
      1 env cstr_and_members
  in
  ignore env;
  let constant_constructor_only =
    List.for_all
      (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
        members_and_accessors = [])
      cstr_and_members
  in
  let single_constructor = List.length cstr_and_members = 1 in
  let pp_enum =
    if single_constructor then
      Pp.mt ()
    else
      Pp.hov 0 (
        (Pp.str "enum" +++ Pp.str enum_tag +++
        hovbrace (pp_joinmap_list (Pp.str "," ++ Pp.spc ())
          (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) -> Pp.str cstr_enum_name)
          cstr_and_members) ++ Pp.str ";"))
  in
  let member_decls =
    List.map
      (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
        pp_sjoinmap_list
          (fun (member_type, member_name, accessor) ->
            Pp.hov 0 (Pp.str member_type +++ Pp.str member_name ++ Pp.str ";"))
          members_and_accessors)
      cstr_and_members
  in
  let cstr_and_members_with_decls =
    List.map2
      (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) member_def ->
        (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors, member_def))
      cstr_and_members member_decls
  in
  let pp_cstr_struct_defs =
    if constant_constructor_only || single_constructor then
      Pp.mt ()
    else
      pp_sjoin_list
        (List.filter_map
          (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors, member_decl) ->
            if members_and_accessors = [] then
              None
            else
              Some (
                Pp.hov 0 (Pp.str "struct" +++ Pp.str cstr_struct) +++
                vbrace member_decl ++
                Pp.str ";"))
          cstr_and_members_with_decls)
  in
  let pp_typedef =
    Pp.v 0 (
      Pp.str "typedef struct" +++
      vbrace (
        (if single_constructor then
          Pp.mt ()
        else
          Pp.hov 0 (Pp.str "enum" +++ Pp.str enum_tag +++ Pp.str "tag;")) +++
        (if constant_constructor_only then
          Pp.mt ()
        else if single_constructor then
          Pp.v 0
            (let (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors, member_decl) = List.hd cstr_and_members_with_decls in
            member_decl)
        else
          Pp.v 0 (Pp.str "union" +++
                  vbrace (
                    pp_sjoin_list
                      (List.filter_map
                        (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors, member_decl) ->
                          if members_and_accessors = [] then
                            None
                          else
                            Some (
                              Pp.hov 0 (Pp.str "struct" +++
                                        Pp.str cstr_struct +++
                                        Pp.str cstr_umember ++
                                        Pp.str ";")))
                        cstr_and_members_with_decls)) ++
                  Pp.str " as;"))
      ) ++ Pp.str (" " ^ ind_typename ^ ";"))
  in
  let pp_swfunc =
    Pp.h (
      Pp.str "#define" +++
      Pp.str swfunc ++ Pp.str "(x)" +++
      (if single_constructor then
        Pp.str "0"
      else
        Pp.str "((x).tag)"))
  in
  let pp_accessors =
    pp_sjoinmap_list
      (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
        pp_sjoinmap_list
          (fun (member_type, member_name, accessor) ->
            Pp.h (Pp.str "#define" +++
                  Pp.str accessor ++
                  Pp.str "(x)" +++
                  (if single_constructor then
                    Pp.str ("((x)." ^ member_name ^ ")")
                  else
                    Pp.str ("((x).as." ^ cstr_umember ^ "." ^ member_name ^ ")"))))
          members_and_accessors)
      cstr_and_members
  in
  let pp_cstr =
    pp_sjoinmap_list
      (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
        let args =
          pp_joinmap_list (Pp.str "," ++ Pp.spc ())
            (fun (member_type, member_name, accessor) -> Pp.str member_name)
            members_and_accessors
        in
        Pp.h (Pp.str "#define" +++
                Pp.str cstrname ++
                Pp.str "(" ++ args ++ Pp.str ")" +++
                Pp.str "(" ++
                Pp.str ("(" ^ ind_typename ^ ")") ++
                (if single_constructor then
                  hbrace args
                else
                  hbrace (
                    let union_init =
                      Pp.str ("." ^ cstr_umember) +++
                      Pp.str "=" +++
                      hbrace args
                    in
                    if List.length members_and_accessors = 0 then
                      Pp.str cstr_enum_name
                    else
                      (Pp.str cstr_enum_name ++ Pp.str "," +++ hbrace union_init))) ++
                Pp.str ")"))
      cstr_and_members
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
  let str = Pp.string_of_ppcmds pp in
  add_snippet str;
  (*msg_info_hov pp;*)
  ()

let generate_indimp_heap (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) : unit =
  msg_info_hov (Pp.str "[codegen] generate_indimp_heap:" +++ Printer.pr_econstr_env env sigma coq_type);
  let (mutind, params, ind_names) = generate_indimp_names env sigma coq_type in
  let env =
    CList.fold_left_i
      (fun i env (ind_typename, enum_tag, swfunc, cstr_and_members) ->
        let ind = (mutind, i) in
        let cstr_caselabel_accessors_list =
          List.mapi
            (fun j (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
              let caselabel = if j = 0 then "default" else "case " ^ cstr_enum_name in
              let accessors = List.map (fun (member_type, member_name, accessor) -> accessor) members_and_accessors in
              (cstrid, caselabel, accessors))
            cstr_and_members
        in
        let params' = Array.map (EConstr.to_constr sigma) params in
        let coq_type_i = Constr.mkApp (Constr.mkInd ind, params') in
        ignore (register_ind_match env sigma coq_type_i swfunc cstr_caselabel_accessors_list);
        CList.fold_left_i
          (fun j env (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
            let cstrterm0 = Constr.mkConstruct (ind, j) in
            ignore (codegen_define_or_check_static_arguments env sigma cstrterm0 (List.init (Array.length params) (fun _ -> SorD_S)));
            let (env, sp_inst) = codegen_define_instance env sigma CodeGenPrimitive cstrterm0 (Array.to_list params') (Some { spi_cfunc_name = Some cstrname; spi_presimp_id = None; spi_simplified_id = None }) in
            env)
          1 env cstr_and_members)
      0 env ind_names
  in
  ignore env;
  let pp_ind_types =
    pp_sjoinmap_list
      (fun (ind_typename, enum_tag, swfunc, cstr_and_members) ->
        let pp_enum =
          Pp.hov 0 (
            (Pp.str "enum" +++ Pp.str enum_tag +++
            hovbrace (pp_joinmap_list (Pp.str "," ++ Pp.spc ())
              (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) -> Pp.str cstr_enum_name)
              cstr_and_members) ++ Pp.str ";"))
        in
        let pp_typedef =
          Pp.hov 0 (
            Pp.str "typedef" +++
            Pp.str "enum" +++
            Pp.str enum_tag +++
            Pp.str "*" ++
            Pp.str ind_typename ++
            Pp.str ";")
        in
        pp_enum +++ pp_typedef)
      ind_names
  in
  let pp_ind_imps =
    pp_sjoinmap_list
      (fun (ind_typename, enum_tag, swfunc, cstr_and_members) ->
        let pp_swfunc =
          Pp.h (
            Pp.str "#define" +++
            Pp.str swfunc ++ Pp.str "(x)" +++
            Pp.str "(*(x))")
        in
        let member_decls =
          List.map
            (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
              Pp.hov 0 (Pp.str ("enum " ^ enum_tag) +++ Pp.str "tag;") +++
              pp_sjoinmap_list
                (fun (member_type, member_name, accessor) ->
                  Pp.hov 0 (Pp.str member_type +++ Pp.str member_name ++ Pp.str ";"))
                members_and_accessors)
            cstr_and_members
        in
        let cstr_and_members_with_decls =
          List.map2
            (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) member_def ->
              (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors, member_def))
            cstr_and_members member_decls
        in
        let pp_cstr_struct_defs =
          pp_sjoinmap_list
            (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors, member_decl) ->
              Pp.hov 0 (Pp.str "struct" +++ Pp.str cstr_struct) +++
              vbrace member_decl ++
              Pp.str ";")
            cstr_and_members_with_decls
        in
        let pp_accessors =
          (* #define list_cons_get1(x) (((struct list_cons_struct * )(x))->head) *)
          pp_sjoinmap_list
            (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
              pp_sjoinmap_list
                (fun (member_type, member_name, accessor) ->
                  Pp.h (Pp.str "#define" +++
                        Pp.str accessor ++
                        Pp.str "(x)" +++
                        Pp.str ("(((struct " ^ cstr_struct ^ " *)(x))->" ^ member_name ^ ")")))
                members_and_accessors)
            cstr_and_members
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
          pp_sjoinmap_list
            (fun (cstrid, cstrname, cstr_enum_name, cstr_struct, cstr_umember, members_and_accessors) ->
              let fargs =
                if members_and_accessors = [] then
                  Pp.str "void"
                else
                  pp_joinmap_list (Pp.str "," ++ Pp.spc ())
                    (fun (member_type, member_name, accessor) -> Pp.hov 0 (Pp.str member_type +++ Pp.str member_name))
                    members_and_accessors
              in
              Pp.v 0 (Pp.hov 2 (
                        Pp.str "static" +++
                        Pp.str ind_typename +++
                        Pp.str cstrname ++
                        Pp.str "(" ++ fargs ++ Pp.str ")") +++
                      vbrace (
                        Pp.hov 0 (Pp.str "struct" +++ Pp.str cstr_struct +++ Pp.str "*p;") +++
                        Pp.hov 0 (Pp.str ("if (!(p = malloc(sizeof(*p)))) abort();")) +++
                        Pp.hov 0 (Pp.str "p->tag =" +++ Pp.str cstr_enum_name ++ Pp.str ";") +++
                        pp_sjoinmap_list
                          (fun (member_type, member_name, accessor) ->
                            Pp.hov 0 (Pp.str "p->" ++ Pp.str member_name +++ Pp.str "=" +++ Pp.str member_name ++ Pp.str ";"))
                          members_and_accessors +++
                        Pp.hov 0 (Pp.str "return" +++ Pp.str ("(" ^ ind_typename ^ ")p;")))))
            cstr_and_members
        in
        pp_cstr_struct_defs +++ pp_swfunc +++ pp_accessors +++ pp_cstr)
    ind_names
  in
  let pp = Pp.v 0 (pp_ind_types +++ pp_ind_imps) in
  (*msg_debug_hov (Pp.str (Pp.db_string_of_pp pp));*)
  let str = Pp.string_of_ppcmds pp in
  add_snippet str;
  (*msg_info_hov pp;*)
  ()

let command_indimp (user_coq_type : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  (if ind_coq_type_registered_p coq_type then
    user_err (Pp.str "[codegen] inductive type already configured:" +++ Printer.pr_constr_env env sigma coq_type));
  let coq_type = EConstr.of_constr coq_type in
  if ind_recursive_p env sigma coq_type || ind_mutual_p env sigma coq_type then
    generate_indimp_heap env sigma coq_type
  else
    generate_indimp_immediate env sigma coq_type
