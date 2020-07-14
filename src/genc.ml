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

module IntSet = Set.Make(Int)

open Names
open Pp
open CErrors
open Constr
open EConstr

open Cgenutil
open State
open Ind
open Linear
open Specialize

let abort (x : 'a) : 'a = assert false

let generate_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let printed_type = mangle_term t in
  let c_name = c_id (squeeze_white_spaces printed_type) in
  let ind_cfg = register_ind_type env sigma (EConstr.to_constr sigma t) c_name in
  Feedback.msg_info (v 2
    (Pp.str "[codegen] inductive type translation automatically configured:" +++
     (hv 2 (Pp.str "inductive type:" +++ Printer.pr_econstr_env env sigma t)) +++
     (hv 2 (Pp.str "C type:" +++ Pp.str (escape_as_coq_string c_name))) +++
     Pp.str "(Use \"CodeGen Inductive Type\" for customization)"));
  ind_cfg

let generate_ind_match (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let (mutind, mutind_body, i, oneind_body, args) = get_ind_coq_type env (EConstr.to_constr sigma t) in
  let printed_type = mangle_term t in
  let swfunc = "sw_" ^ c_id (squeeze_white_spaces printed_type) in
  let numcons = Array.length oneind_body.Declarations.mind_consnames in
  let cstr_caselabel_accessors_list =
    List.init numcons
      (fun j ->
        let consname = oneind_body.Declarations.mind_consnames.(j) in
        let cstr = mkConstruct ((mutind, i), j) in
        let args = CArray.map_of_list EConstr.of_constr args in
        let consterm = mkApp (cstr, args) in
        let s = mangle_term consterm in
        let caselabel =
          if j = 0 then "default" else "case " ^ s ^ "_tag"
        in
        let numargs = oneind_body.Declarations.mind_consnrealargs.(j) in
        let accessors =
          List.init numargs
            (fun k -> s ^ "_get_field_" ^ string_of_int k)
        in
        (consname, caselabel, accessors))
  in
  let msgs_defined = List.filter_map (fun x -> x)
    [
      Some (hv 2 (Pp.str "inductive type:" +++ Printer.pr_econstr_env env sigma t));
      Some (hv 2 (Pp.str "switch function:" +++ Pp.str (escape_as_coq_string swfunc)));
      if cstr_caselabel_accessors_list <> [] then
        Some (hv 2 (Pp.str "case labels:" +++
                    pp_sjoin_list (List.map (fun (_, caselabel, _) -> Pp.str (escape_as_coq_string caselabel)) cstr_caselabel_accessors_list)))
      else
        None;
      if List.exists (fun (_, _, accessors) -> accessors <> []) cstr_caselabel_accessors_list then
         Some (hv 2 (Pp.str "field accessors:" +++
                     pp_sjoin_list (List.concat (List.map (fun (_, _, accessors) -> List.map (fun access -> Pp.str (escape_as_coq_string access)) accessors) cstr_caselabel_accessors_list))))
      else
        None
    ]
  in
  Feedback.msg_info (v 2
    (Pp.str "[codegen] match-expression translation automatically configured:" +++
     pp_sjoin_list msgs_defined +++
     Pp.str "(Use \"CodeGen Inductive Match\" for customization)"));
  register_ind_match env sigma (EConstr.to_constr sigma t) swfunc cstr_caselabel_accessors_list

let get_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  match ConstrMap.find_opt (EConstr.to_constr sigma t) !ind_config_map with
  | Some ind_cfg -> ind_cfg
  | None -> generate_ind_config env sigma t

let c_typename (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : string =
  match EConstr.kind sigma t with
  | Prod _ -> "codegen_closure_t" (* codegen_closure_t is not used yet *)
  | _ -> (get_ind_config env sigma t).c_type

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

let case_cstrfield (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) (k : int) : string =
  let ind_cfg = get_ind_config env sigma t in
  let ind_cfg =
    match ind_cfg.c_swfunc with
    | Some _ -> ind_cfg
    | None -> generate_ind_match env sigma t
  in
  ind_cfg.cstr_configs.(j-1).c_accessors.(k)

let local_gensym_id : (int ref) list ref = ref []

let local_gensym_with (f : unit -> 'a) : 'a =
  local_gensym_id := (ref 0) :: !local_gensym_id;
  let ret = f () in
  local_gensym_id := List.tl !local_gensym_id;
  ret

let local_gensym () : string =
  let idref = List.hd !local_gensym_id in
  let n = !idref in
  idref := n + 1;
  "tmp" ^ string_of_int n

let str_of_name (name : Name.t) : string =
  match name with
  | Name.Anonymous -> user_err (Pp.str "[codegen] str_of_name with anonymous name")
  | Name.Name id -> Id.to_string id

let str_of_annotated_name (name : Name.t Context.binder_annot) : string =
  str_of_name (Context.binder_name name)

let gen_farg (farg : (*varname*)string * (*vartype*)string) : Pp.t =
  let (var, ty) = farg in
  hov 2 (str ty +++ str var)

let gen_fargs (fargs : (string * string) list) : Pp.t =
  match fargs with
  | [] -> str "void"
  | farg1 :: rest ->
      List.fold_left
        (fun pp farg -> pp ++ str "," +++ gen_farg farg)
        (gen_farg farg1)
        rest

let genc_assign (lhs : Pp.t) (rhs : Pp.t) : Pp.t =
  Pp.hov 0 (lhs +++ str "=" +++ rhs ++ str ";")

let gen_return (arg : Pp.t) : Pp.t =
  hov 0 (str "return" +++ arg ++ str ";")

let gen_void_return (retvar : string) (arg : Pp.t) : Pp.t =
  genc_assign (str retvar) arg +++ str "return;"

let gen_funcall (c_fname : string) (argvars : string array) : Pp.t =
  str c_fname ++ str "(" ++
  pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
  str ")"

let gen_app_const_construct (env : Environ.env) (sigma : Evd.evar_map) (f : EConstr.t) (argvars : string array) : Pp.t =
  let sp_inst =
    match ConstrMap.find_opt (EConstr.to_constr sigma f) !gallina_instance_map with
    | None ->
        (match EConstr.kind sigma f with
        | Constr.Const (ctnt, _) ->
            user_err (Pp.str "[codegen] C function name not configured:" +++ Printer.pr_constant env ctnt)
        | Constr.Construct (cstr, _) ->
            user_err (Pp.str "[codegen] C constructor name not configured:" +++ Printer.pr_constructor env cstr)
        | _ ->
            user_err (Pp.str "[codegen:bug] gen_app_const_construct expects Const or Construct"))
    | Some (sp_cfg, sp_inst) ->
        sp_inst
  in
  let c_fname = sp_inst.sp_cfunc_name in
  let gen_constant = Array.length argvars = 0 && sp_inst.sp_gen_constant in
  if gen_constant then
    str c_fname
  else
    gen_funcall c_fname argvars

let get_ctnt_type_body_from_cfunc (cfunc_name : string) : Constant.t * Constr.types * Constr.t =
  let (sp_cfg, sp_inst) =
    match CString.Map.find_opt cfunc_name !cfunc_instance_map with
    | None ->
        user_err (Pp.str "[codegen] C function name not found:" +++
                  Pp.str cfunc_name)
    | Some (sp_cfg, sp_inst) -> (sp_cfg, sp_inst)
  in
  let (env, ctnt) =
    match sp_inst.sp_specialization_name with
    | SpExpectedId id ->
        codegen_specialization_specialize1 cfunc_name (* modify global env *)
    | SpDefinedCtnt ctnt -> (Global.env (), ctnt)
  in
  (*Feedback.msg_debug (Pp.str "[codegen:get_ctnt_type_body_from_cfunc] ctnt=" ++ Printer.pr_constant env ctnt);*)
  let cdef = Environ.lookup_constant ctnt env in
  let ty = cdef.Declarations.const_type in
  match Global.body_of_constant_body Library.indirect_accessor cdef with
  | None -> user_err (Pp.str "[codegen] couldn't obtain the body:" +++
                      Printer.pr_constant env ctnt)
  | Some (body,_, _) -> (ctnt, ty, body)

let hbrace (pp : Pp.t) : Pp.t =
  h 2 (str "{" +++ pp ++ brk (1,-2) ++ str "}")

let hovbrace (pp : Pp.t) : Pp.t =
  hv 2 (str "{" +++ pp ++ brk (1,-2) ++ str "}")

let vbrace (pp : Pp.t) : Pp.t =
  v 2 (str "{" +++ pp ++ brk (1,-2) ++ str "}")

let local_vars : ((string * string) list ref) list ref = ref []

let local_vars_with (f : unit -> 'a) : (string * string) list * 'a =
  let vars = ref [] in
  let old = !local_vars in
  local_vars := vars :: old;
  let ret = f () in
  local_vars := old;
  (List.rev !vars, ret)

let add_local_var (c_type : string) (c_var : string) : unit =
  if !local_vars = [] then
    user_err (Pp.str "[codegen:bug] add_local_var is called outside of local_vars_with");
  let vars = List.hd !local_vars in
  match List.find_opt (fun (c_type1, c_var1) -> c_var1 = c_var) !vars with
  | Some (c_type1, c_var1) ->
      if c_type1 <> c_type then
        user_err (Pp.str "[codegen:bug] add_local_var : inconsistent typed variable")
      else
        ()
  | None -> vars := (c_type, c_var) :: !vars

let id_of_name (name : Name.t) : Id.t =
  match name with
  | Name.Anonymous -> user_err (Pp.str "[codegen:bug] id_of_name require non-anonymous Name")
  | Name.Name id -> id

let id_of_annotated_name (name : Name.t Context.binder_annot) : Id.t =
  id_of_name (Context.binder_name name)

let carg_of_garg (env : Environ.env) (i : int) : string =
  let x = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
  match x with
  | Name.Anonymous -> user_err (Pp.str "[codegen:bug] carg_of_garg require non-anonymous Name")
  | Name.Name id -> Id.to_string id

type fixfunc_info = {
  fixfunc_inlinable: bool;
  fixfunc_used_as_call: bool;
  fixfunc_used_as_goto: bool;
  fixfunc_formal_arguments: (string * string) list; (* [(varname1, vartype1); ...] *)
  fixfunc_return_type: string;
  fixfunc_top_call: string option; (* by detect_top_calls *)
  fixfunc_c_name: string; (* by determine_fixfunc_c_names *)
  fixfunc_outer_variables: (string * string) list; (* [(varname1, vartype1); ...] *) (* by set_fixinfo_naive_outer_variables and filter_fixinfo_outer_variables *)
}

type fixinfo_t = (Id.t, fixfunc_info) Hashtbl.t

let show_fixinfo (env : Environ.env) (sigma : Evd.evar_map) (fixinfo : fixinfo_t) : unit =
  Hashtbl.iter
    (fun fixfunc info ->
      Feedback.msg_debug (hv 2 (Pp.str (Id.to_string fixfunc) ++ Pp.str ":" +++
        Pp.str "inlinable=" ++ Pp.bool info.fixfunc_inlinable +++
        Pp.str "used_as_call=" ++ Pp.bool info.fixfunc_used_as_call +++
        Pp.str "used_as_goto=" ++ Pp.bool info.fixfunc_used_as_goto +++
        Pp.str "formal_arguments=(" ++ pp_join_list (Pp.str ",") (List.map (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str ty) info.fixfunc_formal_arguments) ++ Pp.str ")" +++
        Pp.str "return_type=" ++ Pp.str info.fixfunc_return_type +++
        Pp.str "top_call=" ++ (match info.fixfunc_top_call with None -> Pp.str "None" | Some top -> Pp.str ("Some " ^ top)) +++
        Pp.str "c_name=" ++ Pp.str info.fixfunc_c_name +++
        Pp.str "outer_variables=(" ++ pp_join_list (Pp.str ",") (List.map (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str ty) info.fixfunc_outer_variables) ++ Pp.str ")" +++
        mt ()
      )))
    fixinfo

let rec c_args_and_ret_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((string * string) list) * string =
  match EConstr.kind sigma term with
  | Prod (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let (rest_args, ret_type) = c_args_and_ret_type env2 sigma b in
      (((str_of_annotated_name x, c_typename env sigma t) :: rest_args), ret_type)
  | _ ->
      ([], c_typename env sigma term)

let rec detect_inlinable_fixterm_rec (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (numargs : int) :
    (* variables at tail position *) IntSet.t *
    (* variables at non-tail position *) IntSet.t *
    (* inlinable fixterms *) Id.Set.t =
  (*Feedback.msg_debug (Pp.str "[codegen:detect_inlinable_fixterm_rec] start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs);*)
  let result = detect_inlinable_fixterm_rec1 env sigma term numargs in
  (*let (tailset, nontailset, argset) = result in
  Feedback.msg_debug (hov 2 (Pp.str "[codegen:detect_inlinable_fixterm_rec] end:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs
    +++
    Pp.str "tailset={" ++
    pp_join_list (Pp.str ",")
      (List.map
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name
          )
        (IntSet.elements tailset)) ++
    Pp.str "}"
    +++
    Pp.str "nontailset={" ++
    pp_join_list (Pp.str ",")
      (List.map
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name)
        (IntSet.elements nontailset)) ++
    Pp.str "}" +++
    Pp.str "inlinable-fixterms={" ++
    xxx
    Pp.str "}"));
    *)
  result
and detect_inlinable_fixterm_rec1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (numargs : int) :
    (* variables at tail position *) IntSet.t *
    (* variables at non-tail position *) IntSet.t *
    (* inlinable fixterms *) Id.Set.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i -> (IntSet.singleton i, IntSet.empty, Id.Set.empty)
  | Int _ | Float _ | Const _ | Construct _ -> (IntSet.empty, IntSet.empty, Id.Set.empty)
  | Proj (proj, e) ->
      (* e must be a Rel which type is inductive (non-function) type *)
      (IntSet.empty, IntSet.empty, Id.Set.empty)
  | App (f, args) ->
      let (tailset_f, nontailset_f, inlinable_f) = detect_inlinable_fixterm_rec env sigma f (Array.length args + numargs) in
      let nontailset = Array.fold_left (fun set arg -> IntSet.add (destRel sigma arg) set) nontailset_f args in
      (tailset_f, nontailset, inlinable_f)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let (tailset_e, nontailset_e, inlinable_e) = detect_inlinable_fixterm_rec env sigma e 0 in
      let (tailset_b, nontailset_b, inlinable_b) = detect_inlinable_fixterm_rec env2 sigma b numargs in
      let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
      let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
      let nontailset = IntSet.union
        (IntSet.union tailset_e nontailset_e)
        nontailset_b
      in
      let inlinable = Id.Set.union inlinable_e inlinable_b in
      (tailset_b, nontailset, inlinable)
  | Case (ci, p, item, branches) ->
      (* item must be a Rel which type is inductive (non-function) type *)
      let branches_result = Array.mapi
        (fun i br -> detect_inlinable_fixterm_rec env sigma br
          (ci.Constr.ci_cstr_nargs.(i) + numargs))
        branches
      in
      let tailset =
        Array.fold_left
          (fun set (tailset_br, nontailset_br, inlinable_br) ->
            IntSet.union set tailset_br)
          IntSet.empty
          branches_result
      in
      let nontailset =
        Array.fold_left
          (fun set (tailset_br, nontailset_br, inlinable_br) ->
            IntSet.union set nontailset_br)
          IntSet.empty branches_result
      in
      let inlinable =
        Array.fold_left
          (fun set (tailset_br, nontailset_br, inlinable_br) ->
            Id.Set.union set inlinable_br)
          Id.Set.empty branches_result
      in
      (tailset, nontailset, inlinable)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      if numargs = 0 then
        (* closure creation *)
        let (tailset_b, nontailset_b, inlinable_b) = detect_inlinable_fixterm_rec env2 sigma b (numargs_of_exp env sigma term) in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        let nontailset = IntSet.union tailset_b nontailset_b in
        (IntSet.empty, nontailset, inlinable_b)
      else
        let (tailset_b, nontailset_b, inlinable_b) = detect_inlinable_fixterm_rec env2 sigma b (numargs-1) in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        (tailset_b, nontailset_b, inlinable_b)
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let n = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let fixfuncs_result = Array.mapi
        (fun i f -> detect_inlinable_fixterm_rec env2 sigma f
          (numargs_of_type env sigma tary.(i)))
        fary
      in
      let tailset_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f, inlinable_f) ->
            IntSet.union set tailset_f)
          IntSet.empty fixfuncs_result
      in
      let nontailset_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f, inlinable_f) ->
            IntSet.union set nontailset_f)
          IntSet.empty fixfuncs_result
      in
      let inlinable_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f, inlineable_f) ->
            Id.Set.union set inlineable_f)
          Id.Set.empty fixfuncs_result
      in
      let inlinable_fixterm = not (IntSet.exists ((>=) n) nontailset_fs) in
      let inlinable_fs' =
        if inlinable_fixterm then
          Id.Set.add (id_of_annotated_name nary.(i)) inlinable_fs
        else
          inlinable_fs
      in
      let tailset_fs' = IntSet.map (fun k -> k - n) (IntSet.filter ((<) n) tailset_fs) in
      let nontailset_fs' = IntSet.map (fun k -> k - n) (IntSet.filter ((<) n) nontailset_fs) in
      if numargs < numargs_of_type env sigma tary.(i) || (* closure creation *)
         not inlinable_fixterm then
        (* At least one fix-bounded function is used at
          non-tail position or argument position.
          Assuming fix-bounded functions are strongly-connected,
          there is no tail position in this fix term. *)
        let nontailset = IntSet.union tailset_fs' nontailset_fs' in
        (IntSet.empty, nontailset, inlinable_fs')
      else
        (tailset_fs', nontailset_fs', inlinable_fs')

let detect_inlinable_fixterm (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (numargs : int) : Id.Set.t =
  let (tailset, nontailset, inlinable) = detect_inlinable_fixterm_rec env sigma term numargs in
  inlinable

let rec collect_fix_usage (fixinfo : fixinfo_t) (inlinable_fixterms : Id.Set.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) (numargs : int) (tail_position : bool) :
    (* variables at tail position *) IntSet.t *
    (* variables at non-tail position *) IntSet.t =
  (*Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage] start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs +++
    Pp.str "tail_position=" ++ Pp.bool tail_position);*)
  let result = collect_fix_usage1 fixinfo inlinable_fixterms env sigma term numargs tail_position in
  (*let (tailset, nontailset) = result in
  Feedback.msg_debug (hov 2 (Pp.str "[codegen:collect_fix_usage] end:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs
    +++
    Pp.str "tailset={" ++
    pp_join_list (Pp.str ",")
      (List.map
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name
          )
        (IntSet.elements tailset)) ++
    Pp.str "}"
    +++
    Pp.str "nontailset={" ++
    pp_join_list (Pp.str ",")
      (List.map
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name)
        (IntSet.elements nontailset)) ++
    Pp.str "}"));*)
  result
and collect_fix_usage1 (fixinfo : fixinfo_t) (inlinable_fixterms : Id.Set.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) (numargs : int) (tail_position : bool) :
    (* variables at tail position *) IntSet.t *
    (* variables at non-tail position *) IntSet.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i -> (IntSet.singleton i, IntSet.empty)
  | Int _ | Float _ | Const _ | Construct _ -> (IntSet.empty, IntSet.empty)
  | Proj (proj, e) ->
      (* e must be a Rel which type is inductive (non-function) type *)
      (IntSet.empty, IntSet.empty)
  | App (f, args) ->
      let (tailset_f, nontailset_f) = collect_fix_usage fixinfo inlinable_fixterms env sigma f (Array.length args + numargs) tail_position in
      let nontailset = Array.fold_left (fun set arg -> IntSet.add (destRel sigma arg) set) nontailset_f args in
      (tailset_f, nontailset)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let (tailset_e, nontailset_e) = collect_fix_usage fixinfo inlinable_fixterms env sigma e 0 false in
      let (tailset_b, nontailset_b) = collect_fix_usage fixinfo inlinable_fixterms env2 sigma b numargs tail_position in
      let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
      let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
      let nontailset = IntSet.union
        (IntSet.union tailset_e nontailset_e)
        nontailset_b
      in
      (tailset_b, nontailset)
  | Case (ci, p, item, branches) ->
      (* item must be a Rel which type is inductive (non-function) type *)
      let branches_result = Array.mapi
        (fun i br -> collect_fix_usage fixinfo inlinable_fixterms env sigma br
          (ci.Constr.ci_cstr_nargs.(i) + numargs) tail_position)
        branches
      in
      let tailset =
        Array.fold_left
          (fun set (tailset_br, nontailset_br) ->
            IntSet.union set tailset_br)
          IntSet.empty
          branches_result
      in
      let nontailset =
        Array.fold_left
          (fun set (tailset_br, nontailset_br) ->
            IntSet.union set nontailset_br)
          IntSet.empty branches_result
      in
      (tailset, nontailset)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      if numargs = 0 then
        (* closure creation *)
        let (tailset_b, nontailset_b) = collect_fix_usage fixinfo inlinable_fixterms env2 sigma b (numargs_of_exp env sigma term) true in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        let nontailset = IntSet.union tailset_b nontailset_b in
        (IntSet.empty, nontailset)
      else
        let (tailset_b, nontailset_b) = collect_fix_usage fixinfo inlinable_fixterms env2 sigma b (numargs-1) tail_position in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        (tailset_b, nontailset_b)
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let inlinable = Id.Set.mem (id_of_annotated_name nary.(i)) inlinable_fixterms in
      let n = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let need_function =
        numargs < numargs_of_type env sigma tary.(i) || (* closure creation *)
        (not tail_position && not inlinable)
      in
      let fixfuncs_result =
        if need_function then
          Array.mapi
            (fun i f -> collect_fix_usage fixinfo inlinable_fixterms env2 sigma f
              (numargs_of_type env sigma tary.(i)) true)
            fary
        else
          Array.mapi
            (fun i f -> collect_fix_usage fixinfo inlinable_fixterms env2 sigma f
              (numargs_of_type env sigma tary.(i)) tail_position)
            fary
      in
      let tailset_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f) ->
            IntSet.union set tailset_f)
          IntSet.empty fixfuncs_result
      in
      let nontailset_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f) ->
            IntSet.union set nontailset_f)
          IntSet.empty fixfuncs_result
      in
      for j = 0 to n - 1 do
        let fname = Context.binder_name nary.(j) in
        let k = n - j in
        let used_as_goto = IntSet.mem k tailset_fs in
        let used_as_call =
          (if j = i then need_function else false) ||
          IntSet.mem k nontailset_fs
        in
        let (formal_arguments, return_type) = c_args_and_ret_type env sigma tary.(j) in
        (*Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] fname=" ++ Names.Name.print fname);
        Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] tail_position=" ++ Pp.bool tail_position);
        Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] inlinable=" ++ Pp.bool inlinable);
        Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] i=" ++ Pp.int i);
        Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] j=" ++ Pp.int j);
        Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] need_function=" ++ Pp.bool need_function);
        Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] used_as_goto=" ++ Pp.bool used_as_goto);
        Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage1] used_as_call=" ++ Pp.bool used_as_call);*)
        Hashtbl.add fixinfo (id_of_name fname) {
          fixfunc_inlinable = inlinable;
          fixfunc_used_as_call = used_as_call;
          fixfunc_used_as_goto = used_as_goto;
          fixfunc_formal_arguments = formal_arguments;
          fixfunc_return_type = return_type;
          fixfunc_top_call = None; (* dummy. updated detect_top_calls *)
          fixfunc_c_name = "dummy"; (* dummy. updated by determine_fixfunc_c_names *)
          fixfunc_outer_variables = []; (* dummy. updated by set_fixinfo_naive_outer_variables *)
        }
      done;
      let tailset_fs' = IntSet.map (fun k -> k - n) (IntSet.filter ((<) n) tailset_fs) in
      let nontailset_fs' = IntSet.map (fun k -> k - n) (IntSet.filter ((<) n) nontailset_fs) in
        if need_function then
          (IntSet.empty, IntSet.union tailset_fs' nontailset_fs')
        else
          (tailset_fs', nontailset_fs')

let rec detect_top_calls_rec (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t)
    (top_c_func_name : string) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      detect_top_calls_rec env2 sigma fixinfo top_c_func_name e
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      detect_top_calls_rec env2 sigma fixinfo top_c_func_name fary.(i);
      let key = id_of_annotated_name nary.(i) in
      let usage = Hashtbl.find fixinfo key in
      Hashtbl.replace fixinfo key {
        fixfunc_inlinable = usage.fixfunc_inlinable;
        fixfunc_used_as_call = usage.fixfunc_used_as_call;
        fixfunc_used_as_goto = usage.fixfunc_used_as_goto;
        fixfunc_formal_arguments = usage.fixfunc_formal_arguments;
        fixfunc_return_type = usage.fixfunc_return_type;
        fixfunc_top_call = Some top_c_func_name;
        fixfunc_c_name = usage.fixfunc_c_name;
        fixfunc_outer_variables = usage.fixfunc_outer_variables;
      }
  (* xxx: consider App *)
  | _ -> ()

let detect_top_calls (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t)
    (top_c_func_name : string) (term : EConstr.t) : unit =
  detect_top_calls_rec env sigma fixinfo top_c_func_name term

let rec set_fixinfo_naive_outer_variables (fixinfo : fixinfo_t) (env : Environ.env) (sigma : Evd.evar_map)
    (outer : (string * string) list) (term : EConstr.t) : unit =
  let result = set_fixinfo_naive_outer_variables1 fixinfo env sigma outer term in
  result
and set_fixinfo_naive_outer_variables1 (fixinfo : fixinfo_t) (env : Environ.env) (sigma : Evd.evar_map)
    (outer : (string * string) list) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i -> ()
  | Int _ | Float _ | Const _ | Construct _ -> ()
  | Proj (proj, e) -> ()
  | App (f, args) ->
      set_fixinfo_naive_outer_variables fixinfo env sigma outer f
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let outer2 = (str_of_annotated_name x, c_typename env sigma t) :: outer in
      set_fixinfo_naive_outer_variables fixinfo env sigma outer e;
      set_fixinfo_naive_outer_variables fixinfo env2 sigma outer2 b
  | Case (ci, p, item, branches) ->
      Array.iter
        (fun br ->
          set_fixinfo_naive_outer_variables fixinfo env sigma outer br)
        branches
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let outer2 = (str_of_annotated_name x, c_typename env sigma t) :: outer in
      set_fixinfo_naive_outer_variables fixinfo env2 sigma outer2 b
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let n = Array.length nary in
      for j = 0 to n - 1 do
        let key = id_of_annotated_name nary.(j) in
        let usage = Hashtbl.find fixinfo key in
        Hashtbl.replace fixinfo key {
          fixfunc_inlinable = usage.fixfunc_inlinable;
          fixfunc_used_as_call = usage.fixfunc_used_as_call;
          fixfunc_used_as_goto = usage.fixfunc_used_as_goto;
          fixfunc_formal_arguments = usage.fixfunc_formal_arguments;
          fixfunc_return_type = usage.fixfunc_return_type;
          fixfunc_top_call = usage.fixfunc_top_call;
          fixfunc_c_name = usage.fixfunc_c_name;
          fixfunc_outer_variables = List.rev outer;
        }
      done;
      let env2 = EConstr.push_rec_types prec env in
      Array.iter
        (fun f ->
          set_fixinfo_naive_outer_variables fixinfo env2 sigma outer f)
        fary

let rec fixterm_free_variables_rec (env : Environ.env) (sigma : Evd.evar_map)
    (result : (Id.t, Id.Set.t) Hashtbl.t) (term : EConstr.t) : Id.Set.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i ->
      let decl = Environ.lookup_rel i env in
      let name = Context.Rel.Declaration.get_name decl in
      Id.Set.singleton (id_of_name name)
  | Int _ | Float _ | Const _ | Construct _ -> Id.Set.empty
  | Proj (proj, e) -> fixterm_free_variables_rec env sigma result e
  | App (f, args) ->
      let fv_f = fixterm_free_variables_rec env sigma result f in
      let ids = Array.map
        (fun arg ->
          let i = destRel sigma arg in
          let decl = Environ.lookup_rel i env in
          let name = Context.Rel.Declaration.get_name decl in
          id_of_name name)
        args
      in
      Array.fold_right Id.Set.add ids fv_f
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let id = id_of_annotated_name x in
      let fv_e = fixterm_free_variables_rec env sigma result e in
      let fv_b = fixterm_free_variables_rec env2 sigma result b in
      Id.Set.union fv_e (Id.Set.remove id fv_b)
  | Case (ci, p, item, branches) ->
      let item_id =
        let i = destRel sigma item in
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        id_of_name name
      in
      let fv_branches =
        Array.map (fixterm_free_variables_rec env sigma result) branches
      in
      Array.fold_right Id.Set.union fv_branches (Id.Set.singleton item_id)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let id = id_of_annotated_name x in
      let fv_b = fixterm_free_variables_rec env2 sigma result b in
      Id.Set.remove id fv_b
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ids = Array.map id_of_annotated_name nary in
      let fv_fary =
        Array.map (fixterm_free_variables_rec env2 sigma result) fary
      in
      let fv =
        Id.Set.diff
          (Array.fold_right Id.Set.union fv_fary Id.Set.empty)
          (Array.fold_right Id.Set.add ids Id.Set.empty)
      in
      Hashtbl.add result (id_of_annotated_name nary.(i)) fv;
      fv

let fixterm_free_variables (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : (Id.t, Id.Set.t) Hashtbl.t =
  let result = Hashtbl.create 0 in
  ignore (fixterm_free_variables_rec env sigma result term);
  result

let rec fixterm_fixfunc_relation_rec (env : Environ.env) (sigma : Evd.evar_map)
    (fixterm_to_fixfuncs : (Id.t, Id.Set.t) Hashtbl.t)
    (fixfunc_to_fixterm : (Id.t, Id.t) Hashtbl.t)
    (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i -> ()
  | Int _ | Float _ | Const _ | Construct _ -> ()
  | Proj (proj, e) -> fixterm_fixfunc_relation_rec env sigma fixterm_to_fixfuncs fixfunc_to_fixterm e
  | App (f, args) ->
      fixterm_fixfunc_relation_rec env sigma fixterm_to_fixfuncs fixfunc_to_fixterm f
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      fixterm_fixfunc_relation_rec env sigma fixterm_to_fixfuncs fixfunc_to_fixterm e;
      fixterm_fixfunc_relation_rec env2 sigma fixterm_to_fixfuncs fixfunc_to_fixterm b
  | Case (ci, p, item, branches) ->
      Array.iter
        (fixterm_fixfunc_relation_rec env sigma fixterm_to_fixfuncs fixfunc_to_fixterm)
        branches
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      fixterm_fixfunc_relation_rec env2 sigma fixterm_to_fixfuncs fixfunc_to_fixterm b
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let fixterm_id = id_of_annotated_name nary.(i) in
      let fixfunc_ids = Array.map id_of_annotated_name nary in
      for j = 0 to Array.length nary - 1 do
        let fixfunc_id = fixfunc_ids.(j) in
        Hashtbl.add fixfunc_to_fixterm fixfunc_id fixterm_id
      done;
      Hashtbl.add fixterm_to_fixfuncs fixterm_id
	(Array.fold_right Id.Set.add fixfunc_ids Id.Set.empty);
      let env2 = EConstr.push_rec_types prec env in
      Array.iter
        (fixterm_fixfunc_relation_rec env2 sigma fixterm_to_fixfuncs fixfunc_to_fixterm)
        fary

let fixterm_fixfunc_relation (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : (Id.t, Id.Set.t) Hashtbl.t * (Id.t, Id.t) Hashtbl.t =
  let fixterm_to_fixfuncs = Hashtbl.create 0 in
  let fixfunc_to_fixterm = Hashtbl.create 0 in
  fixterm_fixfunc_relation_rec env sigma fixterm_to_fixfuncs fixfunc_to_fixterm term;
  (fixterm_to_fixfuncs, fixfunc_to_fixterm)

let compute_outer_variables (env : Environ.env) (sigma : Evd.evar_map)
    (fixterm_to_fixfuncs : (Id.t, Id.Set.t) Hashtbl.t)
    (fixfunc_to_fixterm : (Id.t, Id.t) Hashtbl.t)
    (fixterm_free_variables : (Id.t, Id.Set.t) Hashtbl.t) :
    ((*fixterm_id*)Id.t, (*outer_variables*)Id.Set.t) Hashtbl.t =
  let fixfuncs =
    Hashtbl.fold
      (fun fixterm_id fixfunc_ids set ->
        Id.Set.union fixfunc_ids set)
      fixterm_to_fixfuncs
      Id.Set.empty
  in
  let fixterm_outer_variables = Hashtbl.create 0 in
  Hashtbl.iter
    (fun fixterm_id fixterm_fv ->
      let q = ref fixterm_fv in
      let outer_variables = ref Id.Set.empty in
      while not (Id.Set.is_empty !q) do
        let id = Id.Set.choose !q in
        q := Id.Set.remove id !q;
        if not (Id.Set.mem id !outer_variables) then
          (outer_variables := Id.Set.add id !outer_variables;
          match Hashtbl.find_opt fixfunc_to_fixterm id with
          | None -> ()
          | Some fixterm2_id ->
            match Hashtbl.find_opt fixterm_free_variables fixterm2_id with
            | None -> ()
            | Some fv ->
                q := Id.Set.union !q fv)
      done;
      Hashtbl.add fixterm_outer_variables fixterm_id
        (Id.Set.diff !outer_variables fixfuncs))
    fixterm_to_fixfuncs;
  fixterm_outer_variables

let filter_fixinfo_outer_variables (fixinfo : fixinfo_t)
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : unit =
  let (fixterm_to_fixfuncs, fixfunc_to_fixterm) = fixterm_fixfunc_relation env sigma term in
  let fixterm_free_variables = fixterm_free_variables env sigma term in
  let outer_variables = compute_outer_variables env sigma fixterm_to_fixfuncs fixfunc_to_fixterm fixterm_free_variables in
  Hashtbl.filter_map_inplace
    (fun (fixfunc_id : Id.t) (info : fixfunc_info) ->
      let fixterm_id = Hashtbl.find fixfunc_to_fixterm fixfunc_id in
      if info.fixfunc_top_call <> None then
        Some info
      else
        let ov = List.filter
          (fun (varname, vartype) -> Id.Set.mem (Id.of_string varname) (Hashtbl.find outer_variables fixterm_id))
          info.fixfunc_outer_variables
        in
        Some { info with fixfunc_outer_variables = ov })
    fixinfo

let compute_called_fixfuncs (fixinfo : fixinfo_t) : fixfunc_info list =
  Hashtbl.fold
    (fun fixfunc_id info fixfuncs ->
      if info.fixfunc_used_as_call &&
         info.fixfunc_top_call = None then
        info :: fixfuncs
      else
        fixfuncs)
    fixinfo
    []

let determine_fixfunc_c_names (fixinfo : fixinfo_t) : unit =
  Hashtbl.filter_map_inplace
    (fun (fixfunc_id : Id.t) (info : fixfunc_info) ->
      let c_name =
        if info.fixfunc_used_as_call &&
           info.fixfunc_top_call = None then
          global_gensym_with_id fixfunc_id
        else
          Id.to_string fixfunc_id
      in
      Some { info with fixfunc_c_name = c_name })
    fixinfo

let collect_fix_info (env : Environ.env) (sigma : Evd.evar_map) (name : string) (term : EConstr.t) : fixinfo_t =
  let fixinfo = Hashtbl.create 0 in
  let numargs = numargs_of_exp env sigma term in
  let inlinable_fixterms = detect_inlinable_fixterm env sigma term numargs in
  ignore (collect_fix_usage fixinfo inlinable_fixterms env sigma term numargs true);
  detect_top_calls env sigma fixinfo name term;
  determine_fixfunc_c_names fixinfo;
  set_fixinfo_naive_outer_variables fixinfo env sigma [] term;
  filter_fixinfo_outer_variables fixinfo env sigma term;
  show_fixinfo env sigma fixinfo;
  fixinfo

let gen_switch_without_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  v 0 (
  hov 0 (str "switch" +++ str "(" ++ swexpr ++ str ")") +++
  vbrace (pp_join_ary (spc ())
    (Array.map
      (fun (caselabel, pp_branch) ->
        str caselabel ++ str ":" ++ Pp.brk (1,2) ++ v 0 pp_branch)
      branches)))

let gen_switch_with_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  gen_switch_without_break swexpr
    (Array.map
      (fun (caselabel, pp_branch) ->
        (caselabel, pp_branch +++ str "break;"))
      branches)

let rec decompose_lam_n_env (env : Environ.env) (sigma : Evd.evar_map) (n : int) (term : EConstr.t) : (Environ.env * EConstr.t) =
  if n = 0 then
    (env, term)
  else
    match EConstr.kind sigma term with
    | Lambda (x,t,e) ->
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        decompose_lam_n_env env2 sigma (n-1) e
    | _ ->
      user_err (str "[codegen:bug:decompose_lam_n_env] unexpected non-lambda term: " ++ Printer.pr_econstr_env env sigma term)

let gen_match (used : Id.Set.t) (gen_switch : Pp.t -> (string * Pp.t) array -> Pp.t)
    (gen_branch_body : Environ.env -> Evd.evar_map -> EConstr.t -> string list -> Pp.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (ci : case_info) (predicate : EConstr.t) (item : EConstr.t) (branches : EConstr.t array)
    (cargs : string list) : Pp.t =
  (*Feedback.msg_debug (Pp.str "[codegen] gen_match:1");*)
  let item_relindex = destRel sigma item in
  let item_type = Context.Rel.Declaration.get_type (Environ.lookup_rel item_relindex env) in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_match: item_type=" ++ Printer.pr_econstr_env env sigma (EConstr.of_constr item_type));*)
  let item_cvar = carg_of_garg env item_relindex in
  (*let result_type = Retyping.get_type_of env sigma term in*)
  (*let result_type = Reductionops.nf_all env sigma result_type in*)
  (*Feedback.msg_debug (Pp.str "[codegen] gen_match:2");*)
  let gen_branch accessors br =
    let m = Array.length accessors in
    let (env2, branch_body) = decompose_lam_n_env env sigma m br in
    let c_vars = Array.map
      (fun i ->
        let env3 = Environ.pop_rel_context (i-1) env2 in
        let decl = Environ.lookup_rel 1 env3 in
        let (x, _, t) = Context.Rel.Declaration.to_tuple decl in
        let c_id = id_of_annotated_name x in
        let c_var = Id.to_string c_id in
        (if Id.Set.mem c_id used then
          let env4 = Environ.pop_rel_context 1 env3 in
          let t = EConstr.of_constr t in
          add_local_var (c_typename env4 sigma t) c_var);
        c_var)
      (array_rev (iota_ary 1 m))
    in
    let c_field_access =
      pp_sjoin_ary
        (Array.map2
          (fun c_var access ->
            if Id.Set.mem (Id.of_string c_var) used then
              genc_assign (str c_var)
                (str access ++ str "(" ++ str item_cvar ++ str ")")
            else
              mt ())
          c_vars accessors)
    in
    let c_branch_body = gen_branch_body env2 sigma branch_body cargs in
    c_field_access +++ c_branch_body
  in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_match:3");*)
  let n = Array.length branches in
  let caselabel_accessors =
    Array.map
      (fun j ->
        (*Feedback.msg_debug (Pp.str "[codegen] gen_match:30");*)
        (case_cstrlabel env sigma (EConstr.of_constr item_type) j,
         Array.map
           (case_cstrfield env sigma (EConstr.of_constr item_type) j)
           (iota_ary 0 ci.ci_cstr_nargs.(j-1))))
      (iota_ary 1 n)
  in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_match:4");*)
  if n = 1 then
    ((*Feedback.msg_debug (Pp.str "[codegen] gen_match:5");*)
    let accessors = snd caselabel_accessors.(0) in
    let br = branches.(0) in
    gen_branch accessors br)
  else
    ((*Feedback.msg_debug (Pp.str "[codegen] gen_match:6");*)
    let swfunc = case_swfunc env sigma (EConstr.of_constr item_type) in
    let swexpr = if swfunc = "" then str item_cvar else str swfunc ++ str "(" ++ str item_cvar ++ str ")" in
    (*Feedback.msg_debug (Pp.str "[codegen] gen_match:7");*)
    gen_switch swexpr
      (Array.mapi
        (fun i br ->
          let (caselabel, accessors) = caselabel_accessors.(i) in
          (caselabel, gen_branch accessors br))
        branches))

let gen_proj (env : Environ.env) (sigma : Evd.evar_map)
    (pr : Projection.t) (item : EConstr.t) : Pp.t =
  let item_relindex = destRel sigma item in
  let item_type = Context.Rel.Declaration.get_type (Environ.lookup_rel item_relindex env) in
  let item_cvar = carg_of_garg env item_relindex in
  let accessor = case_cstrfield env sigma (EConstr.of_constr item_type) 1 (Projection.arg pr) in
  str accessor ++ str "(" ++ str item_cvar ++ str ")"

let gen_parallel_assignment (assignments : ((*lhs*)string * (*rhs*)string * (*type*)string) array) : Pp.t =
  let assign = Array.to_list assignments in
  let assign = List.filter (fun (lhs, rhs, ty) -> lhs <> rhs) assign in
  let rpp = ref (mt ()) in
  (* better algorithm using topological sort? *)
  let rec loop assign =
    match assign with
    | [] -> ()
    | a :: rest ->
        let rhs_list = List.map (fun (lhs, rhs, ty) -> rhs) assign in
        let blocked_assign, nonblocked_assign =
          List.partition (fun (lhs, rhs, ty) -> List.mem lhs rhs_list) assign
        in
        if nonblocked_assign <> [] then
          (List.iter
            (fun (lhs, rhs, ty) ->
              let pp = genc_assign (str lhs) (str rhs) in
              rpp := !rpp +++ pp)
            nonblocked_assign;
          loop blocked_assign)
        else
          (let (a_lhs, a_rhs, a_ty) = a in
          let tmp = local_gensym () in
          add_local_var a_ty tmp;
          let pp = genc_assign (str tmp) (str a_lhs) in
          (rpp := !rpp +++ pp);
          let assign2 = List.map
            (fun (lhs, rhs, ty) ->
              if rhs = a_lhs then (lhs, tmp, ty) else (lhs, rhs, ty))
            assign
          in
          loop assign2)
  in
  loop assign;
  !rpp

type assign_cont = {
  assign_cont_ret_var: string;
  assign_cont_exit_label: string option;
}

let gen_assign_cont (cont : assign_cont) (rhs : Pp.t) : Pp.t =
  genc_assign (Pp.str cont.assign_cont_ret_var) rhs +++
  match cont.assign_cont_exit_label with
  | None -> mt ()
  | Some label -> Pp.hov 0 (Pp.str "goto" +++ Pp.str label ++ Pp.str ";")

let rec gen_assign (fixinfo : fixinfo_t) (used : Id.Set.t) (cont : assign_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  let pp = gen_assign1 fixinfo used cont env sigma term cargs in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_assign:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_assign1 (fixinfo : fixinfo_t) (used : Id.Set.t) (cont : assign_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _
  | Cast _ | CoFix _ ->
      user_err (str "[codegen:gen_assign] unsupported term (" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_assign_cont cont (Pp.str str)
      else
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        (match Hashtbl.find_opt fixinfo (id_of_name name) with
        | Some info ->
            let fname =
              match info.fixfunc_top_call with
              | Some top_func_name -> top_func_name
              | None -> info.fixfunc_c_name
            in
            if info.fixfunc_inlinable then
              let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) info.fixfunc_formal_arguments cargs in
              let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
              let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str ("entry_" ^ info.fixfunc_c_name) ++ Pp.str ";") in
              pp_assignments +++ pp_goto_entry
            else
              gen_assign_cont cont
                (gen_funcall fname
                  (Array.append
                    (Array.of_list (List.map fst info.fixfunc_outer_variables))
                    (Array.of_list cargs)))
        | None ->
          user_err (Pp.str "[codegen:gen_assign] fix/closure call not supported yet"))
  | Const (ctnt,_) ->
      gen_assign_cont cont (gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list cargs))
  | Construct (cstr,_) ->
      gen_assign_cont cont (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list cargs))
  | App (f,args) ->
      let cargs2 =
        List.append
          (Array.to_list (Array.map (fun arg -> carg_of_garg env (destRel sigma arg)) args))
          cargs
      in
      gen_assign fixinfo used cont env sigma f cargs2
  | Case (ci,predicate,item,branches) ->
      let gen_switch =
        match cont.assign_cont_exit_label with
        | None -> gen_switch_with_break
        | Some _ -> gen_switch_without_break
      in
      gen_match used gen_switch (gen_assign fixinfo used cont) env sigma ci predicate item branches cargs
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (str "[codegen:gen_assign] projection cannot return a function, yet: " ++ Printer.pr_econstr_env env sigma term));
      gen_assign_cont cont (gen_proj env sigma pr item))
  | LetIn (x,e,t,b) ->
      let c_var = str_of_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      let cont1 = { assign_cont_ret_var = c_var;
                    assign_cont_exit_label = None; } in
      gen_assign fixinfo used cont1 env sigma e [] +++
      gen_assign fixinfo used cont env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let ui = Hashtbl.find fixinfo (id_of_annotated_name nary.(i)) in
      let ni_formal_arguments = ui.fixfunc_formal_arguments in
      if List.length cargs < List.length ni_formal_arguments then
        user_err (Pp.str "[codegen] gen_assign: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let ni_funcname = ui.fixfunc_c_name in
      if not ui.fixfunc_inlinable then
        gen_assign_cont cont
          (gen_funcall ni_funcname
            (Array.append
              (Array.of_list (List.map fst ui.fixfunc_outer_variables))
              (Array.of_list cargs)))
      else
        let env2 = EConstr.push_rec_types prec env in
        let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) ni_formal_arguments cargs in
        let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
        let exit_label = "exit_" ^ ni_funcname in
        let pp_exit = Pp.hov 0 (Pp.str exit_label ++ Pp.str ":") in
        let pp_bodies =
          Array.mapi
            (fun j nj ->
              let fj = fary.(j) in
              let uj = Hashtbl.find fixinfo (id_of_annotated_name nj) in
              let nj_formal_arguments = uj.fixfunc_formal_arguments in
              List.iter
                (fun (c_arg, t) -> add_local_var t c_arg)
                nj_formal_arguments;
              let nj_formal_argvars = List.map fst nj_formal_arguments in
              let nj_funcname = uj.fixfunc_c_name in
              let pp_label =
                if uj.fixfunc_used_as_goto ||
                   (uj.fixfunc_used_as_call && uj.fixfunc_top_call = None) then
                  Pp.str ("entry_" ^ nj_funcname)  ++ Pp.str ":"
                else
                  Pp.mt ()
              in
              let cont2 = { assign_cont_ret_var = cont.assign_cont_ret_var ;
                            assign_cont_exit_label = Some exit_label; } in
              pp_label +++ gen_assign fixinfo used cont2 env2 sigma fj nj_formal_argvars)
            nary in
        let reordered_pp_bodies = Array.copy pp_bodies in
        Array.blit pp_bodies 0 reordered_pp_bodies 1 i;
        reordered_pp_bodies.(0) <- pp_bodies.(i);
        pp_assignments +++ pp_join_ary (Pp.spc ()) reordered_pp_bodies +++ pp_exit

  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "[codegen] gen_assign: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_assign] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_assign fixinfo used cont env2 sigma b rest)

let rec gen_tail (fixinfo : fixinfo_t) (used : Id.Set.t) (gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  (*Feedback.msg_debug (Pp.str "[codegen] gen_tail start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "(" ++
    pp_join_list (Pp.spc ()) (List.map Pp.str cargs) ++
    Pp.str ")");*)
  let pp = gen_tail1 fixinfo used gen_ret env sigma term cargs in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_tail return:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_tail1 (fixinfo : fixinfo_t) (used : Id.Set.t) (gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _
  | Cast _ | CoFix _ ->
      user_err (str "[codegen:gen_tail] unsupported term (" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_ret (Pp.str str)
      else
        let key = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
        let uopt = Hashtbl.find_opt fixinfo (id_of_name key) in
        (match uopt with
        | None -> user_err (Pp.str "[codegen] gen_tail doesn't support partial application to (non-fixpoint) Rel, yet:" +++ Printer.pr_econstr_env env sigma term)
        | Some u ->
            let formal_arguments = u.fixfunc_formal_arguments in
            if List.length cargs < List.length formal_arguments then
              user_err (Pp.str "[codegen] gen_tail: partial application for fix-bounded-variable (higher-order term not supported yet):" +++
                Printer.pr_econstr_env env sigma term);
            let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) formal_arguments cargs in
            let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
            let funcname = u.fixfunc_c_name in
            let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str ("entry_" ^ funcname) ++ Pp.str ";") in
            pp_assignments +++ pp_goto_entry)
  | Const (ctnt,_) ->
      gen_ret (gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list cargs))
  | Construct (cstr,_) ->
      gen_ret (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list cargs))
  | App (f,args) ->
      let cargs2 =
        List.append
          (Array.to_list (Array.map (fun arg -> carg_of_garg env (destRel sigma arg)) args))
          cargs
      in
      gen_tail fixinfo used gen_ret env sigma f cargs2
  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "[codegen] gen_tail: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_tail] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_tail fixinfo used gen_ret env2 sigma b rest)
  | Case (ci,predicate,item,branches) ->
      gen_match used gen_switch_without_break (gen_tail fixinfo used gen_ret) env sigma ci predicate item branches cargs
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (str "[codegen:gen_assign] projection cannot return a function, yet: " ++ Printer.pr_econstr_env env sigma term));
      gen_ret (gen_proj env sigma pr item))
  | LetIn (x,e,t,b) ->
      let c_var = str_of_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      let cont1 = { assign_cont_ret_var = c_var;
                    assign_cont_exit_label = None; } in
      gen_assign fixinfo used cont1 env sigma e [] +++
      gen_tail fixinfo used gen_ret env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ui = Hashtbl.find fixinfo (id_of_annotated_name nary.(i)) in
      let ni_formal_arguments = ui.fixfunc_formal_arguments in
      if List.length cargs < List.length ni_formal_arguments then
        user_err (Pp.str "[codegen] gen_tail: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) ni_formal_arguments cargs in
      let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
      let pp_bodies =
        Array.mapi
          (fun j nj ->
            let fj = fary.(j) in
            let uj = Hashtbl.find fixinfo (id_of_annotated_name nj) in
            let nj_formal_arguments = uj.fixfunc_formal_arguments in
            List.iter
              (fun (c_arg, t) -> add_local_var t c_arg)
              nj_formal_arguments;
            let nj_formal_argvars = List.map fst nj_formal_arguments in
            let nj_funcname = uj.fixfunc_c_name in
            let pp_label =
              if uj.fixfunc_used_as_goto || uj.fixfunc_top_call = None then
                Pp.str ("entry_" ^ nj_funcname) ++ Pp.str ":"
              else
                Pp.mt () (* Not reached.  Currently, fix-term in top-call are decomposed by obtain_function_bodies and gen_tail is not used for it. *)
            in
            pp_label +++ gen_tail fixinfo used gen_ret env2 sigma fj nj_formal_argvars)
          nary in
      let reordered_pp_bodies = Array.copy pp_bodies in
      Array.blit pp_bodies 0 reordered_pp_bodies 1 i;
      reordered_pp_bodies.(0) <- pp_bodies.(i);
      pp_assignments +++ pp_join_ary (Pp.spc ()) reordered_pp_bodies

type top_fixterm_t = (*outer_variables*)((string * string) list) * Environ.env * EConstr.t

let rec detect_top_fixterms_rec (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t) (is_tail_position : bool) (term : EConstr.t) (numargs : int)
    (result : top_fixterm_t list)  : top_fixterm_t list =
  detect_top_fixterms_rec1 env sigma fixinfo is_tail_position term numargs result
and detect_top_fixterms_rec1 (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t) (is_tail_position : bool) (term : EConstr.t) (numargs : int)
    (result : top_fixterm_t list)  : top_fixterm_t list =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i -> result
  | Int _ | Float _ | Const _ | Construct _ -> result
  | Proj _ -> result
  | App (f, args) ->
      detect_top_fixterms_rec env sigma fixinfo is_tail_position f
        (Array.length args + numargs) result
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let result1 = detect_top_fixterms_rec env sigma fixinfo false e 0 result in
      detect_top_fixterms_rec env2 sigma fixinfo is_tail_position b numargs result1
  | Case (ci, p, item, branches) ->
      let acc = ref result in
      for i = 0 to Array.length branches - 1 do
        let br = branches.(i) in
        acc := detect_top_fixterms_rec env sigma fixinfo is_tail_position br (ci.Constr.ci_cstr_nargs.(i) + numargs) !acc
      done;
      !acc
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      if numargs = 0 then
        user_err (Pp.str "[codegen:detect_top_fixterms] closure not supported yet")
      else
        detect_top_fixterms_rec env2 sigma fixinfo is_tail_position b (numargs-1) result
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let n = Array.length nary in
      if is_tail_position then
        let acc = ref result in
        for j = 0 to n - 1 do
          let numargs2 = numargs_of_type env sigma tary.(j) in
          acc := detect_top_fixterms_rec env2 sigma fixinfo is_tail_position fary.(j) numargs2 !acc
        done;
        !acc
      else
        let id = id_of_annotated_name nary.(i) in
        let usage = Hashtbl.find fixinfo id in
        if usage.fixfunc_inlinable then
          let acc = ref result in
          for j = 0 to n - 1 do
            let numargs2 = numargs_of_type env sigma tary.(j) in
            acc := detect_top_fixterms_rec env2 sigma fixinfo is_tail_position fary.(j) numargs2 !acc
          done;
          !acc
        else
          (* top functions found. *)
          let acc = ref result in
          for j = 0 to n - 1 do
            let numargs2 = numargs_of_type env sigma tary.(j) in
            acc := detect_top_fixterms_rec env2 sigma fixinfo true fary.(j) numargs2 !acc
          done;
          (usage.fixfunc_outer_variables, env, term) :: !acc

let detect_top_fixterms (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t) (term : EConstr.t) :
    top_fixterm_t list =
  let numargs = numargs_of_exp env sigma term in
  detect_top_fixterms_rec env sigma fixinfo true term numargs []

let rec obtain_function_bodies_rec (env : Environ.env) (sigma : Evd.evar_map)
    (fargs : ((*varname*)string * (*vartype*)string) list) (fixfuncs : string list) (term : EConstr.t) :
    (((*varname*)string * (*vartype*)string) list * string list * Environ.env * EConstr.t) array =
  match EConstr.kind sigma term with
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let c_var = (str_of_annotated_name x, c_typename env sigma t) in
      obtain_function_bodies_rec env2 sigma (c_var :: fargs) fixfuncs b
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let bodies = Array.mapi
        (fun j nj ->
          let fixfunc_name = str_of_annotated_name nj in
          let fj = fary.(j) in
          if i = j then
            obtain_function_bodies_rec env2 sigma fargs (fixfunc_name :: fixfuncs) fj
          else
            obtain_function_bodies_rec env2 sigma fargs (fixfunc_name :: []) fj)
        nary
      in
      let reordered_bodies = Array.copy bodies in
      Array.blit bodies 0 reordered_bodies 1 i;
      reordered_bodies.(0) <- bodies.(i);
      array_flatten reordered_bodies
  | _ ->
      [|(fargs, fixfuncs, env, term)|]

let obtain_function_bodies (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t) (term : EConstr.t) :
    (((*varname*)string * (*vartype*)string) list *
     (*labels*)string list *
     Environ.env *
     EConstr.t) array =
  let gen_labels fixes =
    CList.map_filter
      (fun fix_name ->
        let fix_usage = Hashtbl.find fixinfo (Id.of_string fix_name) in
        if fix_usage.fixfunc_used_as_goto || fix_usage.fixfunc_top_call = None then
          Some ("entry_" ^ fix_usage.fixfunc_c_name)
        else
          None)
      fixes
  in
  let result_whole_body =
    Array.map
      (fun (args, fixes, env2, body) ->
        (args, gen_labels fixes, env2, body))
      (obtain_function_bodies_rec env sigma [] [] term)
  in
  let results_top_fixterms =
    List.map
      (fun (outer_variables, env1, fix) ->
        Array.map
          (fun (args, fixes, env2, body) ->
            (args, gen_labels fixes, env2, body))
        (obtain_function_bodies_rec env1 sigma outer_variables [] fix))
      (detect_top_fixterms env sigma fixinfo term)
  in
  Array.concat (result_whole_body :: results_top_fixterms)

let gen_func_single (cfunc_name : string) (env : Environ.env) (sigma : Evd.evar_map)
  (whole_body : EConstr.t) (return_type : string)
  (fixinfo : fixinfo_t) (used : Id.Set.t) : Pp.t =
  let bodies = obtain_function_bodies env sigma fixinfo whole_body in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_join_ary (spc ()) (Array.map
        (fun (args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          pp_join_list (spc ())
            (List.map (fun l -> Pp.str (l ^ ":")) labels) +++
          gen_tail fixinfo used gen_return env2 sigma body [])
        bodies))
  in
  let c_fargs =
    let (first_args, _, _, _) = bodies.(0) in
    List.rev first_args
  in
  let local_vars = List.filter
    (fun (c_type, c_var) ->
      match List.find_opt (fun (c_var1, ty1) -> c_var = c_var1) c_fargs with
      | Some _ -> false (* xxx: check type mismach *)
      | None -> true)
    local_vars
  in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_func_sub:6");*)
  v 0 (
  hov 0 (str "static" +++
        str return_type) +++
  str cfunc_name ++ str "(" ++
  hov 0 (gen_fargs c_fargs) ++
  str ")" +++
  vbrace (
    pp_postjoin_list (spc ())
      (List.map
        (fun (c_type, c_var) -> hov 0 (str c_type +++ str c_var ++ str ";"))
        local_vars)
    ++
    pp_body))

let gen_func_multi (cfunc_name : string) (env : Environ.env) (sigma : Evd.evar_map)
    (whole_body : EConstr.t) (formal_arguments : (string * string) list) (return_type : string)
    (fixinfo : fixinfo_t) (used : Id.Set.t) (called_fixfuncs : fixfunc_info list) : Pp.t =
  let func_index_type = "codegen_func_indextype_" ^ cfunc_name in
  let func_index_prefix = "codegen_func_index_" in
  let pp_enum =
    hov 0 (
      Pp.str "enum" +++
      Pp.str func_index_type +++
      hovbrace (
        pp_join_list (Pp.str "," ++ Pp.spc ())
          (Pp.str (func_index_prefix ^ cfunc_name) ::
           List.map
             (fun info -> Pp.str (func_index_prefix ^ info.fixfunc_c_name))
             called_fixfuncs)) ++
      Pp.str ";")
  in
  let pp_struct_args =
    let pr_fields args =
      pp_sjoin_list
        (List.map
          (fun (c_arg, t) ->
            hov 0 (Pp.str t +++ Pp.str c_arg ++ Pp.str ";"))
          args)
    in
    pp_sjoin_list
      (List.map
        (fun info ->
          hv 0 (
          Pp.str ("struct codegen_args_" ^ info.fixfunc_c_name) +++
          hovbrace (
          pr_fields info.fixfunc_outer_variables +++
          pr_fields info.fixfunc_formal_arguments +++
          (if CList.is_empty info.fixfunc_outer_variables &&
              CList.is_empty info.fixfunc_formal_arguments then
            (* empty struct is undefined behavior *)
            Pp.str "int" +++ Pp.str "dummy;" (* Not reached because info.fixfunc_formal_arguments cannot be empty. *)
          else
            mt ())) ++ Pp.str ";"))
      called_fixfuncs) +++
    hv 0 (
    Pp.str ("struct codegen_args_" ^ cfunc_name) +++
    hovbrace (
    pr_fields formal_arguments +++
    (if CList.is_empty formal_arguments then
      (* empty struct is undefined behavior *)
      Pp.str "int" +++ Pp.str "dummy;" (* Not reached because info.fixfunc_formal_arguments cannot be empty. *)
    else
      mt ())) ++ Pp.str ";")
  in
  let pp_forward_decl =
    hv 0 (
      Pp.str "static void" +++
      Pp.str ("codegen_functions_" ^ cfunc_name) ++
      Pp.str ("(enum " ^ func_index_type ^ " g, void *args, void *ret);"))
  in
  let pp_entry_functions =
    let pr_entry_function c_name func_index formal_arguments return_type =
      let pp_return_type =
        Pp.str "static" +++
        Pp.str return_type
      in
      let pp_parameters =
        Pp.str "(" ++
        (pp_join_list (Pp.str "," ++ Pp.spc ())
          (List.map
            (fun (c_arg, t) ->
              hov 0 (Pp.str t +++ Pp.str c_arg))
            formal_arguments)) ++
        Pp.str ")"
      in
      let pp_vardecl_args =
        Pp.str ("struct codegen_args_" ^ c_name) +++
        Pp.str "args" +++
        Pp.str "=" +++
        hovbrace (
          (pp_join_list (Pp.str "," ++ Pp.spc ())
            (List.map
              (fun (c_arg, t) -> Pp.str c_arg)
            formal_arguments))) ++
        Pp.str ";"
      in
      let pp_vardecl_ret =
        Pp.str return_type +++
        Pp.str "ret;"
      in
      let pp_call =
        Pp.str ("codegen_functions_" ^ cfunc_name) ++
        Pp.str "(" ++
        Pp.str func_index ++ Pp.str "," +++
        Pp.str "&args," +++
        Pp.str "&ret);"
      in
      let pp_return =
        Pp.str "return ret;"
      in
      v 0 (
        hov 0 pp_return_type +++
        Pp.str c_name ++
        hov 0 (pp_parameters) +++
        vbrace (
          hov 0 (pp_vardecl_args) +++
          hov 0 (pp_vardecl_ret) +++
          hov 0 pp_call +++
          hov 0 pp_return))
    in
    pp_sjoin_list
      (List.map
        (fun info ->
          pr_entry_function info.fixfunc_c_name (func_index_prefix ^ info.fixfunc_c_name)
            (List.append
              info.fixfunc_outer_variables
              info.fixfunc_formal_arguments)
            info.fixfunc_return_type)
        called_fixfuncs) +++
    pr_entry_function cfunc_name (func_index_prefix ^ cfunc_name)
      formal_arguments return_type
  in
  let bodies = obtain_function_bodies env sigma fixinfo whole_body in
  let gen_ret = (gen_void_return ("(*(" ^ return_type ^ " *)ret)")) in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_join_ary (spc ()) (Array.map
        (fun (args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          v 0 (
            pp_join_list (spc ())
              (List.map (fun l -> Pp.str (l ^ ":")) labels) +++
            gen_tail fixinfo used gen_ret env2 sigma body []))
        bodies))
  in
  let pp_local_variables_decls =
    pp_join_list (spc ())
      (List.map
        (fun (c_type, c_var) -> hov 0 (str c_type +++ str c_var ++ str ";"))
        local_vars)
  in
  let pp_switch_cases =
    pp_sjoin_list
      (List.map
        (fun info ->
          let pp_case =
            Pp.str "case" +++ Pp.str (func_index_prefix ^ info.fixfunc_c_name) ++ Pp.str ":"
          in
          let pp_assign_outer =
            pp_sjoin_list
              (List.map
                (fun (c_arg, t) ->
                  hov 0 (
                    Pp.str c_arg +++
                    Pp.str "=" +++
                    Pp.str ("((struct codegen_args_" ^ info.fixfunc_c_name ^ " *)args)->" ^ c_arg) ++
                    Pp.str ";"))
                info.fixfunc_outer_variables)
          in
          let pp_assign_args =
            pp_sjoin_list
              (List.map
                (fun (c_arg, t) ->
                  hov 0 (
                    Pp.str c_arg +++
                    Pp.str "=" +++
                    Pp.str ("((struct codegen_args_" ^ info.fixfunc_c_name ^ " *)args)->" ^ c_arg) ++
                    Pp.str ";"))
                info.fixfunc_formal_arguments)
          in
          let pp_goto =
            Pp.str "goto" +++ Pp.str ("entry_" ^ info.fixfunc_c_name) ++ Pp.str ";"
          in
          let pp_result =
            hov 0 pp_case ++ Pp.brk (1,2) ++
            v 0 (
              pp_assign_outer +++
              pp_assign_args +++
              hov 0 pp_goto)
          in
          pp_result)
        called_fixfuncs)
  in
  let pp_switch_default = Pp.str "case" +++ Pp.str (func_index_prefix ^ cfunc_name) ++ Pp.str ":" in
  let pp_assign_args_default =
    pp_sjoin_list
      (List.map
        (fun (c_arg, t) ->
          hov 0 (
            Pp.str c_arg +++
            Pp.str "=" +++
            Pp.str ("((struct codegen_args_" ^ cfunc_name ^ " *)args)->" ^ c_arg) ++
            Pp.str ";"))
        formal_arguments)
  in
  let pp_switch_body =
    pp_switch_cases +++
    hov 0 pp_switch_default ++ Pp.brk (1,2) ++
    v 0 pp_assign_args_default
  in
  let pp_switch =
    hov 0 (Pp.str "switch" +++ Pp.str "(g)") +++
    vbrace pp_switch_body
  in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_func_sub:6");*)
  v 0 (
    pp_enum +++
    pp_struct_args +++
    pp_forward_decl +++
    pp_entry_functions +++
    Pp.str "static void" +++
    Pp.str ("codegen_functions_" ^ cfunc_name) ++
    Pp.str ("(enum " ^ func_index_type ^ " g, void *args, void *ret)")) +++
    vbrace (
      pp_local_variables_decls +++
      pp_switch +++
      pp_body)

let rec used_variables (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Id.Set.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Const _ | Construct _ | Int _ | Float _ -> Id.Set.empty
  | Rel i ->
      let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
      Id.Set.singleton (id_of_name name)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      used_variables env2 sigma b
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      Array.fold_left
        (fun set f -> Id.Set.union set (used_variables env2 sigma f))
        Id.Set.empty
        fary
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      Id.Set.union
        (used_variables env sigma e)
        (used_variables env2 sigma b)
  | Case (ci, p, item, branches) ->
      Id.Set.union
        (used_variables env sigma item)
        (Array.fold_left
          (fun set br -> Id.Set.union set (used_variables env sigma br))
          Id.Set.empty
          branches)
  | App (f,args) ->
      Id.Set.union
        (used_variables env sigma f)
        (Array.fold_left
          (fun set arg -> Id.Set.union set (used_variables env sigma arg))
          Id.Set.empty
          args)
  | Proj (proj, e) -> used_variables env sigma e

let gen_func_sub (cfunc_name : string) : Pp.t =
  let (ctnt, ty, whole_body) = get_ctnt_type_body_from_cfunc cfunc_name in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  linear_type_check_term whole_body;
  let whole_body = EConstr.of_constr whole_body in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments, return_type) = c_args_and_ret_type env sigma whole_ty in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_func_sub:1");*)
  let fixinfo = collect_fix_info env sigma cfunc_name whole_body in
  (*Feedback.msg_debug (Pp.str "[codegen] gen_func_sub:2");*)
  let used = used_variables env sigma whole_body in
  let called_fixfuncs = compute_called_fixfuncs fixinfo in
  (if called_fixfuncs <> [] then
    gen_func_multi cfunc_name env sigma whole_body formal_arguments return_type fixinfo used called_fixfuncs
  else
    gen_func_single cfunc_name env sigma whole_body return_type fixinfo used) ++
  Pp.fnl ()

let gen_function (cfunc_name : string) : Pp.t =
  local_gensym_with (fun () -> gen_func_sub cfunc_name)

(* Vernacular commands *)

let command_gen (cfunc_list : string_or_qualid list) : unit =
  List.iter
    (fun cfunc_name ->
      match cfunc_name with
      | StrOrQid_Str str ->
          Feedback.msg_info (gen_function str)
      | StrOrQid_Qid qid ->
          let (env, sp_inst) = codegen_function_internal qid []
            { spi_cfunc_name = None;
              spi_partapp_id = None;
              spi_specialized_id = None }
          in
          Feedback.msg_info (gen_function sp_inst.sp_cfunc_name))
    cfunc_list

let command_snippet (str : string) : unit =
  let len = String.length str in
  let str' =
    if 0 < len && str.[len - 1] <> '\n' then
      str ^ "\n"
    else
      str
  in
  generation_list := GenSnippet str' :: !generation_list

let generate_ind_names (env : Environ.env) (sigma : Evd.evar_map) (coq_type : EConstr.types) :
    ((*ind*)inductive *
     (*args*)EConstr.t list *
     (*ind typename*)string *
     (*enum typename*)string *
     (*C switch function*)string *
     ((*cstr ID*)Id.t *
      (*cstr name*)string *
      (*cstr tag*)string *
      (*union field*)string *
      ((*field type*)string *
       (*field name*)string *
       (*accessor name*)string) list) list) =
  let global_prefix = global_gensym () in
  let (f, args) = decompose_app sigma coq_type in
  let (ind, _) = destInd sigma f in
  let (mutind, i) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  let ind_id = mutind_body.Declarations.mind_packets.(i).Declarations.mind_typename in
  let ind_typename = global_prefix ^ "_ind_" ^ Id.to_string ind_id in
  let enum_tag = global_prefix ^ "_enum_" ^ Id.to_string ind_id in
  let swfunc = global_prefix ^ "_sw_" ^ Id.to_string ind_id in
  let numcstr = Array.length oneind_body.Declarations.mind_consnames in
  let cstr_and_fields =
    List.init numcstr
      (fun j ->
        (*Feedback.msg_debug (Printer.pr_econstr_env env sigma coq_type);*)
        let cstrterm = mkApp ((mkConstruct (ind, (j+1))), CArray.rev_of_list args) in (* xxx: args should be parameters of inductive type *)
        (*Feedback.msg_debug (Printer.pr_econstr_env env sigma cstrterm);*)
        let cstrtype = Retyping.get_type_of env sigma cstrterm in
        let (args, result_type) = decompose_prod sigma cstrtype in
        let field_types = List.rev (List.map (fun (name, t) -> c_typename env sigma t) args) in
        let cstrid = oneind_body.Declarations.mind_consnames.(j) in
        let cstrname = global_prefix ^ "_cstr_" ^ (Id.to_string cstrid) in
        let cstrtag = global_prefix ^ "_tag_" ^ (Id.to_string cstrid) in
        let union_field = global_prefix ^ "_u_" ^ (Id.to_string cstrid) in
        let fields_and_accessors =
          List.mapi
            (fun k field_type ->
              let field_name = "field" ^ string_of_int (k+1) in
              let accessor = global_prefix ^ "_get_" ^ (Id.to_string cstrid) ^ "_" ^ field_name in
              (field_type, field_name, accessor))
            field_types
        in
        (cstrid, cstrname, cstrtag, union_field, fields_and_accessors))
  in
  (ind, args, ind_typename, enum_tag, swfunc, cstr_and_fields)

let command_indimp (user_coq_type : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_type env sigma user_coq_type in
  (if ind_coq_type_registered_p coq_type then
    user_err (Pp.str "[codegen] inductive type already configured:" +++ Printer.pr_constr_env env sigma coq_type));
  let coq_type = EConstr.of_constr coq_type in
  let (ind, args, ind_typename, enum_tag, swfunc, cstr_and_fields) = generate_ind_names env sigma coq_type in
  ignore (register_ind_type env sigma (EConstr.to_constr sigma coq_type) ind_typename);
  let cstr_caselabel_accessors_list =
    List.mapi
      (fun j (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) ->
        let caselabel = if j = 0 then "default" else "case " ^ cstrtag in
        let accessors = List.map (fun (field_type, field_name, accessor) -> accessor) fields_and_accessors in
        (cstrid, caselabel, accessors))
      cstr_and_fields
  in
  ignore (register_ind_match env sigma (EConstr.to_constr sigma coq_type) swfunc cstr_caselabel_accessors_list);
  let env =
    CList.fold_left_i
      (fun j env (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) ->
        let cstrterm0 = EConstr.to_constr sigma (mkConstruct (ind, (j+1))) in
        let args' = List.rev_map (EConstr.to_constr sigma) args in
        ignore (codegen_specialization_define_or_check_arguments env sigma cstrterm0 (List.init (List.length args) (fun _ -> SorD_S)));
        let (env, sp_inst) = specialization_instance_internal env sigma cstrterm0 args' (Some { spi_cfunc_name = Some cstrname; spi_partapp_id = None; spi_specialized_id = None }) in
        env)
      0 env cstr_and_fields
  in
  ignore env;
  let no_field =
    List.for_all
      (fun (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) ->
        fields_and_accessors = [])
      cstr_and_fields
  in
  let singlecstr = List.length cstr_and_fields = 1 in
  let pp_enum =
    if singlecstr then
      Pp.mt ()
    else
      Pp.hov 0 (
        (Pp.str "enum" +++ Pp.str enum_tag +++
        hovbrace (pp_join_list
          (Pp.str "," ++ Pp.spc ())
          (List.map (fun (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) -> Pp.str cstrtag)
            cstr_and_fields)) ++ Pp.str ";"))
  in
  let field_decls =
    List.map
      (fun (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) ->
        pp_sjoin_list
          (List.map
            (fun (field_type, field_name, accessor) ->
              Pp.hov 0 (Pp.str field_type +++ Pp.str field_name ++ Pp.str ";"))
            fields_and_accessors))
      cstr_and_fields
  in
  let cstr_and_fields_with_decls =
    List.map2
      (fun (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) field_def ->
        (cstrid, cstrname, cstrtag, union_field, fields_and_accessors, field_def))
      cstr_and_fields field_decls
  in
  let pp_typedef =
    Pp.v 0 (
      Pp.str "typedef struct" +++
      vbrace (
        (if singlecstr then
          Pp.mt ()
        else
          Pp.hov 0 (Pp.str "enum" +++ Pp.str enum_tag +++ Pp.str "tag;")) +++
        (if no_field then
          Pp.mt ()
        else if singlecstr then
          Pp.v 0
            (let (cstrid, cstrname, cstrtag, union_field, fields_and_accessors, field_decl) = List.hd cstr_and_fields_with_decls in
            field_decl)
        else
          Pp.v 0 (Pp.str "union" +++
                  vbrace (
                    pp_sjoin_list
                      (List.filter_map
                        (fun (cstrid, cstrname, cstrtag, union_field, fields_and_accessors, field_decl) ->
                          if fields_and_accessors = [] then
                            None
                          else
                            Some (
                              Pp.str "struct" +++
                              vbrace field_decl ++
                              Pp.str (" " ^ union_field ^ ";")))
                        cstr_and_fields_with_decls)) ++
                  Pp.str " as;"))
      ) ++ Pp.str (" " ^ ind_typename ^ ";"))
  in
  let pp_swfunc =
    Pp.h 0 (
      Pp.str "#define" +++
      Pp.str swfunc ++ Pp.str "(x)" +++
      (if singlecstr then
        Pp.str "0"
      else
        Pp.str "((x).tag)"))
  in
  let pp_accessors =
    pp_sjoin_list
      (List.map
        (fun (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) ->
          pp_sjoin_list
            (List.map
              (fun (field_type, field_name, accessor) ->
                Pp.h 0 (Pp.str "#define" +++
                        Pp.str accessor ++
                        Pp.str "(x)" +++
                        (if singlecstr then
                          Pp.str ("((x)." ^ field_name ^ ")")
                        else
                          Pp.str ("((x).as." ^ union_field ^ "." ^ field_name ^ ")"))))
              fields_and_accessors))
        cstr_and_fields)
  in
  let pp_cstr =
    pp_sjoin_list
      (List.map
        (fun (cstrid, cstrname, cstrtag, union_field, fields_and_accessors) ->
          let args =
            pp_join_list (Pp.str "," ++ Pp.spc ())
              (List.map
                (fun (field_type, field_name, accessor) -> Pp.str field_name)
                fields_and_accessors)
          in
          Pp.h 0 (Pp.str "#define" +++
                    Pp.str cstrname ++
                    Pp.str "(" ++ args ++ Pp.str ")" +++
                    Pp.str "(" ++
                    Pp.str ("(" ^ ind_typename ^ ")") ++
                    (if singlecstr then
                      hbrace args
                    else
                      hbrace (
                        let union_init =
                          Pp.str ("." ^ union_field) +++
                          Pp.str "=" +++
                          hbrace args
                        in
                        if List.length fields_and_accessors = 0 then
                          Pp.str cstrtag
                        else
                          (Pp.str cstrtag ++ Pp.str "," +++ hbrace union_init))) ++
                    Pp.str ")"))
        cstr_and_fields)
  in
  ignore pp_enum;
  ignore pp_typedef;
  ignore pp_accessors;
  let pp =
    Pp.v 0 (
      pp_enum +++
      pp_typedef +++
      pp_swfunc +++
      pp_accessors +++
      pp_cstr +++
      Pp.mt ()
    )
  in
  (*Feedback.msg_debug (Pp.str (Pp.db_string_of_pp pp));*)
  let str = Pp.string_of_ppcmds pp in
  generation_list := GenSnippet str :: !generation_list;
  (*Feedback.msg_info pp;*)
  ()

let gen_file (fn : string) (gen_list : code_generation list) : unit =
  (* open in the standard permission, 0o666, which will be masked by umask. *)
  (let (temp_fn, ch) = Filename.open_temp_file
    ~perms:0o666 ~temp_dir:(Filename.dirname fn) (Filename.basename fn) ".c" in
  let fmt = Format.formatter_of_out_channel ch in
  List.iter
    (fun gen ->
      match gen with
      | GenFunc cfunc_name ->
          Pp.pp_with fmt (gen_function cfunc_name ++ Pp.fnl ())
      | GenSnippet str ->
          let terminator =
            if str = "" then
              Pp.mt ()
            else if str.[String.length str - 1] = '\n' then
              Pp.mt ()
            else
              Pp.fnl ()
          in
          Pp.pp_with fmt (Pp.str str ++ terminator ++ Pp.fnl ()))
    gen_list;
  Format.pp_print_flush fmt ();
  close_out ch;
  Sys.rename temp_fn fn;
  Feedback.msg_info (str ("[codegen] file generated: " ^ fn)))

let command_generate_file (fn : string) =
  gen_file fn (List.rev !generation_list);
  generation_list := []
