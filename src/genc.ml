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
open Constr
open EConstr

open Cgenutil
open State
open Induc
open Specialize

let abort (x : 'a) : 'a = assert false

let generate_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let printed_type = mangle_term env sigma t in
  let c_name = c_id (squeeze_white_spaces printed_type) in
  let ind_cfg = register_ind_type env sigma (EConstr.to_constr sigma t) c_name in
  Feedback.msg_info (v 2
    (Pp.str "[codegen] inductive type translation automatically configured:" +++
     (hv 2 (Pp.str "CodeGen Inductive Type" +++ Printer.pr_econstr_env env sigma t +++
     Pp.str "=>" +++ Pp.str (escape_as_coq_string c_name) ++ Pp.str "."))));
  ind_cfg

let generate_ind_match (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  let (mutind, mutind_body, i, oneind_body, args) = get_ind_coq_type env (EConstr.to_constr sigma t) in
  let printed_type = mangle_term env sigma t in
  let swfunc = "sw_" ^ c_id (squeeze_white_spaces printed_type) in
  let numcons = Array.length oneind_body.Declarations.mind_consnames in
  let cstr_caselabel_accessors_list =
    List.init numcons
      (fun j0 ->
        let j = j0 + 1 in
        let consname = oneind_body.Declarations.mind_consnames.(j0) in
        let cstr = mkConstruct ((mutind, i), j) in
        let args = CArray.map_of_list EConstr.of_constr args in
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
  Feedback.msg_info (v 2
    (Pp.str "[codegen] match-expression translation automatically configured:" +++
     hv 0 (pr_inductive_match env sigma ind_cfg)));
  ind_cfg

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

let case_cstrmember (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) (k : int) : string =
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

let genc_assign (lhs : Pp.t) (rhs : Pp.t) : Pp.t =
  Pp.hov 0 (lhs +++ str "=" +++ rhs ++ str ";")

let gen_return (arg : Pp.t) : Pp.t =
  hov 0 (str "return" +++ arg ++ str ";")

let gen_void_return (retvar : string) (arg : Pp.t) : Pp.t =
  genc_assign (str retvar) arg +++ str "return;"

let gen_funcall (c_fname : string) (argvars : string array) : Pp.t =
  str c_fname ++ str "(" ++
  pp_join_ary (str "," ++ spc ()) (Array.map Pp.str argvars) ++
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
  let gen_constant = Array.length argvars = 0 && sp_inst.sp_icommand = CodeGenConstant in
  if gen_constant then
    str c_fname
  else
    gen_funcall c_fname argvars

let is_static_function_icommand (icommand : instance_command) : bool =
  match icommand with
  | CodeGenFunction -> false
  | CodeGenStaticFunction -> true
  | CodeGenPrimitive -> user_err (Pp.str "[codegen] unexpected CodeGenPrimitive")
  | CodeGenConstant -> user_err (Pp.str "[codegen] unexpected CodeGenConstant")

let get_ctnt_type_body_from_cfunc (cfunc_name : string) :
    bool * Constant.t * Constr.types * Constr.t =
  let (sp_cfg, sp_inst) =
    match CString.Map.find_opt cfunc_name !cfunc_instance_map with
    | None ->
        user_err (Pp.str "[codegen] C function name not found:" +++
                  Pp.str cfunc_name)
    | Some (sp_cfg, sp_inst) -> (sp_cfg, sp_inst)
  in
  let static = is_static_function_icommand sp_inst.sp_icommand in
  let (env, ctnt) =
    match sp_inst.sp_simplified_status with
    | SpNoSimplification -> user_err (Pp.str "[codegen] not a target of code generation:" +++ Pp.str cfunc_name)
    | SpExpectedId id ->
        let (env, declared_ctnt, referred_cfuncs) = codegen_simplify cfunc_name in (* modify global env *)
        (env, declared_ctnt)
    | SpDefined (ctnt, _) -> (Global.env (), ctnt)
  in
  (*msg_debug_hov (Pp.str "[codegen:get_ctnt_type_body_from_cfunc] ctnt=" ++ Printer.pr_constant env ctnt);*)
  let cdef = Environ.lookup_constant ctnt env in
  let ty = cdef.Declarations.const_type in
  match Global.body_of_constant_body Library.indirect_accessor cdef with
  | None -> user_err (Pp.str "[codegen] couldn't obtain the body:" +++
                      Printer.pr_constant env ctnt)
  | Some (body,_, _) -> (static, ctnt, ty, body)

let hbrace (pp : Pp.t) : Pp.t =
  h (str "{" +++ pp ++ brk (1,-2) ++ str "}")

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

type fixterm_info = {
  fixterm_term_id: Id.t;
  fixterm_func_ids: Id.t array;
  fixterm_tail_position: bool;
  fixterm_numargs: int;
  fixterm_term_env: Environ.env;
  fixterm_term: EConstr.t;
  fixterm_inlinable: bool;
  fixterm_outer_variables: (string * string) list; (* [(varname1, vartype1); ...] *) (* by set_fixfuncinfo_outer_variables *)
}

type fixfunc_info = {
  fixfunc_func_id: Id.t;
  fixfunc_func_index: int;
  fixfunc_term_env: Environ.env;
  fixfunc_func_env: Environ.env;
  fixfunc_func: EConstr.t;
  fixfunc_inlinable: bool;
  fixfunc_used_as_call: bool;
  fixfunc_used_as_goto: bool;
  fixfunc_formal_arguments: (string * string) list; (* [(varname1, vartype1); ...] *)
  fixfunc_return_type: string;
  fixfunc_top_call: string option; (* by detect_top_calls *)
  fixfunc_c_name: string; (* by determine_fixfunc_c_names *)
  fixfunc_outer_variables: (string * string) list; (* [(varname1, vartype1); ...] *) (* by set_fixfuncinfo_outer_variables *)
}

type fixfuncinfo_t = (Id.t, fixfunc_info) Hashtbl.t

let show_fixfuncinfo (env : Environ.env) (sigma : Evd.evar_map) (fixfuncinfo : fixfuncinfo_t) : unit =
  Hashtbl.iter
    (fun fixfunc info ->
      msg_debug_hov (Pp.str (Id.to_string fixfunc) ++ Pp.str ":" +++
        Pp.str "inlinable=" ++ Pp.bool info.fixfunc_inlinable +++
        Pp.str "used_as_call=" ++ Pp.bool info.fixfunc_used_as_call +++
        Pp.str "used_as_goto=" ++ Pp.bool info.fixfunc_used_as_goto +++
        Pp.str "formal_arguments=(" ++ pp_joinmap_list (Pp.str ",") (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str ty) info.fixfunc_formal_arguments ++ Pp.str ")" +++
        Pp.str "return_type=" ++ Pp.str info.fixfunc_return_type +++
        Pp.str "top_call=" ++ (match info.fixfunc_top_call with None -> Pp.str "None" | Some top -> Pp.str ("Some " ^ top)) +++
        Pp.str "c_name=" ++ Pp.str info.fixfunc_c_name +++
        Pp.str "outer_variables=(" ++ pp_joinmap_list (Pp.str ",") (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str ty) info.fixfunc_outer_variables ++ Pp.str ")" +++
        mt ()
      ))
    fixfuncinfo

let rec c_args_and_ret_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((string * string) list) * string =
  match EConstr.kind sigma term with
  | Prod (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let (rest_args, ret_type) = c_args_and_ret_type env2 sigma b in
      (((str_of_annotated_name x, c_typename env sigma t) :: rest_args), ret_type)
  | _ ->
      ([], c_typename env sigma term)

let disjoint_id_map_union (m1 : 'a Id.Map.t) (m2 : 'a Id.Map.t) =
  Id.Map.union
    (fun id b1 b2 -> user_err (Pp.str "[codegen:bug] unexpected duplicated variable name:" +++ Id.print id))
    m1 m2

(*
  detect_inlinable_fixterm_rec implements (R,N,T) = RNT[term]_numargs in doc/codegen.tex.
  R is a map from fix-bounded IDs to bool.
  R[n] = true if n is fix-bounded function which is inlinable (only used for goto so do not need to be a real function).
  R[n] = false if n is fix-bounded function not inlinable.
  R can also be usable to determine an ID is fix-bounded function or not.
*)
let rec detect_inlinable_fixterm_rec (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (numargs : int) :
    (* fixterms inlinable or not *) bool Id.Map.t *
    (* variables at non-tail position *) IntSet.t *
    (* variables at tail position *) IntSet.t =
  (*msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_rec] start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs);*)
  let result = detect_inlinable_fixterm_rec1 env sigma term numargs in
  (*let (argmap, nontailset, tailset, argset) = result in
  msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_rec] end:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs
    +++
    Pp.str "tailset={" ++
    pp_joinmap_list (Pp.str ",")
      (fun i ->
        let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
        Pp.int i ++ Pp.str "=" ++ Name.print name
        )
      (IntSet.elements tailset) ++
    Pp.str "}"
    +++
    Pp.str "nontailset={" ++
    pp_joinmap_list (Pp.str ",")
      (fun i ->
        let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
        Pp.int i ++ Pp.str "=" ++ Name.print name)
      (IntSet.elements nontailset) ++
    Pp.str "}" +++
    Pp.str "inlinable-fixterms={" ++
    xxx
    Pp.str "}");
    *)
  result
and detect_inlinable_fixterm_rec1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (numargs : int) :
    (* fixterms inlinable or not *) bool Id.Map.t *
    (* variables at non-tail position *) IntSet.t *
    (* variables at tail position *) IntSet.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Array _ -> user_err (Pp.str "[codegen] Array is not supported for code generation")
  | Rel i -> (Id.Map.empty, IntSet.empty, IntSet.singleton i)
  | Int _ | Float _ | Const _ | Construct _ -> (Id.Map.empty, IntSet.empty, IntSet.empty)
  | Proj (proj, e) ->
      (* e must be a Rel which type is inductive (non-function) type *)
      (Id.Map.empty, IntSet.empty, IntSet.empty)
  | App (f, args) ->
      let (inlinable_f, nontailset_f, tailset_f) = detect_inlinable_fixterm_rec env sigma f (Array.length args + numargs) in
      let nontailset = Array.fold_left (fun set arg -> IntSet.add (destRel sigma arg) set) nontailset_f args in
      (inlinable_f, nontailset, tailset_f)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let (inlinable_e, nontailset_e, tailset_e) = detect_inlinable_fixterm_rec env sigma e 0 in
      let (inlinable_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_rec env2 sigma b numargs in
      let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
      let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
      let nontailset = IntSet.union
        (IntSet.union tailset_e nontailset_e)
        nontailset_b
      in
      let inlinable = disjoint_id_map_union inlinable_e inlinable_b in
      (inlinable, nontailset, tailset_b)
  | Case (ci, p, iv, item, branches) ->
      (* item must be a Rel which type is inductive (non-function) type *)
      let branches_result = Array.map2
        (fun cstr_nargs br -> detect_inlinable_fixterm_rec env sigma br
          (cstr_nargs + numargs))
        ci.Constr.ci_cstr_nargs branches
      in
      let tailset =
        Array.fold_left
          (fun set (inlinable_br, nontailset_br, tailset_br) ->
            IntSet.union set tailset_br)
          IntSet.empty
          branches_result
      in
      let nontailset =
        Array.fold_left
          (fun set (inlinable_br, nontailset_br, tailset_br) ->
            IntSet.union set nontailset_br)
          IntSet.empty branches_result
      in
      let inlinable =
        Array.fold_left
          (fun m (inlinable_br, nontailset_br, tailset_br) ->
            disjoint_id_map_union m inlinable_br)
          Id.Map.empty branches_result
      in
      (inlinable, nontailset, tailset)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      if numargs = 0 then
        (* closure creation *)
        let (inlinable_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_rec env2 sigma b (numargs_of_exp env sigma term) in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        let nontailset = IntSet.union tailset_b nontailset_b in
        (inlinable_b, nontailset, IntSet.empty)
      else
        let (inlinable_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_rec env2 sigma b (numargs-1) in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        (inlinable_b, nontailset_b, tailset_b)
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let h = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let fixfuncs_result = Array.map2
        (fun t f -> detect_inlinable_fixterm_rec env2 sigma f
          (numargs_of_type env sigma t))
        tary fary
      in
      let tailset_fs =
        Array.fold_left
          (fun set (inlinable_f, nontailset_f, tailset_f) ->
            IntSet.union set tailset_f)
          IntSet.empty fixfuncs_result
      in
      let nontailset_fs =
        Array.fold_left
          (fun set (inlinable_f, nontailset_f, tailset_f) ->
            IntSet.union set nontailset_f)
          IntSet.empty fixfuncs_result
      in
      let inlinable_fs =
        Array.fold_left
          (fun m (inlineable_f, nontailset_f, tailset_f) ->
            disjoint_id_map_union m inlineable_f)
          Id.Map.empty fixfuncs_result
      in
      let inlinable_fixterm = not (IntSet.exists ((>=) h) nontailset_fs) in
      let tailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) tailset_fs) in
      let nontailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) nontailset_fs) in
      if numargs < numargs_of_type env sigma tary.(i) || (* closure creation *)
         not inlinable_fixterm then
        (* At least one fix-bounded function is used at
          non-tail position or argument position.
          Assuming fix-bounded functions are strongly-connected,
          there is no tail position in this fix term. *)
        let nontailset = IntSet.union tailset_fs' nontailset_fs' in
        let inlinable_fs' =
          Array.fold_left
            (fun fs name -> Id.Map.add (id_of_annotated_name name) false fs)
            inlinable_fs
            nary
        in
        (inlinable_fs', nontailset, IntSet.empty)
      else
        let inlinable_fs' =
          Array.fold_left
            (fun fs name -> Id.Map.add (id_of_annotated_name name) true fs)
            inlinable_fs
            nary
        in
        (inlinable_fs', nontailset_fs', tailset_fs')

(*
  detect_inlinable_fixterm implementes TR[term]_numargs in doc/codegen.tex.
*)
let detect_inlinable_fixterm (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (numargs : int) : bool Id.Map.t =
  let (inlinable, nontailset, tailset) = detect_inlinable_fixterm_rec env sigma term numargs in
  inlinable

(*
  collect_fix_usage collects information for each fix-bounded functions.
  The result is stored in fixfuncinfo as side effect.

  collect_fix_usage tracks the term will be translated by gen_assign or gen_tail.
  tail_position=false means that term will be translated by gen_assign.
  tail_position=true means that term will be translated by gen_tail.
*)

let rec collect_fix_usage_rec
    ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (tail_position : bool) (term : EConstr.t) (numargs : int)
    ~(used_as_call : bool ref list)
    ~(used_as_goto : bool ref list) :
    fixterm_info Seq.t * fixfunc_info Seq.t =
  let result = collect_fix_usage_rec1 ~inlinable_fixterms env sigma tail_position term numargs ~used_as_call ~used_as_goto in
  result
and collect_fix_usage_rec1 ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (tail_position : bool) (term : EConstr.t) (numargs : int)
    ~(used_as_call : bool ref list)
    ~(used_as_goto : bool ref list) :
    fixterm_info Seq.t * fixfunc_info Seq.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Array _ -> user_err (Pp.str "[codegen] Array is not supported for code generation")
  | Rel i ->
      ((if 0 < numargs then
        let id = id_of_name (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)) in
        match Id.Map.find_opt id inlinable_fixterms with
        | None -> () (* term is not fix-bounded function *)
        | Some inlinable ->
            if tail_position then
              List.nth used_as_goto (i-1) := true
            else
              if inlinable then
                List.nth used_as_goto (i-1) := true
              else
                List.nth used_as_call (i-1) := true);
      (Seq.empty, Seq.empty))
  | Int _ | Float _ | Const _ | Construct _ -> (Seq.empty, Seq.empty)
  | Proj (proj, e) ->
      (* e must be a Rel which type is inductive (non-function) type *)
      (Seq.empty, Seq.empty)
  | App (f, args) ->
      collect_fix_usage_rec ~inlinable_fixterms env sigma tail_position f (Array.length args + numargs) ~used_as_call ~used_as_goto
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let used_as_call2 = ref false :: used_as_call in
      let used_as_goto2 = ref false :: used_as_goto in
      let (fixterms1, fixfuncs1) = collect_fix_usage_rec ~inlinable_fixterms env sigma false e 0 ~used_as_call ~used_as_goto in
      let (fixterms2, fixfuncs2) = collect_fix_usage_rec ~inlinable_fixterms env2 sigma tail_position b numargs ~used_as_call:used_as_call2 ~used_as_goto:used_as_goto2 in
      (Seq.append fixterms1 fixterms2, Seq.append fixfuncs1 fixfuncs2)
  | Case (ci, p, iv, item, branches) ->
      (* item must be a Rel which type is inductive (non-function) type *)
      let results =
        Array.map2
          (fun cstr_nargs br -> collect_fix_usage_rec ~inlinable_fixterms env sigma
            tail_position br (cstr_nargs + numargs) ~used_as_call ~used_as_goto)
          ci.Constr.ci_cstr_nargs branches
      in
      (concat_array_seq (Array.map fst results),
       concat_array_seq (Array.map snd results))
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let used_as_call2 = ref false :: used_as_call in
      let used_as_goto2 = ref false :: used_as_goto in
      if numargs = 0 then
        (* closure creation *)
        collect_fix_usage_rec ~inlinable_fixterms env2 sigma true b (numargs_of_exp env sigma term) ~used_as_call:used_as_call2 ~used_as_goto:used_as_goto2
      else
        collect_fix_usage_rec ~inlinable_fixterms env2 sigma tail_position b (numargs-1) ~used_as_call:used_as_call2 ~used_as_goto:used_as_goto2
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let fixterm_id = id_of_annotated_name nary.(i) in
      let inlinable = Id.Map.find (id_of_annotated_name nary.(i)) inlinable_fixterms in
      let h = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let used_as_call2 =
        list_rev_map_append
          (fun j -> ref (i = j && not tail_position && not inlinable))
          (iota_list 0 h)
          used_as_call
      in
      let used_as_goto2 = list_rev_map_append (fun () -> ref false) (ncons h () []) used_as_goto in
      let tail_position2 =
        if not tail_position then
          if inlinable then
            false (* A_K via GENBODY^{AT} *)
          else
            true (* B_K via GENBODY^{AN}: individual function will be generated *)
        else
          true (* B_K via GENBODY^{B} *)
      in
      let results =
        Array.map2
          (fun t f -> collect_fix_usage_rec ~inlinable_fixterms env2 sigma
            tail_position2 f (numargs_of_type env sigma t) ~used_as_call:used_as_call2 ~used_as_goto:used_as_goto2)
          tary fary
      in
      let fixterm = {
        fixterm_term_id = fixterm_id;
        fixterm_func_ids = Array.map id_of_annotated_name nary;
        fixterm_tail_position = tail_position;
        fixterm_numargs = numargs;
        fixterm_term_env = env;
        fixterm_term = term;
        fixterm_inlinable = inlinable;
        fixterm_outer_variables = []; (* dummy. updated by set_fixfuncinfo_naive_outer_variables *)
      } in
      let fixfuncs =
        Array.to_seq
          (CArray.map2_i
            (fun j name ty ->
              let (formal_arguments, return_type) = c_args_and_ret_type env sigma ty in
              {
                fixfunc_func_id = id_of_annotated_name nary.(j);
                fixfunc_func_index = j;
                fixfunc_term_env = env;
                fixfunc_func_env = env2;
                fixfunc_func = fary.(j);
                fixfunc_inlinable = inlinable;
                fixfunc_used_as_call = !(List.nth used_as_call2 (h - j - 1));
                fixfunc_used_as_goto = !(List.nth used_as_goto2 (h - j - 1));
                fixfunc_formal_arguments = formal_arguments;
                fixfunc_return_type = return_type;
                fixfunc_top_call = None; (* dummy. updated by detect_top_calls *)
                fixfunc_c_name = "dummy"; (* dummy. updated by determine_fixfunc_c_names *)
                fixfunc_outer_variables = []; (* dummy. updated by set_fixfuncinfo_naive_outer_variables *)
              })
            nary tary)
      in
      (Seq.cons fixterm (concat_array_seq (Array.map fst results)),
       Seq.append fixfuncs (concat_array_seq (Array.map snd results)))

let collect_fix_usage2
    ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    fixterm_info list * fixfunc_info list =
  let (fixterms, fixfuncs) = collect_fix_usage_rec ~inlinable_fixterms env sigma true term (numargs_of_exp env sigma term) ~used_as_call:[] ~used_as_goto:[] in
  (List.of_seq fixterms, List.of_seq fixfuncs)

let collect_fix_usage
    ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t)
    ~(fixfuncinfo : fixfuncinfo_t) : unit =
  let (fixterms, fixfuncs) = collect_fix_usage2 ~inlinable_fixterms env sigma term in
  List.iter
    (fun fixfunc ->
      Hashtbl.add fixfuncinfo fixfunc.fixfunc_func_id fixfunc)
    fixfuncs

let rec detect_top_calls (env : Environ.env) (sigma : Evd.evar_map)
    (top_c_func_name : string) (term : EConstr.t)
    ~(fixfuncinfo : fixfuncinfo_t) : unit =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      detect_top_calls env2 sigma top_c_func_name e ~fixfuncinfo
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      detect_top_calls env2 sigma top_c_func_name fary.(i) ~fixfuncinfo;
      let key = id_of_annotated_name nary.(i) in
      let usage = Hashtbl.find fixfuncinfo key in
      Hashtbl.replace fixfuncinfo key { usage with fixfunc_top_call = Some top_c_func_name }
  (* xxx: consider App *)
  | _ -> ()

let determine_fixfunc_c_names (fixfuncinfo : fixfuncinfo_t) : unit =
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
    fixfuncinfo

let rec fixterm_free_variables_rec (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) ~(result : (Id.t, Id.Set.t) Hashtbl.t) : Id.Set.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Array _ -> user_err (Pp.str "[codegen] Array is not supported for code generation")
  | Rel i ->
      let decl = Environ.lookup_rel i env in
      let name = Context.Rel.Declaration.get_name decl in
      Id.Set.singleton (id_of_name name)
  | Int _ | Float _ | Const _ | Construct _ -> Id.Set.empty
  | Proj (proj, e) -> fixterm_free_variables_rec env sigma e ~result
  | App (f, args) ->
      let fv_f = fixterm_free_variables_rec env sigma f ~result in
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
      let fv_e = fixterm_free_variables_rec env sigma e ~result in
      let fv_b = fixterm_free_variables_rec env2 sigma b ~result in
      Id.Set.union fv_e (Id.Set.remove id fv_b)
  | Case (ci, p, iv, item, branches) ->
      let item_id =
        let i = destRel sigma item in
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        id_of_name name
      in
      let fv_branches =
        Array.map (fixterm_free_variables_rec env sigma ~result) branches
      in
      Array.fold_right Id.Set.union fv_branches (Id.Set.singleton item_id)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let id = id_of_annotated_name x in
      let fv_b = fixterm_free_variables_rec env2 sigma b ~result in
      Id.Set.remove id fv_b
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ids = Array.map id_of_annotated_name nary in
      let fv_fary =
        Array.map (fixterm_free_variables_rec env2 sigma ~result) fary
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
  ignore (fixterm_free_variables_rec env sigma term ~result);
  result

let rec fixterm_fixfunc_relation_rec (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t)
    ~(fixterm_to_fixfuncs : (Id.t, Id.Set.t) Hashtbl.t)
    ~(fixfunc_to_fixterm : (Id.t, Id.t) Hashtbl.t) : unit =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Array _ -> user_err (Pp.str "[codegen] Array is not supported for code generation")
  | Rel i -> ()
  | Int _ | Float _ | Const _ | Construct _ -> ()
  | Proj (proj, e) -> fixterm_fixfunc_relation_rec env sigma e ~fixterm_to_fixfuncs ~fixfunc_to_fixterm
  | App (f, args) ->
      fixterm_fixfunc_relation_rec env sigma f ~fixterm_to_fixfuncs ~fixfunc_to_fixterm
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      fixterm_fixfunc_relation_rec env sigma e ~fixterm_to_fixfuncs ~fixfunc_to_fixterm;
      fixterm_fixfunc_relation_rec env2 sigma b ~fixterm_to_fixfuncs ~fixfunc_to_fixterm
  | Case (ci, p, iv, item, branches) ->
      Array.iter
        (fixterm_fixfunc_relation_rec env sigma ~fixterm_to_fixfuncs ~fixfunc_to_fixterm)
        branches
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      fixterm_fixfunc_relation_rec env2 sigma b ~fixterm_to_fixfuncs ~fixfunc_to_fixterm
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
        (fixterm_fixfunc_relation_rec env2 sigma ~fixterm_to_fixfuncs ~fixfunc_to_fixterm)
        fary

let fixterm_fixfunc_relation (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : (Id.t, Id.Set.t) Hashtbl.t * (Id.t, Id.t) Hashtbl.t =
  let fixterm_to_fixfuncs = Hashtbl.create 0 in
  let fixfunc_to_fixterm = Hashtbl.create 0 in
  fixterm_fixfunc_relation_rec env sigma term ~fixterm_to_fixfuncs ~fixfunc_to_fixterm;
  (fixterm_to_fixfuncs, fixfunc_to_fixterm)

let pr_outer_variable (outer : (string * string) list) : Pp.t =
  Pp.str "[" ++
  pp_joinmap_list (Pp.str ",")
    (fun (x,t) -> Pp.str "(" ++ Pp.str x ++ Pp.str "," ++ Pp.str t ++ Pp.str ")")
    outer ++
  Pp.str "]"

let check_eq_outer_variables outer1 outer2 =
  if outer1 <> outer2 then
    user_err (Pp.str "[codegen:bug] outer length differ:" +++ pr_outer_variable outer1 +++ Pp.str "<>" +++ pr_outer_variable outer2)

(*
  outer_variables_from_env computes outer variables in "naive" way:
  It may contain unused variables.
*)
let outer_variables_from_env ~(fixfuncinfo : fixfuncinfo_t) (env : Environ.env) (sigma : Evd.evar_map) : (string * string) list =
  let n = Environ.nb_rel env in
  let outer = ref [] in
  for i = 1 to n do
    let decl = Environ.lookup_rel i env in
    let x = Context.Rel.Declaration.get_name decl in
    let t = Context.Rel.Declaration.get_type decl in
    let id = id_of_name x in
    if not (Hashtbl.mem fixfuncinfo id) then (* Don't include fix-bounded functions *)
      outer := (str_of_name x, c_typename env sigma (EConstr.of_constr t)) :: !outer;
  done;
  !outer

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
    fixterm_free_variables;
  fixterm_outer_variables

let set_fixfuncinfo_outer_variables
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t)
    ~(fixfuncinfo : fixfuncinfo_t) : unit =
  let (fixterm_to_fixfuncs, fixfunc_to_fixterm) = fixterm_fixfunc_relation env sigma term in
  let fixterm_free_variables = fixterm_free_variables env sigma term in
  let outer_variables = compute_outer_variables env sigma fixterm_to_fixfuncs fixfunc_to_fixterm fixterm_free_variables in
  Hashtbl.filter_map_inplace
    (fun (fixfunc_id : Id.t) (info : fixfunc_info) ->
      let fixterm_id = Hashtbl.find fixfunc_to_fixterm fixfunc_id in
      let ov = outer_variables_from_env ~fixfuncinfo info.fixfunc_term_env sigma in
      if info.fixfunc_top_call <> None then
        Some { info with fixfunc_outer_variables = ov }
      else
        let ov = List.filter
          (fun (varname, vartype) -> Id.Set.mem (Id.of_string varname) (Hashtbl.find outer_variables fixterm_id))
          ov
        in
        Some { info with fixfunc_outer_variables = ov })
    fixfuncinfo

let collect_fix_info (env : Environ.env) (sigma : Evd.evar_map) (name : string) (term : EConstr.t) : fixfuncinfo_t =
  let fixfuncinfo = Hashtbl.create 0 in
  let numargs = numargs_of_exp env sigma term in
  let inlinable_fixterms = detect_inlinable_fixterm env sigma term numargs in
  ignore (collect_fix_usage ~inlinable_fixterms env sigma term ~fixfuncinfo);
  detect_top_calls env sigma name term ~fixfuncinfo;
  determine_fixfunc_c_names fixfuncinfo;
  set_fixfuncinfo_outer_variables env sigma term ~fixfuncinfo;
  (*show_fixfuncinfo env sigma fixfuncinfo;*)
  fixfuncinfo

let compute_called_fixfuncs (fixfuncinfo : fixfuncinfo_t) : fixfunc_info list =
  Hashtbl.fold
    (fun fixfunc_id info fixfuncs ->
      if info.fixfunc_used_as_call &&
         info.fixfunc_top_call = None then
        info :: fixfuncs
      else
        fixfuncs)
    fixfuncinfo
    []

let gen_switch_without_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  v 0 (
  hov 0 (str "switch" +++ str "(" ++ swexpr ++ str ")") +++
  vbrace (pp_sjoinmap_ary
    (fun (caselabel, pp_branch) ->
      str caselabel ++ str ":" ++ Pp.brk (1,2) ++ v 0 pp_branch)
    branches))

let gen_switch_with_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  gen_switch_without_break swexpr
    (Array.map
      (fun (caselabel, pp_branch) ->
        (caselabel, pp_branch +++ str "break;"))
      branches)

let gen_match (used : Id.Set.t) (gen_switch : Pp.t -> (string * Pp.t) array -> Pp.t)
    (gen_branch_body : Environ.env -> Evd.evar_map -> EConstr.t -> string list -> Pp.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (ci : case_info) (predicate : EConstr.t) (item : EConstr.t) (branches : EConstr.t array)
    (cargs : string list) : Pp.t =
  (*msg_debug_hov (Pp.str "[codegen] gen_match:1");*)
  let item_relindex = destRel sigma item in
  let item_type = Context.Rel.Declaration.get_type (Environ.lookup_rel item_relindex env) in
  (*msg_debug_hov (Pp.str "[codegen] gen_match: item_type=" ++ Printer.pr_econstr_env env sigma (EConstr.of_constr item_type));*)
  let item_cvar = carg_of_garg env item_relindex in
  (*let result_type = Retyping.get_type_of env sigma term in*)
  (*let result_type = Reductionops.nf_all env sigma result_type in*)
  (*msg_debug_hov (Pp.str "[codegen] gen_match:2");*)
  let c_deallocation =
    if Linear.is_linear env sigma (EConstr.of_constr item_type) then
      match ConstrMap.find_opt item_type !deallocator_cfunc_of_type with
      | None -> user_err (str "[codegen] cannot match linear variable without destructor:" +++ Printer.pr_econstr_env env sigma item)
      | Some dealloc_cfunc ->
          str dealloc_cfunc ++ str "(" ++ str item_cvar ++ str ");"
    else
      mt ()
  in
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
    let c_member_access =
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
    c_member_access +++ c_deallocation +++ c_branch_body
  in
  (*msg_debug_hov (Pp.str "[codegen] gen_match:3");*)
  let n = Array.length branches in
  let caselabel_accessors =
    Array.map
      (fun j ->
        (*msg_debug_hov (Pp.str "[codegen] gen_match:30");*)
        (case_cstrlabel env sigma (EConstr.of_constr item_type) j,
         Array.map
           (case_cstrmember env sigma (EConstr.of_constr item_type) j)
           (iota_ary 0 ci.ci_cstr_nargs.(j-1))))
      (iota_ary 1 n)
  in
  (*msg_debug_hov (Pp.str "[codegen] gen_match:4");*)
  if n = 1 then
    ((*msg_debug_hov (Pp.str "[codegen] gen_match:5");*)
    let accessors = snd caselabel_accessors.(0) in
    let br = branches.(0) in
    gen_branch accessors br)
  else
    ((*msg_debug_hov (Pp.str "[codegen] gen_match:6");*)
    let swfunc = case_swfunc env sigma (EConstr.of_constr item_type) in
    let swexpr = if swfunc = "" then str item_cvar else str swfunc ++ str "(" ++ str item_cvar ++ str ")" in
    (*msg_debug_hov (Pp.str "[codegen] gen_match:7");*)
    gen_switch swexpr
      (Array.map2
        (fun (caselabel, accessors) br ->
          (caselabel, gen_branch accessors br))
        caselabel_accessors branches))

let gen_proj (env : Environ.env) (sigma : Evd.evar_map)
    (pr : Projection.t) (item : EConstr.t) : Pp.t =
  let item_relindex = destRel sigma item in
  let item_type = Context.Rel.Declaration.get_type (Environ.lookup_rel item_relindex env) in
  let item_cvar = carg_of_garg env item_relindex in
  let accessor = case_cstrmember env sigma (EConstr.of_constr item_type) 1 (Projection.arg pr) in
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

let rec gen_assign ~(fixfuncinfo : fixfuncinfo_t) ~(used : Id.Set.t) ~(cont : assign_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  let pp = gen_assign1 ~fixfuncinfo ~used ~cont env sigma term cargs in
  (*msg_debug_hov (Pp.str "[codegen] gen_assign:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_assign1 ~(fixfuncinfo : fixfuncinfo_t) ~(used : Id.Set.t) ~(cont : assign_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _ | Array _
  | Cast _ | CoFix _ ->
      user_err (str "[codegen:gen_assign] unsupported term (" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_assign_cont cont (Pp.str str)
      else
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        (match Hashtbl.find_opt fixfuncinfo (id_of_name name) with
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
      gen_assign ~fixfuncinfo ~used ~cont env sigma f cargs2
  | Case (ci,predicate,iv,item,branches) ->
      let gen_switch =
        match cont.assign_cont_exit_label with
        | None -> gen_switch_with_break
        | Some _ -> gen_switch_without_break
      in
      gen_match used gen_switch (gen_assign ~fixfuncinfo ~used ~cont) env sigma ci predicate item branches cargs
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
      gen_assign ~fixfuncinfo ~used ~cont:cont1 env sigma e [] +++
      gen_assign ~fixfuncinfo ~used ~cont env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let ui = Hashtbl.find fixfuncinfo (id_of_annotated_name nary.(i)) in
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
        let cont2 = match cont.assign_cont_exit_label with
                    | None -> { cont with assign_cont_exit_label = Some exit_label }
                    | Some _ -> cont
        in
        let pp_exit =
          match cont.assign_cont_exit_label with
          | None -> Pp.hov 0 (Pp.str exit_label ++ Pp.str ":")
          | Some _ -> Pp.mt ()
        in
        let pp_bodies =
          Array.mapi
            (fun j nj ->
              let fj = fary.(j) in
              let uj = Hashtbl.find fixfuncinfo (id_of_annotated_name nj) in
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
              pp_label +++ gen_assign ~fixfuncinfo ~used ~cont:cont2 env2 sigma fj nj_formal_argvars)
            nary in
        let reordered_pp_bodies = Array.copy pp_bodies in
        Array.blit pp_bodies 0 reordered_pp_bodies 1 i;
        reordered_pp_bodies.(0) <- pp_bodies.(i);
        pp_assignments +++ pp_sjoin_ary reordered_pp_bodies +++ pp_exit

  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "[codegen] gen_assign: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_assign] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_assign ~fixfuncinfo ~used ~cont env2 sigma b rest)

let rec gen_tail ~(fixfuncinfo : fixfuncinfo_t) ~(used : Id.Set.t) ~(gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  (*msg_debug_hov (Pp.str "[codegen] gen_tail start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "(" ++
    pp_sjoinmap_list Pp.str cargs ++
    Pp.str ")");*)
  let pp = gen_tail1 ~fixfuncinfo ~used ~gen_ret env sigma term cargs in
  (*msg_debug_hov (Pp.str "[codegen] gen_tail return:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_tail1 ~(fixfuncinfo : fixfuncinfo_t) ~(used : Id.Set.t) ~(gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _ | Array _
  | Cast _ | CoFix _ ->
      user_err (str "[codegen:gen_tail] unsupported term (" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_ret (Pp.str str)
      else
        let key = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
        let uopt = Hashtbl.find_opt fixfuncinfo (id_of_name key) in
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
      gen_tail ~fixfuncinfo ~used ~gen_ret env sigma f cargs2
  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "[codegen] gen_tail: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_tail] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_tail ~fixfuncinfo ~used ~gen_ret env2 sigma b rest)
  | Case (ci,predicate,iv,item,branches) ->
      gen_match used gen_switch_without_break (gen_tail ~fixfuncinfo ~used ~gen_ret) env sigma ci predicate item branches cargs
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
      gen_assign ~fixfuncinfo ~used ~cont:cont1 env sigma e [] +++
      gen_tail ~fixfuncinfo ~used ~gen_ret env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ui = Hashtbl.find fixfuncinfo (id_of_annotated_name nary.(i)) in
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
            let uj = Hashtbl.find fixfuncinfo (id_of_annotated_name nj) in
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
            pp_label +++ gen_tail ~fixfuncinfo ~used ~gen_ret env2 sigma fj nj_formal_argvars)
          nary in
      let reordered_pp_bodies = Array.copy pp_bodies in
      Array.blit pp_bodies 0 reordered_pp_bodies 1 i;
      reordered_pp_bodies.(0) <- pp_bodies.(i);
      pp_assignments +++ pp_sjoin_ary reordered_pp_bodies

type top_fixterm_t = (*outer_variables*)((string * string) list) * Environ.env * EConstr.t

let rec detect_top_fixterms_rec
    ~(fixfuncinfo : fixfuncinfo_t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (tail_position : bool)
    (term : EConstr.t) (numargs : int) : top_fixterm_t Seq.t =
  detect_top_fixterms_rec1 ~fixfuncinfo env sigma tail_position term numargs
and detect_top_fixterms_rec1
    ~(fixfuncinfo : fixfuncinfo_t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (tail_position : bool)
    (term : EConstr.t) (numargs : int) : top_fixterm_t Seq.t =
  match EConstr.kind sigma term with
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Array _ -> user_err (Pp.str "[codegen] Array is not supported for code generation")
  | Rel i -> Seq.empty
  | Int _ | Float _ | Const _ | Construct _ -> Seq.empty
  | Proj _ -> Seq.empty
  | App (f, args) ->
      detect_top_fixterms_rec ~fixfuncinfo env sigma tail_position f
        (Array.length args + numargs)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      Seq.append
        (detect_top_fixterms_rec ~fixfuncinfo env sigma false e 0)
        (detect_top_fixterms_rec ~fixfuncinfo env2 sigma tail_position b numargs)
  | Case (ci, p, iv, item, branches) ->
      seq_flat_map2
        (fun cstr_nargs br ->
          detect_top_fixterms_rec ~fixfuncinfo env sigma tail_position br (cstr_nargs + numargs))
        (Array.to_seq ci.Constr.ci_cstr_nargs)
        (Array.to_seq branches)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      if numargs = 0 then
        user_err (Pp.str "[codegen:detect_top_fixterms] closure not supported yet")
      else
        detect_top_fixterms_rec ~fixfuncinfo env2 sigma tail_position b (numargs-1)
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      if tail_position then
        seq_flat_map2
          (fun t f ->
            let numargs2 = numargs_of_type env sigma t in
            detect_top_fixterms_rec ~fixfuncinfo env2 sigma tail_position f numargs2)
          (Array.to_seq tary) (Array.to_seq fary)
      else
        let id = id_of_annotated_name nary.(i) in
        let usage = Hashtbl.find fixfuncinfo id in
        if usage.fixfunc_inlinable then
          seq_flat_map2
            (fun t f ->
              let numargs2 = numargs_of_type env sigma t in
              detect_top_fixterms_rec ~fixfuncinfo env2 sigma tail_position f numargs2)
            (Array.to_seq tary) (Array.to_seq fary)
        else
          (* top functions found. *)
          Seq.cons
            (usage.fixfunc_outer_variables, env, term)
            (seq_flat_map2
              (fun t f ->
                let numargs2 = numargs_of_type env sigma t in
                detect_top_fixterms_rec ~fixfuncinfo env2 sigma true f numargs2)
              (Array.to_seq tary) (Array.to_seq fary))

let detect_top_fixterms
    ~(fixfuncinfo : fixfuncinfo_t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    top_fixterm_t list =
  let numargs = numargs_of_exp env sigma term in
  List.of_seq (detect_top_fixterms_rec ~fixfuncinfo env sigma true term numargs)

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

let obtain_function_bodies
    ~(fixfuncinfo : fixfuncinfo_t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    (((*varname*)string * (*vartype*)string) list *
     (*labels*)string list *
     Environ.env *
     EConstr.t) array =
  let gen_labels fixes =
    CList.map_filter
      (fun fix_name ->
        let fix_usage = Hashtbl.find fixfuncinfo (Id.of_string fix_name) in
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
      (detect_top_fixterms ~fixfuncinfo env sigma term)
  in
  Array.concat (result_whole_body :: results_top_fixterms)

let gen_function_header (static : bool) (return_type : string) (c_name : string)
    (formal_arguments : (string * string) list) : Pp.t =
  let pp_return_type =
    (if static then Pp.str "static" else Pp.mt ()) +++
    Pp.str return_type
  in
  let pp_parameters =
    Pp.str "(" ++
    (pp_joinmap_list (Pp.str "," ++ Pp.spc ())
      (fun (c_arg, t) ->
        hov 0 (Pp.str t +++ Pp.str c_arg))
      formal_arguments) ++
    Pp.str ")"
  in
  hov 0 pp_return_type +++
  Pp.str c_name ++
  hov 0 (pp_parameters)

let gen_func_single ~(static : bool) ~(cfunc_name : string) (env : Environ.env) (sigma : Evd.evar_map)
  (whole_body : EConstr.t) (return_type : string)
  (fixfuncinfo : fixfuncinfo_t) (used : Id.Set.t) : Pp.t =
  let bodies = obtain_function_bodies ~fixfuncinfo env sigma whole_body in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_ary
        (fun (args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
          gen_tail ~fixfuncinfo ~used ~gen_ret:gen_return env2 sigma body [])
        bodies)
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
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:6");*)
  v 0 (
  gen_function_header static return_type cfunc_name c_fargs +++
  vbrace (
    pp_sjoinmap_list
      (fun (c_type, c_var) -> hov 0 (str c_type +++ str c_var ++ str ";"))
      local_vars
    +++
    pp_body))

let gen_func_multi ~(static : bool) ~(cfunc_name : string) (env : Environ.env) (sigma : Evd.evar_map)
    (whole_body : EConstr.t) (formal_arguments : (string * string) list) (return_type : string)
    (fixfuncinfo : fixfuncinfo_t) (used : Id.Set.t) (called_fixfuncs : fixfunc_info list) : Pp.t =
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
    let pr_members args =
      pp_sjoinmap_list
        (fun (c_arg, t) -> hov 0 (Pp.str t +++ Pp.str c_arg ++ Pp.str ";"))
        args
    in
    pp_sjoinmap_list
      (fun info ->
        hv 0 (
        Pp.str ("struct codegen_args_" ^ info.fixfunc_c_name) +++
        hovbrace (
        pr_members info.fixfunc_outer_variables +++
        pr_members info.fixfunc_formal_arguments +++
        (if CList.is_empty info.fixfunc_outer_variables &&
            CList.is_empty info.fixfunc_formal_arguments then
          (* empty struct is undefined behavior *)
          Pp.str "int" +++ Pp.str "dummy;" (* Not reached because info.fixfunc_formal_arguments cannot be empty. *)
        else
          mt ())) ++ Pp.str ";"))
      called_fixfuncs +++
    hv 0 (
    Pp.str ("struct codegen_args_" ^ cfunc_name) +++
    hovbrace (
    pr_members formal_arguments +++
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
    let pr_entry_function static c_name func_index formal_arguments return_type =
      let pp_vardecl_args =
        Pp.str ("struct codegen_args_" ^ c_name) +++
        Pp.str "args" +++
        Pp.str "=" +++
        hovbrace (
          (pp_joinmap_list (Pp.str "," ++ Pp.spc ())
            (fun (c_arg, t) -> Pp.str c_arg)
            formal_arguments)) ++
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
        gen_function_header static return_type c_name formal_arguments +++
        vbrace (
          hov 0 (pp_vardecl_args) +++
          hov 0 (pp_vardecl_ret) +++
          hov 0 pp_call +++
          hov 0 pp_return))
    in
    pp_sjoinmap_list
      (fun info ->
        pr_entry_function true info.fixfunc_c_name (func_index_prefix ^ info.fixfunc_c_name)
          (List.append
            info.fixfunc_outer_variables
            info.fixfunc_formal_arguments)
          info.fixfunc_return_type)
      called_fixfuncs +++
    pr_entry_function static cfunc_name (func_index_prefix ^ cfunc_name)
      formal_arguments return_type
  in
  let bodies = obtain_function_bodies ~fixfuncinfo env sigma whole_body in
  let gen_ret = (gen_void_return ("(*(" ^ return_type ^ " *)ret)")) in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_ary
        (fun (args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          v 0 (
            pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
            gen_tail ~fixfuncinfo ~used ~gen_ret env2 sigma body []))
        bodies)
  in
  let pp_local_variables_decls =
    pp_sjoinmap_list
      (fun (c_type, c_var) -> hov 0 (str c_type +++ str c_var ++ str ";"))
      local_vars
  in
  let pp_switch_cases =
    pp_sjoinmap_list
      (fun info ->
        let pp_case =
          Pp.str "case" +++ Pp.str (func_index_prefix ^ info.fixfunc_c_name) ++ Pp.str ":"
        in
        let pp_assign_outer =
          pp_sjoinmap_list
            (fun (c_arg, t) ->
              hov 0 (
                Pp.str c_arg +++
                Pp.str "=" +++
                Pp.str ("((struct codegen_args_" ^ info.fixfunc_c_name ^ " *)args)->" ^ c_arg) ++
                Pp.str ";"))
            info.fixfunc_outer_variables
        in
        let pp_assign_args =
          pp_sjoinmap_list
            (fun (c_arg, t) ->
              hov 0 (
                Pp.str c_arg +++
                Pp.str "=" +++
                Pp.str ("((struct codegen_args_" ^ info.fixfunc_c_name ^ " *)args)->" ^ c_arg) ++
                Pp.str ";"))
            info.fixfunc_formal_arguments
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
      called_fixfuncs
  in
  let pp_switch_default = Pp.str "default:" in
  let pp_assign_args_default =
    if formal_arguments = [] then
      Pp.str ";"
    else
      pp_sjoinmap_list
        (fun (c_arg, t) ->
          hov 0 (
            Pp.str c_arg +++
            Pp.str "=" +++
            Pp.str ("((struct codegen_args_" ^ cfunc_name ^ " *)args)->" ^ c_arg) ++
            Pp.str ";"))
        formal_arguments
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
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:6");*)
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

(* the reslut of used_variables is used to avoid
   useless accessor call and assignment in translation of match-expression *)
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
  | Array _ -> user_err (Pp.str "[codegen] Array is not supported for code generation")
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
  | Case (ci, p, iv, item, branches) ->
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
  let (static, ctnt, ty, whole_body) = get_ctnt_type_body_from_cfunc cfunc_name in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_body = EConstr.of_constr whole_body in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments, return_type) = c_args_and_ret_type env sigma whole_ty in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:1");*)
  let fixfuncinfo = collect_fix_info env sigma cfunc_name whole_body in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:2");*)
  let used = used_variables env sigma whole_body in
  let called_fixfuncs = compute_called_fixfuncs fixfuncinfo in
  (if called_fixfuncs <> [] then
    gen_func_multi ~static ~cfunc_name env sigma whole_body formal_arguments return_type fixfuncinfo used called_fixfuncs
  else
    gen_func_single ~static ~cfunc_name env sigma whole_body return_type fixfuncinfo used) ++
  Pp.fnl ()

let gen_function (cfunc_name : string) : Pp.t =
  local_gensym_with (fun () -> gen_func_sub cfunc_name)

let gen_prototype (cfunc_name : string) : Pp.t =
  let (static, ctnt, ty, whole_body) = get_ctnt_type_body_from_cfunc cfunc_name in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments, return_type) = c_args_and_ret_type env sigma whole_ty in
  gen_function_header static return_type cfunc_name formal_arguments ++ Pp.str ";"

let fix_snippet (str : string) : string =
  let len = String.length str in
  if 0 < len && str.[len - 1] <> '\n' then
    str ^ "\n"
  else
    str

let add_snippet (str : string) : unit =
  let str' = fix_snippet str in
  codegen_add_source_generation (GenSnippet str')

let add_header_snippet (str : string) : unit =
  let str' = fix_snippet str in
  codegen_add_header_generation (GenSnippet str')

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

let gen_pp_iter (f : Pp.t -> unit) (gen_list : code_generation list) : unit =
  List.iter
    (fun gen ->
      match gen with
      | GenFunc cfunc_name ->
          f (gen_function cfunc_name ++ Pp.fnl ())
      | GenPrototype cfunc_name ->
          f (gen_prototype cfunc_name ++ Pp.fnl ())
      | GenSnippet str ->
          f (Pp.str str ++ Pp.fnl ()))
    gen_list

(* Vernacular commands *)

let command_gen (cfunc_list : string_or_qualid list) : unit =
  List.iter
    (fun cfunc_name ->
      match cfunc_name with
      | StrOrQid_Str str ->
          Feedback.msg_info (gen_function str)
      | StrOrQid_Qid qid ->
          (let env = Global.env () in
          let sigma = Evd.from_env env in
          let func = func_of_qualid env qid in
          let sp_cfg = codegen_auto_arguments_internal env sigma func in
          (if List.mem SorD_S sp_cfg.sp_sd_list then
            user_err (Pp.str "[codegen] function has static arguments:" +++ Printer.pr_constr_env env sigma func));
          let (env, sp_inst) =
            match ConstrMap.find_opt func sp_cfg.sp_instance_map with
            | None -> codegen_define_instance env sigma CodeGenFunction func [] None
            | Some sp_inst -> (env, sp_inst)
          in
          Feedback.msg_info (gen_function sp_inst.sp_cfunc_name)))
    cfunc_list

let command_snippet (str : string) : unit =
  add_snippet str

let command_header_snippet (str : string) : unit =
  add_header_snippet str

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

let gen_file (fn : string) (gen_list : code_generation list) : unit =
  (* open in the standard permission, 0o666, which will be masked by umask. *)
  (let (temp_fn, ch) = Filename.open_temp_file
    ~perms:0o666 ~temp_dir:(Filename.dirname fn) (Filename.basename fn) ".c" in
  let fmt = Format.formatter_of_out_channel ch in
  gen_pp_iter (Pp.pp_with fmt) gen_list;
  Format.pp_print_flush fmt ();
  close_out ch;
  Sys.rename temp_fn fn;
  msg_info_hov (str ("[codegen] file generated: " ^ fn)))

let gen_test (gen_list : code_generation list) : unit =
  gen_pp_iter Feedback.msg_info gen_list

let command_generate_file () : unit =
  List.iter
    (fun (fn, gen_list) -> gen_file fn (List.rev gen_list))
    (CString.Map.bindings !generation_map);
  generation_map := CString.Map.empty

let command_generate_test () : unit =
  List.iter
    (fun (fn, gen_list) -> Feedback.msg_info (Pp.str fn); gen_test (List.rev gen_list))
    (CString.Map.bindings !generation_map)
