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

module StrSet = Set.Make(String)
module IntSet = Set.Make(Int)

open Names
open Pp
open CErrors
open Constr
open EConstr

open Cgenutil
open State
open Linear
open Specialize

let get_ind_config (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : ind_config =
  match ConstrMap.find_opt (EConstr.to_constr sigma t) !ind_config_map with
  | Some ind_cfg -> ind_cfg
  | None -> user_err (Pp.str "[codegen:get_ind_config] C type not configured:" +++ Printer.pr_econstr_env env sigma t)

let c_typename (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : string =
  (get_ind_config env sigma t).c_type

let case_swfunc (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : string =
  let ind_cfg = get_ind_config env sigma t in
  match ind_cfg.c_swfunc with
  | Some c_swfunc -> c_swfunc
  | None -> user_err (
    Pp.str "inductive match configuration not registered:" +++
    Printer.pr_lconstr_env env sigma ind_cfg.coq_type)

let case_cstrlabel (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) : string =
  let ind_cfg = get_ind_config env sigma t in
  match ind_cfg.c_swfunc with
  | Some _ -> ind_cfg.cstr_configs.(j-1).c_caselabel
  | None -> raise (CodeGenError "[bug] inductive match configuration not registered") (* should be called after case_swfunc *)

let case_cstrfield (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) (j : int) (k : int) : string =
  let ind_cfg = get_ind_config env sigma t in
  match ind_cfg.c_swfunc with
  | Some _ -> ind_cfg.cstr_configs.(j-1).c_accessors.(k)
  | None -> raise (CodeGenError "[bug] inductive match configuration not registered") (* should be called after case_swfunc *)

let global_gensym () : string =
  let n = !gensym_id in
  gensym_id := n + 1;
  "g" ^ string_of_int n

let global_gensym_with_name (name : Name.t) : string =
  match name with
  | Names.Name.Anonymous -> global_gensym ()
  | Names.Name.Name id -> global_gensym () ^ "_" ^ (c_id (Id.to_string id))

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
  | Name.Anonymous -> user_err (Pp.str "str_of_name with anonymous name")
  | Name.Name id -> Id.to_string id

let str_of_annotated_name (name : Name.t Context.binder_annot) : string =
  str_of_name (Context.binder_name name)

let genc_farg (env : Environ.env) (sigma : Evd.evar_map) (farg : string * EConstr.types) : Pp.t =
  let (var, ty) = farg in
  hv 2 (str (c_typename env sigma ty) +++ str var)

let genc_fargs (env : Environ.env) (sigma : Evd.evar_map) (fargs : (string * EConstr.types) list) : Pp.t =
  match fargs with
  | [] -> str "void"
  | farg1 :: rest ->
      List.fold_left
        (fun pp farg -> pp ++ str "," +++ genc_farg env sigma farg)
        (genc_farg env sigma farg1)
        rest

let genc_assign (lhs : Pp.t) (rhs : Pp.t) : Pp.t =
  Pp.hov 0 (lhs +++ str "=" +++ rhs ++ str ";")

let genc_return (arg : Pp.t) : Pp.t =
  hv 0 (str "return" +++ arg ++ str ";")

let genc_void_return (retvar : string) (arg : Pp.t) : Pp.t =
  hv 0 (genc_assign (str retvar) arg +++ str "return;")

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
            user_err (Pp.str "C function name not configured:" +++ Printer.pr_constant env ctnt)
        | Constr.Construct (cstr, _) ->
            user_err (Pp.str "C constructor name not configured:" +++ Printer.pr_constructor env cstr)
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
        user_err (Pp.str "C function name not found:" +++
                  Pp.str cfunc_name)
    | Some (sp_cfg, sp_inst) -> (sp_cfg, sp_inst)
  in
  let ctnt =
    match sp_inst.sp_specialization_name with
    | SpExpectedId id ->
        codegen_specialization_specialize1 cfunc_name (* modify global env *)
    | SpDefinedCtnt ctnt -> ctnt
  in
  let env = Global.env () in
  let (ctnt, ty, body) =
    let cdef = Environ.lookup_constant ctnt env in
    let ty = cdef.Declarations.const_type in
    match Global.body_of_constant_body Library.indirect_accessor cdef with
    | None -> user_err (Pp.str "couldn't obtain the body:" +++
                        Printer.pr_constant env ctnt)
    | Some (body,_, _) -> (ctnt, ty, body)
  in
  (ctnt, ty, body)

let brace (pp : Pp.t) : Pp.t =
  hv 2 (str "{" +++ pp ++ brk (1,-2) ++ str "}")

let local_vars : ((string * string) list ref) list ref = ref []

let local_vars_with (f : unit -> 'a) : (string * string) list * 'a =
  let vars = ref [] in
  let old = !local_vars in
  local_vars := vars :: old;
  let ret = f () in
  local_vars := old;
  (!vars, ret)

let add_local_var (c_type : string) (c_var : string) : unit =
  if !local_vars = [] then
    user_err (Pp.str "[codegen:bug] add_local_var is called outside of local_vars_with");
  let vars = List.hd !local_vars in
  match List.find_opt (fun (c_type1, c_var1) -> c_var1 = c_var) !vars with
  | Some (c_type1, c_var1) ->
      (if c_type1 <> c_type then
        user_err (Pp.str "[codegen:bug] add_local_var : inconsistent typed variable"));
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
  fixfunc_c_name: string;
  fixfunc_used_as_call: bool;
  fixfunc_used_as_goto: bool;
  fixfunc_used_as_closure: bool;
  fixfunc_outer_variables: (string * EConstr.types) list;
  fixfunc_formal_arguments: (string * EConstr.types) list;
  fixfunc_return_type: EConstr.types;
  fixfunc_top_call: string option;
  fixfunc_goto_only_fix_term: bool;
}

type fixinfo_t = (Id.t, fixfunc_info) Hashtbl.t

let show_fixinfo (env : Environ.env) (sigma : Evd.evar_map) (fixinfo : fixinfo_t) : unit =
  Hashtbl.iter
    (fun fixfunc info ->
      Feedback.msg_debug (hv 2 (Pp.str (Id.to_string fixfunc) ++ Pp.str ":" +++
        Pp.str "c_name=" ++ Pp.str info.fixfunc_c_name +++
        Pp.str "used_as_call=" ++ Pp.bool info.fixfunc_used_as_call +++
        Pp.str "used_as_goto=" ++ Pp.bool info.fixfunc_used_as_goto +++
        Pp.str "used_as_closure=" ++ Pp.bool info.fixfunc_used_as_closure +++
        Pp.str "outer_variables=(" ++ pp_join_list (Pp.str ",") (List.map (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Printer.pr_econstr_env env sigma ty) info.fixfunc_outer_variables) ++ Pp.str ")" +++
        Pp.str "formal_arguments=(" ++ pp_join_list (Pp.str ",") (List.map (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Printer.pr_econstr_env env sigma ty) info.fixfunc_formal_arguments) ++ Pp.str ")" +++
        Pp.str "return_type=" ++ Printer.pr_econstr_env env sigma info.fixfunc_return_type ++ Pp.str ")" +++
        Pp.str "top_call=" ++ (match info.fixfunc_top_call with None -> Pp.str "None" | Some top -> Pp.str ("Some " ^ top)) +++
        Pp.str "goto_only_fix_term=" ++ Pp.bool info.fixfunc_goto_only_fix_term
      )))
    fixinfo

let rec collect_fix_usage (fixinfo : fixinfo_t) (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) (numargs : int) :
    (* variables at tail position *) IntSet.t *
    (* variables at non-tail position *) IntSet.t *
    (* variables at argument position *) IntSet.t =
  (*Feedback.msg_debug (Pp.str "[codegen:collect_fix_usage] start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs);*)
  let result = collect_fix_usage1 fixinfo env sigma term numargs in
  (*let (tailset, nontailset, argset) = result in
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
    Pp.str "}" +++
    Pp.str "argset={" ++
    pp_join_list (Pp.str ",")
      (List.map
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name)
        (IntSet.elements argset)) ++
    Pp.str "}"));*)
  result
and collect_fix_usage1 (fixinfo : fixinfo_t) (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) (numargs : int) :
    (* variables at tail position *) IntSet.t *
    (* variables at non-tail position *) IntSet.t *
    (* variables at argument position *) IntSet.t =
  match EConstr.kind sigma term with
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i -> (IntSet.singleton i, IntSet.empty, IntSet.empty)
  | Int _ | Float _ | Const _ | Construct _ -> (IntSet.empty, IntSet.empty, IntSet.empty)
  | Proj (proj, e) ->
      (* e must be a Rel which type is inductive (non-function) type *)
      (IntSet.empty, IntSet.empty, IntSet.empty)
  | Cast (e,ck,t) -> collect_fix_usage fixinfo env sigma e numargs
  | App (f, args) ->
      let (tailset_f, nontailset_f, argset_f) = collect_fix_usage fixinfo env sigma f (Array.length args + numargs) in
      let argset = Array.fold_left (fun set arg -> IntSet.add (destRel sigma arg) set) argset_f args in
      (tailset_f, nontailset_f, argset)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let (tailset_e, nontailset_e, argset_e) = collect_fix_usage fixinfo env sigma e 0 in
      let (tailset_b, nontailset_b, argset_b) = collect_fix_usage fixinfo env2 sigma b numargs in
      let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
      let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
      let argset_b = IntSet.map pred (IntSet.filter ((<) 1) argset_b) in
      let nontailset = IntSet.union
        (IntSet.union tailset_e nontailset_e)
        nontailset_b
      in
      let argset = IntSet.union argset_e argset_b in
      (tailset_b, nontailset, argset)
  | Case (ci, p, item, branches) ->
      (* item must be a Rel which type is inductive (non-function) type *)
      let branches_result = Array.mapi
        (fun i br -> collect_fix_usage fixinfo env sigma br
          (ci.Constr.ci_cstr_nargs.(i) + numargs))
        branches
      in
      let tailset =
        Array.fold_left
          (fun set (tailset_br, nontailset_br, argset_br) ->
            IntSet.union set tailset_br)
          IntSet.empty
          branches_result
      in
      let nontailset =
        Array.fold_left
          (fun set (tailset_br, nontailset_br, argset_br) ->
            IntSet.union set nontailset_br)
          IntSet.empty branches_result
      in
      let argset =
        Array.fold_left
          (fun set (tailset_br, nontailset_br, argset_br) ->
            IntSet.union set argset_br)
          IntSet.empty branches_result
      in
      (tailset, nontailset, argset)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      if numargs = 0 then
        (* closure creation *)
        let (tailset_b, nontailset_b, argset_b) = collect_fix_usage fixinfo env2 sigma b (numargs_of_exp env sigma term) in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        let argset_b = IntSet.map pred (IntSet.filter ((<) 1) argset_b) in
        (IntSet.empty, IntSet.union tailset_b nontailset_b, argset_b)
      else
        let (tailset_b, nontailset_b, argset_b) = collect_fix_usage fixinfo env2 sigma b (numargs-1) in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        let argset_b = IntSet.map pred (IntSet.filter ((<) 1) argset_b) in
        (tailset_b, nontailset_b, argset_b)
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let n = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let fixfuncs_result = Array.mapi
        (fun i f -> collect_fix_usage fixinfo env2 sigma f
          (numargs_of_type env sigma tary.(i)))
        fary
      in
      let tailset_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f, argset_f) ->
            IntSet.union set tailset_f)
          IntSet.empty fixfuncs_result
      in
      let nontailset_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f, argset_f) ->
            IntSet.union set nontailset_f)
          IntSet.empty fixfuncs_result
      in
      let argset_fs =
        Array.fold_left
          (fun set (tailset_f, nontailset_f, argset_f) ->
            IntSet.union set argset_f)
          IntSet.empty fixfuncs_result
      in
      let outer_variables = (* xxx: reduce variables *)
        let n = Environ.nb_rel env in
        List.rev_map
          (fun k ->
            let decl = Environ.lookup_rel k env in
            let name = Context.Rel.Declaration.get_name decl in
            let t = Context.Rel.Declaration.get_type decl in
            (str_of_name name, EConstr.of_constr t))
          (iota_list 1 n)
      in
      let goto_only_fix_term =
        not (IntSet.exists ((>=) n) nontailset_fs ||
             IntSet.exists ((>=) n) argset_fs)
      in
      for j = 1 to n do
        let fname = Context.binder_name nary.(j-1) in
        let used_as_goto = IntSet.mem j tailset_fs in
        let used_as_call = IntSet.mem j nontailset_fs in
        let used_as_closure = IntSet.mem j argset_fs in
        let gensym_with_name =
          if used_as_call || used_as_closure then
            global_gensym_with_name
          else
            str_of_name
        in
        let c_name = gensym_with_name fname in
        let args_and_ret_type = EConstr.decompose_prod sigma tary.(j-1) in
        let formal_arguments = List.rev_map
          (fun (x,t) ->
            let c_arg = str_of_annotated_name x in
            (c_arg, t))
          (fst args_and_ret_type)
        in
        let return_type = snd args_and_ret_type in
        Hashtbl.add fixinfo (id_of_name fname) {
          fixfunc_c_name = c_name;
          fixfunc_used_as_call = used_as_call;
          fixfunc_used_as_goto = used_as_goto;
          fixfunc_used_as_closure = used_as_closure;
          fixfunc_outer_variables = outer_variables;
          fixfunc_formal_arguments = formal_arguments;
          fixfunc_return_type = return_type;
          fixfunc_top_call = None; (* dummy. updated later *)
          fixfunc_goto_only_fix_term = goto_only_fix_term;
        }
      done;
      let tailset_fs' = IntSet.map (fun k -> k - n) (IntSet.filter ((<) n) tailset_fs) in
      let nontailset_fs' = IntSet.map (fun k -> k - n) (IntSet.filter ((<) n) nontailset_fs) in
      let argset_fs' = IntSet.map (fun k -> k - n) (IntSet.filter ((<) n) argset_fs) in
      if numargs < numargs_of_type env sigma tary.(i) || (* closure creation *)
         not goto_only_fix_term then
        (* At least one fix-bounded function is used at
          non-tail position or argument position.
          Assuming fix-bounded functions are strongly-connected,
          there is no tail position in this fix term. *)
        (IntSet.empty, IntSet.union tailset_fs' nontailset_fs', argset_fs')
      else
        (tailset_fs', nontailset_fs', argset_fs')

let rec detect_top_calls_rec (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t)
    (top_c_func_name : string) (outer_variables_rev : (string * EConstr.types) list) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      detect_top_calls_rec env2 sigma fixinfo top_c_func_name ((str_of_annotated_name x, t) :: outer_variables_rev) e
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      detect_top_calls_rec env2 sigma fixinfo top_c_func_name outer_variables_rev fary.(i);
      let key = id_of_annotated_name nary.(i) in
      let usage = Hashtbl.find fixinfo key in
      Hashtbl.replace fixinfo key {
        fixfunc_c_name = usage.fixfunc_c_name;
        fixfunc_used_as_call = usage.fixfunc_used_as_call;
        fixfunc_used_as_goto = usage.fixfunc_used_as_goto;
        fixfunc_used_as_closure = usage.fixfunc_used_as_closure;
        fixfunc_outer_variables = List.rev outer_variables_rev;
        fixfunc_formal_arguments = usage.fixfunc_formal_arguments;
        fixfunc_return_type = usage.fixfunc_return_type;
        fixfunc_top_call = Some top_c_func_name;
        fixfunc_goto_only_fix_term = usage.fixfunc_goto_only_fix_term;
      }
  (* xxx: consider App *)
  | _ -> ()

let detect_top_calls (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t)
    (top_c_func_name : string) (term : EConstr.t) : unit =
  detect_top_calls_rec env sigma fixinfo top_c_func_name [] term

let collect_fix_info (env : Environ.env) (sigma : Evd.evar_map) (name : string) (term : EConstr.t) : fixinfo_t =
  let fixinfo = Hashtbl.create 0 in
  let numargs = numargs_of_exp env sigma term in
  ignore (collect_fix_usage fixinfo env sigma term numargs);
  detect_top_calls env sigma fixinfo name term;
  show_fixinfo env sigma fixinfo;
  fixinfo

let needs_multiple_functions (fixinfo : fixinfo_t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool =
  Hashtbl.fold
    (fun name info b ->
      if b then
        b
      else if Option.has_some info.fixfunc_top_call then
        false
      else if info.fixfunc_used_as_call || info.fixfunc_used_as_closure then
        true
      else
        false)
    fixinfo
    false

let gen_switch_without_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  hv 0 (
  hov 0 (str "switch" +++ str "(" ++ swexpr ++ str ")") +++
  brace (pp_join_ary (spc ())
    (Array.map
      (fun (caselabel, pp_branch) ->
        str caselabel ++ str ":" ++ Pp.brk (1,2) ++ hv 0 pp_branch)
      branches)))

let gen_switch_with_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  gen_switch_without_break swexpr
    (Array.map
      (fun (caselabel, pp_branch) ->
        (caselabel, pp_branch +++ str "break;"))
      branches)

let gen_match (gen_switch : Pp.t -> (string * Pp.t) array -> Pp.t)
    (gen_branch_body : Environ.env -> Evd.evar_map -> EConstr.t -> string list -> Pp.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (ci : case_info) (predicate : EConstr.t) (item : EConstr.t) (branches : EConstr.t array)
    (cargs : string list) : Pp.t =
  (*Feedback.msg_debug (Pp.str "gen_match:1");*)
  let item_relindex = destRel sigma item in
  let item_type = Context.Rel.Declaration.get_type (Environ.lookup_rel item_relindex env) in
  (*Feedback.msg_debug (Pp.str "gen_match: item_type=" ++ Printer.pr_econstr_env env sigma (EConstr.of_constr item_type));*)
  let item_cvar = carg_of_garg env (destRel sigma item) in
  (*let result_type = Retyping.get_type_of env sigma term in*)
  (*let result_type = Reductionops.nf_all env sigma result_type in*)
  (*Feedback.msg_debug (Pp.str "gen_match:2");*)
  let gen_branch accessors br =
    (
    let branch_type = Retyping.get_type_of env sigma br in
    let branch_type = Reductionops.nf_all env sigma branch_type in
    let (branch_arg_types, _) = decompose_prod sigma branch_type in
    let branch_arg_types = CList.lastn (Array.length accessors) branch_arg_types in
    let branch_arg_types = CArray.rev_of_list branch_arg_types in
    let c_vars = Array.map
      (fun (x,t) ->
        let c_var = str_of_annotated_name x in
        add_local_var (c_typename env sigma t) c_var;
        c_var)
      branch_arg_types
    in
    let c_field_access =
      pp_join_ary (spc ())
        (Array.map2
          (fun c_var access -> genc_assign (str c_var) (str access ++ str "(" ++ str item_cvar ++ str ")"))
          c_vars accessors)
    in
    let c_branch_body =
      gen_branch_body env sigma br (List.append (Array.to_list c_vars) cargs)
    in
    c_field_access +++ c_branch_body)
  in
  (*Feedback.msg_debug (Pp.str "gen_match:3");*)
  let n = Array.length branches in
  let caselabel_accessors =
    Array.map
      (fun j ->
        (*Feedback.msg_debug (Pp.str "gen_match:30");*)
        (case_cstrlabel env sigma (EConstr.of_constr item_type) j,
         Array.map
           (case_cstrfield env sigma (EConstr.of_constr item_type) j)
           (iota_ary 0 ci.ci_cstr_nargs.(j-1))))
      (iota_ary 1 n)
  in
  (*Feedback.msg_debug (Pp.str "gen_match:4");*)
  if n = 1 then
    ((*Feedback.msg_debug (Pp.str "gen_match:5");*)
    let accessors = snd caselabel_accessors.(0) in
    let br = branches.(0) in
    gen_branch accessors br)
  else
    ((*Feedback.msg_debug (Pp.str "gen_match:6");*)
    let swfunc = case_swfunc env sigma (EConstr.of_constr item_type) in
    let swexpr = if swfunc = "" then str item_cvar else str swfunc ++ str "(" ++ str item_cvar ++ str ")" in
    (*Feedback.msg_debug (Pp.str "gen_match:7");*)
    gen_switch swexpr
      (Array.mapi
        (fun i br ->
          let (caselabel, accessors) = caselabel_accessors.(i) in
          (caselabel, gen_branch accessors br))
        branches))

let gen_parallel_assignment (env : Environ.env) (sigma : Evd.evar_map) (assignments : (string * string * EConstr.types) array) : Pp.t =
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
          add_local_var (c_typename env sigma a_ty) tmp;
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

let rec  gen_assign (fixinfo : fixinfo_t) (cont : assign_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  let pp = gen_assign1 fixinfo cont env sigma term cargs in
  (*Feedback.msg_debug (Pp.str "gen_assign:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_assign1 (fixinfo : fixinfo_t) (cont : assign_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
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
            if info.fixfunc_goto_only_fix_term then
              let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) info.fixfunc_formal_arguments cargs in
              let pp_assignments = gen_parallel_assignment env sigma (Array.of_list assginments) in
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
      gen_assign1 fixinfo cont env sigma f cargs2
  | Case (ci,predicate,item,branches) ->
      let gen_switch =
        match cont.assign_cont_exit_label with
        | None -> gen_switch_with_break
        | Some _ -> gen_switch_without_break
      in
      gen_match gen_switch (gen_assign fixinfo cont) env sigma ci predicate item branches cargs
  | LetIn (x,e,t,b) ->
      let c_var = str_of_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      let cont1 = { assign_cont_ret_var = c_var;
                    assign_cont_exit_label = None; } in
      gen_assign fixinfo cont1 env sigma e [] +++
      gen_assign fixinfo cont env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      if Array.exists
           (fun n ->
             let ui = Hashtbl.find fixinfo (id_of_annotated_name n) in
             ui.fixfunc_used_as_call || ui.fixfunc_used_as_closure)
           nary
      then
        (let msg = ref (Pp.mt ()) in
          msg := !msg +++ Pp.hov 0 (Pp.str "[codegen] gen_assign: fix term not purely tail recursive:") +++
                          Pp.hv 0 (Printer.pr_econstr_env env sigma term);
         Array.iter
           (fun n ->
             let ui = Hashtbl.find fixinfo (id_of_annotated_name n) in
             if ui.fixfunc_used_as_call then
               msg := !msg +++ Pp.hov 0 (Pp.str "recursive function," +++ Pp.str ui.fixfunc_c_name ++ Pp.str ", is used as a call");
             if ui.fixfunc_used_as_closure then
               msg := !msg +++ Pp.hov 0 (Pp.str "recursive function," +++ Pp.str ui.fixfunc_c_name ++ Pp.str ", is used as a closure"))
           nary;
          user_err (Pp.hv 0 !msg));
      let env2 = EConstr.push_rec_types prec env in
      let ui = Hashtbl.find fixinfo (id_of_annotated_name nary.(i)) in
      let ni_formal_arguments = ui.fixfunc_formal_arguments in
      if List.length cargs < List.length ni_formal_arguments then
        user_err (Pp.str "[codegen] gen_assign: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) ni_formal_arguments cargs in
      let pp_assignments = gen_parallel_assignment env sigma (Array.of_list assginments) in
      let ni_funcname = ui.fixfunc_c_name in
      let exit_label = "exit_" ^ ni_funcname in
      let pp_exit = Pp.hov 0 (Pp.str exit_label ++ Pp.str ":") in
      let pp_bodies =
        Array.mapi
          (fun j nj ->
            let fj = fary.(j) in
            let uj = Hashtbl.find fixinfo (id_of_annotated_name nj) in
            let nj_formal_arguments = uj.fixfunc_formal_arguments in
            List.iter
              (fun (c_arg, t) -> add_local_var (c_typename env sigma t) c_arg)
              nj_formal_arguments;
            let nj_formal_argvars = List.map fst nj_formal_arguments in
            let nj_funcname = uj.fixfunc_c_name in
            let pp_label =
              if uj.fixfunc_used_as_goto || Option.is_empty uj.fixfunc_top_call then
                Pp.str ("entry_" ^ nj_funcname)  ++ Pp.str ":"
              else
                Pp.mt ()
            in
            let cont2 = { assign_cont_ret_var = cont.assign_cont_ret_var ;
                          assign_cont_exit_label = Some exit_label; } in
            hv 0 (pp_label +++ gen_assign fixinfo cont2 env2 sigma fj nj_formal_argvars))
          nary in
      let reordered_pp_bodies = Array.copy pp_bodies in
      Array.blit pp_bodies 0 reordered_pp_bodies 1 i;
      reordered_pp_bodies.(0) <- pp_bodies.(i);
      pp_assignments +++ pp_join_ary (Pp.spc ()) reordered_pp_bodies +++ pp_exit

  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "gen_assign: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_assign] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_assign fixinfo cont env2 sigma b rest)

  | Proj _ ->
      user_err (str "[codegen:gen_assign] not impelemented (" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term)

let rec gen_tail (fixinfo : fixinfo_t) (gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  (*Feedback.msg_debug (Pp.str "gen_tail start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "(" ++
    pp_join_list (Pp.spc ()) (List.map Pp.str cargs) ++
    Pp.str ")");*)
  let pp = gen_tail1 fixinfo gen_ret env sigma term cargs in
  (*Feedback.msg_debug (Pp.str "gen_tail return:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_tail1 (fixinfo : fixinfo_t) (gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
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
            let pp_assignments = gen_parallel_assignment env sigma (Array.of_list assginments) in
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
      gen_tail fixinfo gen_ret env sigma f cargs2
  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "gen_tail: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_tail] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_tail fixinfo gen_ret env2 sigma b rest)
  | Case (ci,predicate,item,branches) ->
      gen_match gen_switch_without_break (gen_tail fixinfo gen_ret) env sigma ci predicate item branches cargs
  | LetIn (x,e,t,b) ->
      let c_var = str_of_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      let cont1 = { assign_cont_ret_var = c_var;
                    assign_cont_exit_label = None; } in
      gen_assign fixinfo cont1 env sigma e [] +++
      gen_tail fixinfo gen_ret env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ui = Hashtbl.find fixinfo (id_of_annotated_name nary.(i)) in
      let ni_formal_arguments = ui.fixfunc_formal_arguments in
      if List.length cargs < List.length ni_formal_arguments then
        user_err (Pp.str "[codegen] gen_tail: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) ni_formal_arguments cargs in
      let pp_assignments = gen_parallel_assignment env sigma (Array.of_list assginments) in
      let pp_bodies =
        Array.mapi
          (fun j nj ->
            let fj = fary.(j) in
            let uj = Hashtbl.find fixinfo (id_of_annotated_name nj) in
            let nj_formal_arguments = uj.fixfunc_formal_arguments in
            List.iter
              (fun (c_arg, t) -> add_local_var (c_typename env sigma t) c_arg)
              nj_formal_arguments;
            let nj_formal_argvars = List.map fst nj_formal_arguments in
            let nj_funcname = uj.fixfunc_c_name in
            let pp_label =
              if uj.fixfunc_used_as_goto || Option.is_empty uj.fixfunc_top_call then
                Pp.str ("entry_" ^ nj_funcname) ++ Pp.str ":"
              else
                Pp.mt ()
            in
            hv 0 (pp_label +++ gen_tail fixinfo gen_ret env2 sigma fj nj_formal_argvars))
          nary in
      let reordered_pp_bodies = Array.copy pp_bodies in
      Array.blit pp_bodies 0 reordered_pp_bodies 1 i;
      reordered_pp_bodies.(0) <- pp_bodies.(i);
      pp_assignments +++ pp_join_ary (Pp.spc ()) reordered_pp_bodies

  | Proj _ -> user_err (Pp.str "gen_tail: unsupported term Proj:" +++ Printer.pr_econstr_env env sigma term)

let rec obtain_function_bodies_rec (env : Environ.env) (sigma : Evd.evar_map)
    (fargs : (string * EConstr.types) list) (fixfuncs : string list) (term : EConstr.t) :
    ((string * EConstr.types) list * string list * Environ.env * EConstr.t) array =
  match EConstr.kind sigma term with
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let c_var = (str_of_annotated_name x, t) in
      obtain_function_bodies_rec env2 sigma (c_var :: fargs) fixfuncs b
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let bodies = Array.mapi
        (fun j nj ->
          let fixfunc_name = str_of_annotated_name nj in
          let fj = fary.(j) in
          obtain_function_bodies_rec env2 sigma fargs (fixfunc_name :: fixfuncs) fj)
        nary
      in
      let reordered_bodies = Array.copy bodies in
      Array.blit bodies 0 reordered_bodies 1 i;
      reordered_bodies.(0) <- bodies.(i);
      array_flatten reordered_bodies
  | _ ->
      [|(fargs, fixfuncs, env, term)|]

let obtain_function_bodies (env : Environ.env) (sigma : Evd.evar_map)
   (term : EConstr.t) :
    ((string * EConstr.types) list *
     string list *
     Environ.env *
     EConstr.t) array =
  obtain_function_bodies_rec env sigma [] [] term

let gen_func2_single (cfunc_name : string) (env : Environ.env) (sigma : Evd.evar_map)
  (whole_body : EConstr.t) (return_type : EConstr.types)
  (fixinfo : fixinfo_t) : Pp.t =
  let bodies = obtain_function_bodies env sigma whole_body in
  let (first_args, _, _, _) = bodies.(0) in
  let c_fargs = List.rev first_args in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_join_ary (spc ()) (Array.map
        (fun (args, fixes, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var (c_typename env sigma arg_type) arg_name)
            args;
          let labels = CList.map_filter
            (fun fix_name ->
              let fix_usage = Hashtbl.find fixinfo (Id.of_string fix_name) in
              if fix_usage.fixfunc_used_as_goto || Option.is_empty fix_usage.fixfunc_top_call then
                Some ("entry_" ^ fix_usage.fixfunc_c_name)
              else
                None)
            fixes
          in
          hv 0 (
            pp_join_list (spc ())
              (List.map (fun l -> Pp.str (l ^ ":")) labels) +++
            gen_tail fixinfo genc_return env2 sigma body []))
        bodies))
    in
  let local_vars = List.filter
    (fun (c_type, c_var) ->
      match List.find_opt (fun (c_var1, ty1) -> c_var = c_var1) c_fargs with
      | Some _ -> false (* xxx: check type mismach *)
      | None -> true)
    local_vars
  in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:6");*)
  hv 0 (
  hv 0 (str "static" +++
        str (c_typename env sigma return_type)) +++
  str cfunc_name ++ str "(" ++
  hv 0 (genc_fargs env sigma c_fargs) ++
  str ")" +++
  brace (
    pp_postjoin_list (spc ())
      (List.map
        (fun (c_type, c_var) -> hv 0 (str c_type +++ str c_var ++ str ";"))
        local_vars)
    ++
    pp_body))

let gen_func2_multi (cfunc_name : string) (env : Environ.env) (sigma : Evd.evar_map)
    (whole_body : EConstr.t) (formal_arguments : (string * EConstr.types) list) (return_type : EConstr.types)
    (fixinfo : fixinfo_t) : Pp.t =
  let pp_struct_args =
    let pr_fields args =
      pp_sjoin_list
        (List.map
          (fun (c_arg, t) ->
            hv 0 (Pp.str (c_typename env sigma t) +++
            Pp.str c_arg ++
            Pp.str ";"))
          args)
    in
    (Hashtbl.fold
      (fun fixfunc_name info pp ->
        if (info.fixfunc_used_as_call || info.fixfunc_used_as_closure) &&
           Option.is_empty info.fixfunc_top_call then
          hv 0 (
          Pp.str ("struct codegen_args_" ^ info.fixfunc_c_name) +++
          Pp.str "{" +++
          pr_fields info.fixfunc_outer_variables +++
          pr_fields info.fixfunc_formal_arguments +++
          (if CList.is_empty info.fixfunc_outer_variables &&
              CList.is_empty info.fixfunc_formal_arguments then
            (* empty struct is undefined behavior *)
            Pp.str "int" +++ Pp.str "dummy;"
          else
            mt ()) +++
          Pp.str "};")
        else
          pp)
      fixinfo
      (mt ())) +++
    hv 0 (
    Pp.str ("struct codegen_args_" ^ cfunc_name) +++
    Pp.str "{" +++
    pr_fields formal_arguments +++
    (if CList.is_empty formal_arguments then
      (* empty struct is undefined behavior *)
      Pp.str "int" +++ Pp.str "dummy;"
    else
      mt ()) +++
    Pp.str "};")
  in
  let pp_forward_decl =
    hv 0 (
      Pp.str "static void" +++
      Pp.str ("codegen_functions_" ^ cfunc_name) ++
      Pp.str "(int g, void *args, void *ret);")
  in
  let pp_entry_functions =
    let pr_entry_function c_name func_num formal_arguments return_type =
      let pp_return_type =
        Pp.str "static" +++
        Pp.str (c_typename env sigma return_type)
      in
      let pp_parameters =
        Pp.str "(" ++
        (pp_join_list (Pp.str "," ++ Pp.spc ())
          (List.map
            (fun (c_arg, t) ->
              hv 0 (Pp.str (c_typename env sigma t) +++
              Pp.str c_arg))
            formal_arguments)) ++
        Pp.str ")"
      in
      let pp_vardecl_args =
        Pp.str ("struct codegen_args_" ^ c_name) +++
        Pp.str "args" +++
        Pp.str "=" +++
        Pp.str "{" +++
        (pp_join_list (Pp.str "," ++ Pp.spc ())
          (List.map
            (fun (c_arg, t) -> Pp.str c_arg)
            formal_arguments)) +++
        Pp.str "};"
      in
      let pp_vardecl_ret =
        Pp.str (c_typename env sigma return_type) +++
        Pp.str "ret;"
      in
      let pp_call =
        Pp.str ("codegen_functions_" ^ cfunc_name) ++
        Pp.str "(" ++
        Pp.int func_num ++ Pp.str "," +++
        Pp.str "&args," +++
        Pp.str "&ret);"
      in
      let pp_return =
        Pp.str "return ret;"
      in
      hv 0 (
        hov 0 pp_return_type +++
        Pp.str c_name ++
        hov 0 (pp_parameters) +++
        brace (
          hov 0 (pp_vardecl_args) +++
          hov 0 (pp_vardecl_ret) +++
          hov 0 pp_call +++
          hov 0 pp_return))
    in
    snd (Hashtbl.fold
      (fun fixfunc_name info (i,pp) ->
        if (info.fixfunc_used_as_call || info.fixfunc_used_as_closure) &&
           Option.is_empty info.fixfunc_top_call then
          let pp_result = pr_entry_function info.fixfunc_c_name i
            (List.append
              info.fixfunc_outer_variables
              info.fixfunc_formal_arguments)
            info.fixfunc_return_type in
          (i+1, pp_result)
        else
          (i, pp))
      fixinfo
      (1, mt ())) +++
    pr_entry_function cfunc_name 0
      formal_arguments return_type
  in
  let bodies = obtain_function_bodies env sigma whole_body in
  let gen_ret = (genc_void_return ("(*(" ^ c_typename env sigma return_type ^ " *)ret)")) in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_join_ary (spc ()) (Array.map
        (fun (args, fixes, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var (c_typename env sigma arg_type) arg_name)
            args;
          let labels = CList.map_filter
            (fun fix_name ->
              let fix_usage = Hashtbl.find fixinfo (Id.of_string fix_name) in
              if fix_usage.fixfunc_used_as_goto || Option.is_empty fix_usage.fixfunc_top_call then
                Some ("entry_" ^ fix_usage.fixfunc_c_name)
              else
                None)
            fixes
          in
          hv 0 (
            pp_join_list (spc ())
              (List.map (fun l -> Pp.str (l ^ ":")) labels) +++
            gen_tail fixinfo gen_ret env2 sigma body []))
        bodies))
    in
  let pp_local_variables_decls =
    pp_join_list (spc ())
      (List.map
        (fun (c_type, c_var) -> hv 0 (str c_type +++ str c_var ++ str ";"))
        local_vars)
  in
  let (num_cases, pp_switch_cases) =
    (Hashtbl.fold
      (fun fixfunc_name info (i,pp) ->
        if info.fixfunc_used_as_call || info.fixfunc_used_as_closure then
          let pp_case =
            Pp.str "case" +++ Pp.int i ++ Pp.str ":"
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
            hv 0 (
              pp_assign_outer +++
              pp_assign_args +++
              hov 0 pp_goto)
          in
          (i+1, pp_result)
        else
          (i, pp))
      fixinfo
      (1, mt ()))
  in
  let num_cases = num_cases - 1 in
  let pp_assign_args_default =
    pp_sjoin_list
      (List.map
        (fun (c_arg, t) ->
          hv 0 (
            Pp.str c_arg +++
            Pp.str "=" +++
            Pp.str ("((struct codegen_args_" ^ cfunc_name ^ " *)args)->" ^ c_arg) ++
            Pp.str ";"))
        formal_arguments)
  in
  let pp_switch_body =
    pp_switch_cases +++
    Pp.str "default:" ++ Pp.brk (1,2) ++
    hv 0 pp_assign_args_default
  in
  let pp_switch =
    if num_cases = 0 then
      pp_assign_args_default
    else
      hov 0 (Pp.str "switch" +++ Pp.str "(g)") +++
      brace pp_switch_body
  in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:6");*)
  hv 0 (
    pp_struct_args +++
    pp_forward_decl +++
    pp_entry_functions +++
    Pp.str "static void" +++
    Pp.str ("codegen_functions_" ^ cfunc_name) ++
    Pp.str "(int g, void *args, void *ret)") +++
    brace (
      pp_local_variables_decls +++
      pp_switch +++
      pp_body)

let gen_func2_sub (cfunc_name : string) : Pp.t =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (ctnt, ty, whole_body) = get_ctnt_type_body_from_cfunc cfunc_name in
  linear_type_check_term whole_body;
  let whole_body = EConstr.of_constr whole_body in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let args_and_ret_type = decompose_prod sigma whole_ty in
  let formal_arguments = List.rev_map
    (fun (x,t) ->
      let c_arg = str_of_annotated_name x in
      (c_arg, t))
    (fst args_and_ret_type)
  in
  let return_type = snd args_and_ret_type in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:1");*)
  let fixinfo = collect_fix_info env sigma cfunc_name whole_body in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:2");*)
  if needs_multiple_functions fixinfo env sigma whole_body then
    gen_func2_multi cfunc_name env sigma whole_body formal_arguments return_type fixinfo
  else
    gen_func2_single cfunc_name env sigma whole_body return_type fixinfo

let gen_function2 (cfunc_name : string) : Pp.t =
  local_gensym_with (fun () -> gen_func2_sub cfunc_name)

let gen_function0 (cfunc_name : string) : Pp.t =
  gen_function2 cfunc_name

(* Vernacular commands *)

let gen2 (cfunc_list : string list) : unit =
  List.iter
    (fun cfunc_name ->
      Feedback.msg_info (gen_function2 cfunc_name))
    cfunc_list

let gen (cfunc_list : string list) : unit =
  List.iter
    (fun cfunc_name ->
      Feedback.msg_info (gen_function0 cfunc_name))
    cfunc_list

let codegen_snippet (str : string) : unit =
  let len = String.length str in
  let str' =
    if 0 < len && str.[len - 1] <> '\n' then
      str ^ "\n"
    else
      str
  in
  generation_list := GenSnippet str' :: !generation_list

let gen_file (fn : string) (gen_list : code_generation list) : unit =
  (* open in the standard permission, 0o666, which will be masked by umask. *)
  (let (temp_fn, ch) = Filename.open_temp_file
    ~perms:0o666 ~temp_dir:(Filename.dirname fn) (Filename.basename fn) ".c" in
  let fmt = Format.formatter_of_out_channel ch in
  List.iter
    (fun gen ->
      match gen with
      | GenFunc cfunc_name ->
          Pp.pp_with fmt (gen_function0 cfunc_name ++ Pp.fnl ())
      | GenSnippet str ->
          Pp.pp_with fmt (Pp.str str ++ Pp.fnl ()))
    gen_list;
  Format.pp_print_flush fmt ();
  close_out ch;
  Sys.rename temp_fn fn;
  Feedback.msg_info (str ("file generated: " ^ fn)))

let generate_file (fn : string) =
  gen_file fn (List.rev !generation_list);
  generation_list := []
