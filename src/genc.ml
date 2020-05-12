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
open GlobRef
open Pp
open CErrors
open Constr
open EConstr

open Cgenutil
open State
open Linear
open Specialize

let (+++) d1 d2 =
  if Pp.ismt d1 then
    d2
  else if Pp.ismt d2 then
    d1
  else
    d1 ++ Pp.spc () ++ d2

let c_funcname (fname : string) : string =
  c_id fname

let goto_label (fname : string) : string =
  "entry_" ^ (c_id fname)

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

let global_gensym_with_str (suffix : string) : string =
  global_gensym () ^ "_" ^ (c_id suffix)

let global_gensym_with_name (name : Name.t) : string =
  match name with
  | Names.Name.Anonymous -> global_gensym ()
  | Names.Name.Name id -> global_gensym () ^ "_" ^ (c_id (Id.to_string id))

let global_gensym_with_nameopt (nameopt : Name.t option) : string =
  match nameopt with
  | None -> global_gensym ()
  | Some name -> global_gensym_with_name name

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
  "v" ^ string_of_int n

let local_gensym_with_str (suffix : string) : string =
  local_gensym () ^ "_" ^ (c_id suffix)

let local_gensym_with_name (name : Name.t) : string =
  match name with
  | Name.Anonymous -> local_gensym ()
  | Name.Name id -> local_gensym () ^ "_" ^ (c_id (Id.to_string id))

let local_gensym_with_annotated_name (name : Name.t Context.binder_annot) : string =
  local_gensym_with_name (Context.binder_name name)

let local_gensym_with_nameopt (nameopt : Name.t option) : string =
  match nameopt with
  | None -> local_gensym ()
  | Some name -> local_gensym_with_name name

let rec argtys_and_rety_of_type (sigma : Evd.evar_map) (ty : EConstr.types) : EConstr.types list * EConstr.types =
  match EConstr.kind sigma ty with
  | Prod (name, ty', body) ->
      let (argtys, rety) = argtys_and_rety_of_type sigma body in
      (ty :: argtys, rety)
  | _ -> ([], ty)

let rec nargtys_and_rety_of_type (sigma : Evd.evar_map) (n : int) (ty : EConstr.types) : EConstr.types list * EConstr.types =
  if n == 0 then
    ([], ty)
  else
    match EConstr.kind sigma ty with
    | Prod (name, ty', body) ->
        let (argtys, rety) = nargtys_and_rety_of_type sigma (n-1) body in
        (ty :: argtys, rety)
    | _ -> user_err (Pp.str "too few prods in type")

type context_elt =
  | CtxVar of string
  | CtxRec of
      string *
      (string * EConstr.types) array (* fname, argname_argtype_array *)

let rec fargs_and_body (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (string * EConstr.types) list * Environ.env * EConstr.t =
  match EConstr.kind sigma term with
  | Constr.Lambda (name, ty, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      let var = local_gensym_with_name (Context.binder_name name) in
      let fargs1, env1, body1 = fargs_and_body env2 sigma body in
      let fargs2 = (var, ty) :: fargs1 in
      (fargs2, env1, body1)
  | _ -> ([], env, term)

let fargs_and_body_ary (env : Environ.env) (sigma : Evd.evar_map)
    (strnameary : string array) (ty : EConstr.types)
    (ia : int array) (i : int)
    (nameary : Name.t array)
    (tyary : EConstr.types array)
    (funary : EConstr.t array) :
    (string *
     EConstr.types *
     (string * EConstr.types) list *
     context_elt list *
     Environ.env *
     EConstr.t) array =
  let fb_ary = Array.map (fun term1 -> fargs_and_body env sigma term1) funary in
  let ctxrec_ary = Array.map
    (fun j ->
      let nm = strnameary.(j) in
      let fargs, envb, _(* _ was previously named body but was not used *) =
        fb_ary.(j) in
      CtxRec (nm, Array.of_list fargs))
    (iota_ary 0 (Array.length funary))
  in
  let ctxrec_list = Array.to_list ctxrec_ary in
  let fb_ary2 = array_map2
    (fun ty (fargs, envb, body) ->
      let context1 = List.rev_map (fun (var, ty) -> CtxVar var) fargs in
      let context2 = List.append context1 (List.rev ctxrec_list) in
      (ty, fargs, context2, envb, body))
    tyary fb_ary
  in
  array_map2 (fun nm (ty, fargs, context, envb, body) ->
      (nm, ty, fargs, context, envb, body))
    strnameary fb_ary2

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

let genc_vardecl (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) (varname : string) : Pp.t =
  hv 0 (str (c_typename env sigma ty) +++ str varname ++ str ";")

let genc_varinit (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) (varname : string) (init : Pp.t) : Pp.t =
  hv 0 (str (c_typename env sigma ty) +++ str varname +++ str "=" +++ init ++ str ";")

let genc_assign (lhs : Pp.t) (rhs : Pp.t) : Pp.t =
  Pp.hov 0 (lhs +++ str "=" +++ rhs ++ str ";")

let genc_return (arg : Pp.t) : Pp.t =
  hv 0 (str "return" +++ arg ++ str ";")

let genc_void_return (retvar : string) (arg : Pp.t) : Pp.t =
  hv 0 (genc_assign (str retvar) arg +++ str "return;")

let varname_of_rel (context : context_elt list) (i : int) : string =
  match List.nth context (i-1) with
  | CtxVar varname -> varname
  | _ -> raise (Invalid_argument "unexpected context element")

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
  let gen_constant = Array.length argvars = 0 && sp_inst.sp_gen_constant
  in
  if gen_constant then
    str c_fname
  else
    str c_fname ++ str "(" ++
    pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
    str ")"

let genc_app (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (f : EConstr.t) (argsary : EConstr.t array) : Pp.t =
  let argvars = Array.map (fun arg -> varname_of_rel context (destRel sigma arg)) argsary in
  match EConstr.kind sigma f with
  | Constr.Rel i ->
      (match List.nth context (i-1) with
      | CtxVar _ -> user_err (str "indirect call not implemented")
      | CtxRec (fname, _) ->
          let c_fname = c_funcname fname in
          str c_fname ++ str "(" ++
          pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
          str ")")
  | Constr.Const _ | Constr.Construct _ ->
      gen_app_const_construct env sigma f argvars
  | _ ->
      user_err (Pp.str "[codegen:bug] genc_app expects Rel or Const")

let genc_multi_assign (env : Environ.env) (sigma : Evd.evar_map) (assignments : (string * (string * EConstr.types)) array) : Pp.t =
  let ass = Array.to_list assignments in
  let ass = List.filter (fun (lhs, (rhs, ty)) -> lhs <> rhs) ass in
  let rpp = ref (mt ()) in
  (* better algorithm using topological sort? *)
  let rec loop ass =
    match ass with
    | [] -> ()
    | a :: rest ->
        let rhs_list = List.map (fun (lhs, (rhs, ty)) -> rhs) ass in
        let blocked_ass, nonblocked_ass =
          List.partition (fun (lhs, (rhs, ty)) -> List.mem lhs rhs_list) ass
        in
        if nonblocked_ass <> [] then
          (List.iter
            (fun (lhs, (rhs, ty)) ->
              let pp = genc_assign (str lhs) (str rhs) in
              rpp := !rpp +++ pp)
            nonblocked_ass;
          loop blocked_ass)
        else
          (let a_lhs, (a_rhs, a_ty) = a in
          let tmp = local_gensym () in
          let pp = genc_varinit env sigma a_ty tmp (str a_lhs) in
          (rpp := !rpp +++ pp);
          let ass2 = List.map
            (fun (lhs, (rhs, ty)) ->
              if rhs = a_lhs then (lhs, (tmp, ty)) else (lhs, (rhs, ty)))
            ass
          in
          loop ass2)
  in
  loop ass;
  !rpp

let genc_goto (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (ctxrec : string * (string * EConstr.types) array) (argsary : EConstr.t array) : Pp.t =
  let fname, argvars = ctxrec in
  (if Array.length argsary <> Array.length argvars then
    user_err (str "partial function invocation not supported yet");
  let fname_argn = goto_label fname in
  let assignments =
    (array_map2
      (fun (var, ty) arg -> (var, (varname_of_rel context (destRel sigma arg), ty)))
      argvars argsary)
  in
  let pp_assigns = genc_multi_assign env sigma assignments in
  let pp_goto = (hv 0 (str "goto" +++ str fname_argn ++ str ";")) in
  if Pp.ismt pp_assigns then pp_goto else pp_assigns +++ pp_goto)

let genc_const (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (ctnt : Constant.t) : Pp.t =
  genc_app env sigma context (mkConst ctnt) [| |]

let genc_construct (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (cstr : Names.constructor) : Pp.t =
  genc_app env sigma context (mkConstruct cstr) [| |]

let split_case_tyf (sigma : Evd.evar_map) (tyf : EConstr.t) : EConstr.types * EConstr.t =
  match EConstr.kind sigma tyf with
  | Constr.Lambda (name, ty, body) -> (ty, body)
  | _ -> user_err (str "unexpected case type function")

let rec strip_outer_lambdas (sigma : Evd.evar_map) (ndecls : int) (term : EConstr.t) : (Name.t Context.binder_annot * EConstr.types) list * EConstr.t =
  if ndecls = 0 then
    ([], term)
  else
    match EConstr.kind sigma term with
    | Constr.Lambda (name, ty, body) ->
        let (decls, innermostbody) = strip_outer_lambdas sigma (ndecls-1) body in
        ((name, ty) :: decls, innermostbody)
    | _ -> user_err (str "case body lambda nesting is not enough")

let genc_case_branch_body (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> EConstr.constr -> Pp.t)
    (exprty : EConstr.types) (exprvar : string) (ndecls : int)
    (br : EConstr.t) (cstr_index : int) : Pp.t =
  let (decls, body) = strip_outer_lambdas sigma ndecls br in
  let decls2 =
    List.map2
      (fun (name, ty) field_index ->
        let name = Context.binder_name name in
        let varname = local_gensym_with_name name in
        let cstr_field = case_cstrfield env sigma exprty cstr_index field_index in
        (CtxVar varname, genc_varinit env sigma ty varname (str cstr_field ++ str "(" ++ str exprvar ++ str ")")))
       decls
      (iota_list 0 (List.length decls))
  in
  let context2 = List.rev_append (List.map fst decls2) context in
  let decls3 = List.map snd decls2 in
  pp_postjoin_list (spc ()) decls3 ++ bodyfunc env sigma context2 body

let genc_case_branch (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> EConstr.constr -> Pp.t)
    (exprty : EConstr.types) (exprvar : string) (ndecls : int)
    (br : EConstr.t) (cstr_index : int) : Pp.t =
  let cstr_label = case_cstrlabel env sigma exprty cstr_index in
  let pp_label = str cstr_label ++ str ":" in
  hv 0 (hv 0 (pp_label +++ str "{") ++ brk (1,2) ++
    hv 0 (genc_case_branch_body env sigma context bodyfunc exprty exprvar ndecls br cstr_index) +++
    str "}")

let genc_case_nobreak (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list) (ci : Constr.case_info) (tyf : EConstr.t)
    (expr : EConstr.t) (brs : EConstr.t array)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> EConstr.constr -> Pp.t) : Pp.t =
  let (exprty, rety) = split_case_tyf sigma tyf in
  let exprvar = varname_of_rel context (destRel sigma expr) in
  if Array.length brs = 1 then
    let ndecls = ci.Constr.ci_cstr_ndecls.(0) in
    let br = brs.(0) in
    let cstr_index = 1 in
    genc_case_branch_body env sigma context bodyfunc exprty exprvar ndecls br cstr_index
  else
    let swfunc = case_swfunc env sigma exprty in
    let swexpr = if swfunc = "" then str exprvar else str swfunc ++ str "(" ++ str exprvar ++ str ")" in
    hv 0 (
    hv 0 (str "switch" +++ str "(" ++ swexpr ++ str ")") +++
    str "{" ++ brk (1,2) ++
    hv 0 (
    pp_join_ary (spc ())
      (array_map3
        (genc_case_branch env sigma context bodyfunc exprty exprvar)
        ci.Constr.ci_cstr_ndecls
        brs
        (iota_ary 1 (Array.length brs)))) +++ str "}")

let genc_case_break (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list) (ci : Constr.case_info) (tyf : EConstr.t)
    (expr : EConstr.t) (brs : EConstr.t array)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> EConstr.constr -> Pp.t) : Pp.t =
  genc_case_nobreak env sigma context ci tyf expr brs
    (fun envb sigma context2 body -> bodyfunc envb sigma context2 body +++ str "break;")

let genc_geninitvar (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) (namehint : Names.Name.t) (init : Pp.t) : Pp.t * string =
  let varname = local_gensym_with_name namehint in
  (genc_varinit env sigma ty varname init, varname)

(* not tail position. return a variable *)
let rec genc_body_var (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (namehint : Names.Name.t) (term : EConstr.t) (termty : EConstr.types) : Pp.t * string =
  match EConstr.kind sigma term with
  | Constr.Rel i ->
      (mt (), varname_of_rel context i)
  | Constr.LetIn (name, expr, exprty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
      let name = Context.binder_name name in
      let env2 = EConstr.push_rel decl env in
      let (exprbody, exprvarname) = genc_body_var env sigma context name expr exprty in
      let (bodybody, bodyvarname) = genc_body_var env2 sigma (CtxVar exprvarname :: context) namehint body termty in
      (exprbody +++ bodybody, bodyvarname)
  | Constr.App (f, argsary) ->
      genc_geninitvar env sigma termty namehint (genc_app env sigma context f argsary)
  | Constr.Case (ci, tyf, expr, brs) ->
      let varname = local_gensym_with_name namehint in
      (genc_vardecl env sigma termty varname +++
       genc_case_break env sigma context ci tyf expr brs
        (fun envb sigma context2 body -> genc_body_assign envb sigma context2 varname body),
      varname)
  | Constr.Const ctntu ->
      genc_geninitvar env sigma termty namehint (genc_const env sigma context (out_punivs ctntu))
  | Constr.Construct cstru ->
      genc_geninitvar env sigma termty namehint (genc_construct env sigma context (out_punivs cstru))
  | _ -> (user_err (str "not impelemented (genc_body_var:" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term))

(* not tail position. assign to the specified variable *)
and genc_body_assign (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (retvar : string) (term : EConstr.t) : Pp.t =
  match EConstr.kind sigma term with
  | Constr.Rel i ->
      genc_assign (str retvar) (str (varname_of_rel context i))
  | Constr.LetIn (name, expr, exprty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
      let name = Context.binder_name name in
      let env2 = EConstr.push_rel decl env in
      let (exprbody, varname) = genc_body_var env sigma context name expr exprty in
      exprbody +++
      genc_body_assign env2 sigma (CtxVar varname :: context) retvar body
  | Constr.App (f, argsary) ->
      genc_assign (str retvar) (genc_app env sigma context f argsary)
  | Constr.Case (ci, tyf, expr, brs) ->
      genc_case_break env sigma context ci tyf expr brs
        (fun envb sigma context2 body -> genc_body_assign envb sigma context2 retvar body)
  | Constr.Const ctntu ->
      genc_assign (str retvar) (genc_const env sigma context (out_punivs ctntu))
  | Constr.Construct cstru ->
      genc_assign (str retvar) (genc_construct env sigma context (out_punivs cstru))
  | _ -> (user_err (str "not impelemented (genc_body_assign:" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term))

(* tail position.  "return" part is generalized as gen_ret. *)
let rec genc_body_tail (gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (term : EConstr.t) : Pp.t =
  match EConstr.kind sigma term with
  | Constr.Rel i ->
      gen_ret (str (varname_of_rel context i))
  | Constr.LetIn (name, expr, exprty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
      let name = Context.binder_name name in
      let env2 = EConstr.push_rel decl env in
      let (exprbody, varname) = genc_body_var env sigma context name expr exprty in
      exprbody +++
      genc_body_tail gen_ret env2 sigma (CtxVar varname :: context) body
  | Constr.App (f, argsary) ->
      (match EConstr.kind sigma f with
      | Constr.Rel i ->
          (match List.nth context (i-1) with
          | CtxRec (fname, argvars) -> genc_goto env sigma context (fname, argvars) argsary
          | _ -> gen_ret (genc_app env sigma context f argsary))
      | _ -> gen_ret (genc_app env sigma context f argsary))
  | Constr.Case (ci, tyf, expr, brs) ->
      genc_case_nobreak env sigma context ci tyf expr brs (genc_body_tail gen_ret)
  | Constr.Const ctntu ->
      gen_ret (genc_const env sigma context (out_punivs ctntu))
  | Constr.Construct cstru ->
      gen_ret (genc_construct env sigma context (out_punivs cstru))
  | _ -> (user_err (str "not impelemented (genc_body_tail:" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term))

let found_funref (context : (int * bool ref * bool ref * bool ref) option list) (i : int) =
  match List.nth context (i-1) with
  | None -> ()
  | Some callsites ->
      let nargs, headcall, tailcall, partcall = callsites in
      partcall := true

let found_callsite (tail : bool) (context : (int * bool ref * bool ref * bool ref) option list) (i : int) (n : int) : unit =
  match List.nth context (i-1) with
  | None -> ()
  | Some callsites ->
      let nargs, headcall, tailcall, partcall = callsites in
      if nargs <= n then
        if tail then
          tailcall := true
        else
          headcall := true
      else
        partcall := true

let rec scan_callsites_rec (env : Environ.env) (sigma : Evd.evar_map) (tail : bool) (context : (int * bool ref * bool ref * bool ref) option list) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Constr.Const ctntu -> ()
  | Constr.Construct cstru -> ()
  | Constr.Rel i ->
      found_funref context i
  | Constr.Cast (expr, kind, ty) ->
      scan_callsites_rec env sigma false context expr
  | Constr.LetIn (name, expr, ty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = EConstr.push_rel decl env in
      (scan_callsites_rec env sigma false context expr;
      scan_callsites_rec env2 sigma tail (None :: context) body)
  | Constr.App (f, argsary) ->
      ((match EConstr.kind sigma f with
      | Constr.Rel i -> found_callsite tail context i (Array.length argsary)
      | _ -> scan_callsites_rec env sigma false context f);
      Array.iter (scan_callsites_rec env sigma false context) argsary)
  | Constr.Case (ci, tyf, expr, brs) ->
      (scan_callsites_rec env sigma false context expr;
      array_iter2
        (fun nargs br ->
          let context2 = ncons nargs None context in
          let (decls, br2) = strip_outer_lambdas sigma nargs br in
          let env2 = EConstr.push_rel_context
            (List.map
              (fun (name, ty) -> Context.Rel.Declaration.LocalAssum (name, ty))
              (List.rev decls))
            env in
          scan_callsites_rec env2 sigma tail context2 br2)
        ci.Constr.ci_cstr_nargs brs)
  | Constr.Proj (proj, expr) ->
      scan_callsites_rec env sigma false context expr
  | _ -> user_err ~hdr:"scan_callsites_rec" (hv 0 (str "unexpected term:" +++ Printer.pr_econstr_env env sigma term))

let scan_callsites (sigma : Evd.evar_map) (i : int)
    (ntfcb_ary : (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array) :
    (bool * bool * bool) array =
  let context = Array.to_list (array_rev (Array.mapi
    (fun j (nm, ty, fargs, ctx, envb, body) ->
      Some (List.length fargs, ref (j = i), ref false, ref false))
    ntfcb_ary))
  in
  Array.iter
    (fun (nm, ty, fargs, ctx, envb, body) ->
      scan_callsites_rec envb sigma true (ncons (List.length fargs) None context) body)
    ntfcb_ary;
  Array.map
    (fun callsites_opt ->
      match callsites_opt with
      | Some (nargs, headcall, tailcall, partcall) -> (!headcall, !tailcall, !partcall)
      | None -> (user_err (Pp.str "[codgen:bug] scan_callsites needs callsites")))
    (array_rev (Array.of_list context))

let genc_func_single (env : Environ.env) (sigma : Evd.evar_map)
    (fname : string) (ty : EConstr.types)
    (fargs : (string * EConstr.types) list)
    (context : context_elt list) (body : EConstr.t) : Pp.t =
  (*let (ty, fargs, context, body) = fargs_and_body fname term in*)
  let (argtys, rety) = argtys_and_rety_of_type sigma ty in
  (if List.length argtys <> List.length fargs then
    user_err (str ("function value not supported yet: " ^
      string_of_int (List.length argtys) ^ " prods and " ^
      string_of_int (List.length fargs) ^ " lambdas")));
  let c_fname = c_funcname fname in
  hv 0 (
  hv 0 (str "static" +++
        str (c_typename env sigma rety)) +++
  str c_fname ++ str "(" ++
  hv 0 (genc_fargs env sigma fargs) ++
  str ")" +++
  str "{" ++ brk (1,2) ++
  hv 0 (
    genc_body_tail genc_return env sigma context body) +++ str "}")

let find_headcalls
    (ntfcb_ary : (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array)
    (callsites_ary : (bool * bool * bool) array) :
    (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array =
  Array.concat
    (Array.to_list
      (array_map2
        (fun ntfcb (headcall, tailcall, partcall) ->
          if headcall then [| ntfcb |] else [| |])
        ntfcb_ary callsites_ary))

let genc_mufun_struct_one (env : Environ.env) (sigma : Evd.evar_map) (ntfcb : string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) : Pp.t =
  let nm, ty, fargs, context, envb, body = ntfcb in
  hv 0 (
  str "struct" +++
  str nm +++
  str "{" +++
  pp_postjoin_list (str ";" ++ spc ()) (List.map (genc_farg env sigma) fargs) ++
  str "};")

let genc_mufun_structs (env : Environ.env) (sigma : Evd.evar_map)
    (ntfcb_ary : (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.map (genc_mufun_struct_one env sigma) ntfcb_ary2)

let genc_mufun_entry (env : Environ.env) (sigma : Evd.evar_map) (mfnm : string) (i : int) (ntfcb : string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) : Pp.t =
  let nm, ty, fargs, context, envb, body = ntfcb in
  let (argtys, rety) = nargtys_and_rety_of_type sigma (List.length fargs) ty in
  let c_fname = c_funcname nm in
  hv 0 (
  str "static" +++
  str (c_typename env sigma rety) +++
  str c_fname ++ str "(" ++
  hv 0 (genc_fargs env sigma fargs) ++
  str ")" +++
  str "{" ++ brk (1,2) ++
  hv 0 (
    hv 0 (str "struct" +++ str nm +++ str "args" +++
      str "=" +++ str "{" +++
      pp_join_list (str "," ++ spc ())
        (List.map
          (fun (var, ty) -> hv 0 (str var))
        fargs) +++ str "};") +++
    hv 0 (str (c_typename env sigma rety) +++ str "ret;") +++
    hv 0 (str mfnm ++ str "(" ++ int i ++ str "," +++ str "&args," +++ str "&ret);") +++
    hv 0 (str "return" +++ str "ret;")) +++ str "}")

let genc_mufun_entries (env : Environ.env) (sigma : Evd.evar_map) (mfnm : string)
    (ntfcb_ary : (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.mapi (genc_mufun_entry env sigma mfnm) ntfcb_ary2)

let genc_mufun_forward_decl (mfnm : string) : Pp.t =
  hv 0 (
  str "static" +++
  str "void" +++
  str mfnm ++ str "(" ++
  hv 0 (
    hv 0 (str "int" +++ str "i") ++ str "," +++
    hv 0 (str "void*" +++ str "argsp") ++ str "," +++
    hv 0 (str "void*" +++ str "retp")) ++ str ");")

let genc_mufun_bodies_func (env : Environ.env) (sigma :Evd.evar_map) (mfnm : string) (i : int)
    (ntfcb_ary : (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  hv 0 (
  str "static" +++
  str "void" +++
  str mfnm ++ str "(" ++
  hv 0 (
    hv 0 (str "int" +++ str "i") ++ str "," +++
    hv 0 (str "void*" +++ str "argsp") ++ str "," +++
    hv 0 (str "void*" +++ str "retp")) ++ str ")" +++
  str "{" ++ brk (1,2) ++
  hv 0 (
    pp_join_ary (spc ())
      (Array.map
        (fun (nm, ty, fargs, context, envb, body) ->
           pp_join_list (spc ())
             (List.map
               (fun (var, ty) -> hv 0 (str (c_typename env sigma ty) +++ str var ++ str ";"))
               fargs))
        ntfcb_ary) +++
    hv 0 (str "switch" +++ str "(i)") +++ str "{" ++ brk (1,2) ++
      hv 0 (
        pp_join_ary (spc ())
          (Array.mapi
            (fun j (nm, ty, fargs, context, envb, body) ->
              let headcall, tailcall, partcall = callsites_ary.(j) in
              let (argtys, rety) = nargtys_and_rety_of_type sigma (List.length fargs) ty in
              let fname_argn = goto_label nm in
              hv 0 (
                (if j == i then str "default:" else hv 0 (str "case" +++ int j ++ str ":")) ++ brk (1,2) ++
                hv 0 (
                  pp_join_list (spc ())
                    (List.map
                      (fun (var, ty) -> hv 0 (str var +++ str "=" +++ str "((struct" +++ str nm +++ str "*)argsp)->" ++ str var ++ str ";"))
                      fargs) +++
                  (if tailcall then str fname_argn ++ str ":;" ++ spc () else mt ()) ++
                  let gen_ret = (genc_void_return ("(*(" ^ c_typename env sigma rety ^ " *)retp)")) in
                  genc_body_tail gen_ret envb sigma context body +++
                  str "return;")))
            ntfcb_ary)) +++ str "}") +++
    str "}")

let genc_mufun_single_func (env : Environ.env) (sigma : Evd.evar_map) (mfnm : string) (i : int)
    (ntfcb_ary : (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let entry_nm, entry_ty, entry_fargs, entry_context, entry_envb, entry_body = ntfcb_ary.(i) in
  let (entry_argtys, entry_rety) = nargtys_and_rety_of_type sigma (List.length entry_fargs) entry_ty in
  let c_fname = c_funcname entry_nm in
  let label_fname_argn = goto_label entry_nm in
  hv 0 (
  str "static" +++
  str (c_typename env sigma entry_rety) +++
  str c_fname ++ str "(" ++
  hv 0 (genc_fargs env sigma entry_fargs) ++
  str ")" +++
  str "{" ++ brk (1,2) ++
  hv 0 (
    pp_postjoin_ary (spc ())
      (Array.mapi
        (fun j (nm, ty, fargs, context, envb, body) ->
          if j = i then
            mt ()
          else
            pp_join_list (spc ())
              (List.map
                (fun (var, ty) -> hv 0 (str (c_typename env sigma ty) +++ str var ++ str ";"))
                fargs))
        ntfcb_ary) ++
    (if i = 0 then mt () else hv 0 (str "goto" +++ str label_fname_argn ++ str ";") ++ spc ()) ++
    pp_join_ary (spc ())
      (Array.mapi
        (fun j (nm, ty, fargs, context, envb, body) ->
          let headcall, tailcall, partcall = callsites_ary.(j) in
          let fname_argn = goto_label nm in
          hv 0 (
            (if tailcall || (i <> 0 && i == j) then str fname_argn ++ str ":;" ++ spc () else mt ()) ++
            genc_body_tail genc_return envb sigma context body))
        ntfcb_ary)) +++ str "}")

let genc_func_mutual (env : Environ.env) (sigma : Evd.evar_map) (mfnm : string) (i : int)
    (ntfcb_ary : (string * EConstr.types * (string * EConstr.types) list * context_elt list * Environ.env * EConstr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let num_entry_funcs = Array.fold_left (+) 0 (Array.map (fun (headcall, tailcall, partcall) -> if headcall then 1 else 0) callsites_ary) in
  if num_entry_funcs = 1 then
    genc_mufun_single_func env sigma mfnm i ntfcb_ary callsites_ary
  else
    genc_mufun_structs env sigma ntfcb_ary callsites_ary +++
    genc_mufun_forward_decl mfnm +++
    genc_mufun_entries env sigma mfnm ntfcb_ary callsites_ary +++
    genc_mufun_bodies_func env sigma mfnm i ntfcb_ary callsites_ary

let genc_func (env : Environ.env) (sigma : Evd.evar_map) (fname : string) (ty : EConstr.types) (term : EConstr.t) : Pp.t =
  local_gensym_with (fun () ->
  match EConstr.kind sigma term with
  | Constr.Fix ((ia, i), ((nameary, tyary, funary) as prec)) ->
      let env2 = push_rec_types prec env in
      let nameary' = Array.map Context.binder_name nameary in
      let strnameary = Array.mapi (fun j nm ->
          if j = i then
            fname
          else
            let nm = Context.binder_name nm in
            global_gensym_with_name nm)
        nameary
      in
      let ntfcb_ary = fargs_and_body_ary env2 sigma strnameary ty ia i nameary' tyary funary in
      let callsites_ary = scan_callsites sigma i ntfcb_ary in
      let mfnm = global_gensym_with_str fname in
      genc_func_mutual env sigma mfnm i ntfcb_ary callsites_ary
  | _ ->
      let fargs, envb, body = fargs_and_body env sigma term in
      let context = List.rev_map (fun (var, ty) -> CtxVar var) fargs in
      genc_func_single envb sigma fname ty fargs context body)

let get_ctnt_type_body (env : Environ.env) (name : Libnames.qualid) : Constant.t * Constr.types * Constr.t =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef ctnt ->
      begin match Global.body_of_constant Library.indirect_accessor ctnt with
      | Some (b,_,_) ->
          let (ty, _) = Typeops.type_of_global_in_context env reference in
          (ctnt, ty, b)
      | None -> user_err (Pp.str "can't genc axiom")
      end
  | VarRef _ -> user_err (Pp.str "can't genc VarRef")
  | IndRef _ -> user_err (Pp.str "can't genc IndRef")
  | ConstructRef _ -> user_err (Pp.str "can't genc ConstructRef")

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

let gen_function (cfunc_name : string) : Pp.t =
  let (ctnt, ty, body) = get_ctnt_type_body_from_cfunc cfunc_name in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  linear_type_check_term body;
  let ty = EConstr.of_constr ty in
  let body = EConstr.of_constr body in
  genc_func env sigma cfunc_name ty body

let brace (pp : Pp.t) : Pp.t =
  hv 2 (str "{" +++ pp ++ brk (1,-2) ++ str "}")

let local_vars : ((string * string) list ref) list ref = ref []

let local_vars_with (f : unit -> 'a) : (string * string) list * 'a =
  let vars = ref [] in
  local_vars := vars :: !local_vars;
  let ret = f () in
  (!vars, ret)

let local_vars_get () =
  !(List.hd !local_vars)

let add_local_var (c_type : string) (c_var : string) : unit =
  if !local_vars = [] then
    user_err (Pp.str "[codegen:bug] add_local_var is called outside of local_vars_with");
  let vars = List.hd !local_vars in
  vars := (c_type, c_var) :: !vars

let id_of_name (name : Name.t Context.binder_annot) : Id.t =
  match Context.binder_name name with
  | Name.Anonymous -> user_err (Pp.str "[codegen:bug] id_of_name require non-anonymous Name")
  | Name.Name id -> id

let carg_of_garg (env : Environ.env) (i : int) : string =
  let x = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
  match x with
  | Name.Anonymous -> user_err (Pp.str "[codegen:bug] carg_of_garg require non-anonymous Name")
  | Name.Name id -> Id.to_string id

exception NeedsMultipleFunctions

type nmf_var = NMFRec | NMFArg | NMFOther (* NMF : Needs Multiple Functions *)

let rec needs_multiple_functions_rec (env : Environ.env) (sigma : Evd.evar_map)
    (top_numargs : int option)
    (top_vars : nmf_var list)
    (outer_recfuncs : bool list)
    (inner_recfuncs : bool list)
    (term : EConstr.t) : unit =
  (*
  let pr_recfuncs recfuncs =
    pp_join_list (Pp.spc ())
      (CList.map_filter_i
        (fun i b ->
          if b then
            let x = Context.Rel.Declaration.get_name (Environ.lookup_rel (i+1) env) in
            let str =
              match x with
              | Name.Anonymous -> "<anon>"
              | Name.Name id -> Id.to_string id
            in
            Some (Pp.str str)
          else
            None)
        recfuncs)
  in
  Feedback.msg_info (Pp.str "needs_multiple_functions_rec:");
  Feedback.msg_info (Pp.str "  top_callable: " ++ Pp.bool top_callable);
  Feedback.msg_info (Pp.str "  top_recfuncs: " ++ hv 0 (pr_recfuncs top_recfuncs));
  Feedback.msg_info (Pp.str "  outer_recfuncs: " ++ hv 0 (pr_recfuncs outer_recfuncs));
  Feedback.msg_info (Pp.str "  inner_recfuncs: " ++ hv 0 (pr_recfuncs inner_recfuncs));
  Feedback.msg_info (Pp.str "  term: " ++ Printer.pr_econstr_env env sigma term);
  *)
  needs_multiple_functions_rec1 env sigma top_numargs top_vars outer_recfuncs inner_recfuncs term
and needs_multiple_functions_rec1 (env : Environ.env) (sigma : Evd.evar_map)
    (top_numargs : int option)
    (top_vars : nmf_var list)
    (outer_recfuncs : bool list)
    (inner_recfuncs : bool list)
    (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Rel i ->
      if List.nth outer_recfuncs (i-1) then
        (match List.nth top_vars (i-1) with
        | NMFRec -> ()
        | NMFArg -> raise NeedsMultipleFunctions
        | NMFOther -> raise NeedsMultipleFunctions)
  | Var _ | Meta _ | Evar _ | Sort _ | Ind _
  | Const _ | Construct _ | Int _ | Float _ | Prod _ -> ()
  | Cast (e,ck,ty) ->
      needs_multiple_functions_rec env sigma top_numargs top_vars outer_recfuncs inner_recfuncs term
  | LetIn (x,e,t,b) ->
      let top_numargs1 = None in
      let top_vars1 = top_vars in
      let outer_recfuncs1 = List.map2 (||) outer_recfuncs inner_recfuncs in
      let inner_recfuncs1 = List.init (List.length outer_recfuncs1) (fun _ -> false) in
      needs_multiple_functions_rec env sigma top_numargs1 top_vars1 outer_recfuncs1 inner_recfuncs1 e;
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let top_numargs2 = None in
      let top_vars2 = NMFOther :: top_vars in
      let outer_recfuncs2 = false :: outer_recfuncs in
      let inner_recfuncs2 = false :: inner_recfuncs in
      needs_multiple_functions_rec env2 sigma top_numargs2 top_vars2 outer_recfuncs2 inner_recfuncs2 b
  | App (f,args) ->
      (* arguments cannot refer functions until downward funarg support *)
      Array.iter
        (fun arg ->
          let i = destRel sigma arg in
          (if List.nth outer_recfuncs (i-1) then raise NeedsMultipleFunctions);
          (if List.nth inner_recfuncs (i-1) then raise NeedsMultipleFunctions))
        args;
      let top_numargs_f =
        match top_numargs with
        | None -> None
        | Some m ->
            let n = Array.length args in
            if Array.map (destRel sigma) args = iota_ary (m-n) n then
              Some (m-n)
            else
              None
      in
      needs_multiple_functions_rec env sigma top_numargs_f top_vars outer_recfuncs inner_recfuncs f
  | Case (ci,predicate,item,branches) ->
      (* match item cannot refer function because its type is inductive type *)
      let top_numargs_branch = None in
      Array.iter
        (needs_multiple_functions_rec env sigma top_numargs_branch top_vars outer_recfuncs inner_recfuncs)
        branches
  | Proj (proj, e) ->
      (* projection item cannot refer function because its type is inductive type *)
      ()
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let (top_numargs_body, top_vars_body) =
        match top_numargs with
        | None -> (None, NMFOther :: top_vars)
        | Some m -> (Some (m+1), NMFArg :: top_vars)
      in
      let outer_recfuncs_body = false :: outer_recfuncs in
      let inner_recfuncs_body = false :: inner_recfuncs in
      needs_multiple_functions_rec env2 sigma top_numargs_body top_vars_body outer_recfuncs_body inner_recfuncs_body b
  | Fix ((ia, i), (nary, tary, fary)) ->
      let prec = (nary, tary, fary) in
      let env2 = push_rec_types prec env in
      let n = Array.length fary in
      let top_numargs_f_ary =
        match top_numargs with
        | None -> Array.make n None
        | Some m -> Array.init n (fun j -> if i = j then Some m else None)
      in
      let top_vars_f =
        let ary = Array.map (fun tn -> if Option.has_some tn then NMFRec else NMFOther) top_numargs_f_ary in
        List.append (CArray.rev_to_list ary) top_vars
      in
      let outer_recfuncs2 = List.append (List.init n (fun _ -> false)) outer_recfuncs in
      let inner_recfuncs2 = List.append (List.init n (fun _ -> true)) inner_recfuncs in
      Array.iteri
        (fun i ->
          (needs_multiple_functions_rec env2 sigma top_numargs_f_ary.(i) top_vars_f outer_recfuncs2 inner_recfuncs2))
        fary
  | CoFix (i, (nary, tary, fary)) ->
      user_err (Pp.str "[codegen] CoFix is not supported")

let needs_multiple_functions (env : Environ.env) (sigma : Evd.evar_map) (body : EConstr.t) : bool =
  try
    needs_multiple_functions_rec env sigma (Some 0) [] [] [] body;
    false
  with NeedsMultipleFunctions -> true

type how_fixfunc_used = {
  mutable how_used_as_call: bool;
  mutable how_used_as_goto: bool;
  mutable how_used_as_closure: bool;
}

type fixfunc_info = {
  fixfunc_c_name: string;
  fixfunc_used_as_call: bool;
  fixfunc_used_as_goto: bool;
  fixfunc_used_as_closure: bool;
  fixfunc_formal_arguments: (string * EConstr.types) list;
}

type fixinfo_t = (Name.t, fixfunc_info) Hashtbl.t

let num_funargs (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : int =
  let t = Retyping.get_type_of env sigma term in
  let t = Reductionops.nf_all env sigma t in
  let (args, result_type) = decompose_prod sigma t in
  List.length args

let fixvar_usage2
    (outer_vars : how_fixfunc_used option list)
    (inner_vars : how_fixfunc_used option list)
    (i : int)
    (outer_func : how_fixfunc_used -> unit)
    (inner_func : how_fixfunc_used -> unit)
    : unit =
  let (b, uopt) =
    try
      (true, List.nth inner_vars (i - 1))
    with Failure _ ->
      (false, List.nth outer_vars (i - 1 - List.length inner_vars))
  in
  match uopt with
  | None -> ()
  | Some u ->
      if b then
        inner_func u
      else
        outer_func u

let fixvar_usage1
    (outer_vars : how_fixfunc_used option list)
    (inner_vars : how_fixfunc_used option list)
    (i : int)
    (func : how_fixfunc_used -> unit)
    : unit =
  fixvar_usage2 outer_vars inner_vars i func func

let rec gensym_fix_vars (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t)
    (outer_vars : how_fixfunc_used option list)
    (inner_vars : how_fixfunc_used option list)
    (term : EConstr.t) (numargs : int) : EConstr.t =
  (*Feedback.msg_debug (Pp.str "[codegen:gensym_fix_vars] start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "numargs=" ++ Pp.int numargs);*)
  gensym_fix_vars1 env sigma fixinfo outer_vars inner_vars term numargs
and gensym_fix_vars1 (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t)
    (outer_vars : how_fixfunc_used option list)
    (inner_vars : how_fixfunc_used option list)
    (term : EConstr.t) (numargs : int) : EConstr.t =
  match EConstr.kind sigma term with
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Rel i ->
      let numargs_in_type = num_funargs env sigma term in
      (if 0 < numargs_in_type then (* non-function is not interesting here *)
        if numargs = numargs_in_type then
          (fixvar_usage2 outer_vars inner_vars i
            (fun u -> u.how_used_as_call <- true)
            (fun u -> u.how_used_as_goto <- true))
        else
          (fixvar_usage1 outer_vars inner_vars i
            (fun u ->
              (*Feedback.msg_debug
                (Pp.str "[codegen:gensym_fix_vars:Rel] u.how_used_as_closure<-true" +++
                Pp.str "numargs=" ++ Pp.int numargs +++
                Pp.str "numargs_in_type=" ++ Pp.int numargs_in_type);*)
              u.how_used_as_closure <- true)));
      term
  | Int _ | Float _ | Const _ | Construct _ -> term
  | Proj (proj, e) ->
      term (* e must be a Rel which type is inductive (non-function) type *)
  | Cast (e,ck,t) -> gensym_fix_vars env sigma fixinfo outer_vars inner_vars e numargs
  | App (f, args) ->
      (Array.iter
        (fun arg ->
          let i = destRel sigma arg in
          (fixvar_usage1 outer_vars inner_vars i
            (fun u ->
              (*Feedback.msg_debug (Pp.str "[codegen:gensym_fix_vars:App] u.how_used_as_closure <- true");*)
              u.how_used_as_closure <- true)))
        args);
      let f' = gensym_fix_vars env sigma fixinfo outer_vars inner_vars f (Array.length args + numargs) in
      mkApp (f', args)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let outer_vars1 = List.append outer_vars inner_vars in
      let inner_vars1 = [] in
      let outer_vars2 = outer_vars in
      let inner_vars2 = None :: inner_vars in
      let e' = gensym_fix_vars env sigma fixinfo outer_vars1 inner_vars1 e 0 in
      let b' = gensym_fix_vars env2 sigma fixinfo outer_vars2 inner_vars2 b numargs in
      mkLetIn (x, e', t, b')
  | Case (ci, p, item, branches) ->
      (* item must be a Rel which type is inductive (non-function) type *)
      let branches' = Array.mapi
        (fun i br ->
          let numargs' = ci.Constr.ci_cstr_nargs.(i) + numargs in
          gensym_fix_vars env sigma fixinfo outer_vars inner_vars br numargs')
        branches in
      mkCase (ci, p, item, branches')
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let outer_vars2 = outer_vars in
      let inner_vars2 = None :: inner_vars in
      let b' = gensym_fix_vars env2 sigma fixinfo outer_vars2 inner_vars2 b (numargs-1) in
      mkLambda (x, t, b')
  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let n = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let outer_vars2 = outer_vars in
      let fixvar_usages = Array.init n (fun i -> {
          how_used_as_call = false;
          how_used_as_goto = false;
          how_used_as_closure = false; }) in
      let inner_vars2 = List.append (CArray.map_to_list (fun u -> Some u) fixvar_usages) inner_vars in
      let fary' = Array.map (fun f -> gensym_fix_vars env2 sigma fixinfo outer_vars2 inner_vars2 f numargs) fary in
      let nary' = Array.init n
        (fun i ->
          let u = fixvar_usages.(i) in
          let gensym_with_name =
            if u.how_used_as_call then
              global_gensym_with_name
            else
              local_gensym_with_name
          in
          let c_name = gensym_with_name (Context.binder_name nary.(i)) in
          let args_and_ret_type = EConstr.decompose_prod sigma tary.(i) in
          let formal_arguments = List.rev_map
            (fun (x,t) ->
              let c_arg = local_gensym_with_annotated_name x in
              (c_arg, t))
            (fst args_and_ret_type)
          in
          let newkey = Name.Name (Id.of_string ("fixfunc" ^ string_of_int (Hashtbl.length fixinfo) ^ "_" ^ c_name)) in
          Hashtbl.add fixinfo newkey {
            fixfunc_c_name = c_name;
            fixfunc_used_as_call = u.how_used_as_call;
            fixfunc_used_as_goto = u.how_used_as_goto;
            fixfunc_used_as_closure = u.how_used_as_closure;
            fixfunc_formal_arguments = formal_arguments;
          };
          (Context.annotR newkey))
      in
      mkFix ((ia, i), (nary', tary, fary'))

let rec rename_top_fix_var (env : Environ.env) (sigma : Evd.evar_map)
    (fixinfo : fixinfo_t)
    (name : string) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let e' = rename_top_fix_var env2 sigma fixinfo name e in
      mkLambda (x,t,e')
  | Fix ((ia, i), (nary, tary, fary)) ->
      let key = Context.binder_name nary.(i) in
      let usage = Hashtbl.find fixinfo key in
      Hashtbl.replace fixinfo key {
        fixfunc_c_name = name;
        fixfunc_used_as_call = true;
        fixfunc_used_as_goto = usage.fixfunc_used_as_goto;
        fixfunc_used_as_closure = usage.fixfunc_used_as_closure;
        fixfunc_formal_arguments = usage.fixfunc_formal_arguments;
      };
      mkFix ((ia, i), (nary, tary, fary))
  (* xxx: consider App *)
  | _ -> term

let rename_fix_var (env : Environ.env) (sigma : Evd.evar_map) (name : string) (term : EConstr.t) : (EConstr.t * fixinfo_t) =
  let fixinfo = Hashtbl.create 0 in
  let numargs = num_funargs env sigma term in
  let term2 = gensym_fix_vars env sigma fixinfo [] [] term numargs in
  let term3 = rename_top_fix_var env sigma fixinfo name term2 in
  (term3, fixinfo)

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
        let c_var = local_gensym_with_annotated_name x in
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
  let ass = Array.to_list assignments in
  let ass = List.filter (fun (lhs, rhs, ty) -> lhs <> rhs) ass in
  let rpp = ref (mt ()) in
  (* better algorithm using topological sort? *)
  let rec loop ass =
    match ass with
    | [] -> ()
    | a :: rest ->
        let rhs_list = List.map (fun (lhs, rhs, ty) -> rhs) ass in
        let blocked_ass, nonblocked_ass =
          List.partition (fun (lhs, rhs, ty) -> List.mem lhs rhs_list) ass
        in
        if nonblocked_ass <> [] then
          (List.iter
            (fun (lhs, rhs, ty) ->
              let pp = genc_assign (str lhs) (str rhs) in
              rpp := !rpp +++ pp)
            nonblocked_ass;
          loop blocked_ass)
        else
          (let (a_lhs, a_rhs, a_ty) = a in
          let tmp = local_gensym () in
          add_local_var (c_typename env sigma a_ty) tmp;
          let pp = genc_assign (str tmp) (str a_lhs) in
          (rpp := !rpp +++ pp);
          let ass2 = List.map
            (fun (lhs, rhs, ty) ->
              if rhs = a_lhs then (lhs, tmp, ty) else (lhs, rhs, ty))
            ass
          in
          loop ass2)
  in
  loop ass;
  !rpp

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
        let uopt = Hashtbl.find_opt fixinfo key in
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
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_tail fixinfo gen_ret env2 sigma b rest)
  | Case (ci,predicate,item,branches) ->
      gen_match gen_switch_without_break (gen_tail fixinfo gen_ret) env sigma ci predicate item branches cargs
  | LetIn (x,e,t,b) ->
      let c_var = local_gensym_with_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      gen_assign fixinfo c_var env sigma e [] +++
      gen_tail fixinfo gen_ret env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ui = Hashtbl.find fixinfo (Context.binder_name nary.(i)) in
      let ni_formal_arguments = ui.fixfunc_formal_arguments in
      if List.length cargs < List.length ni_formal_arguments then
        user_err (Pp.str "[codegen] gen_tail: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) ni_formal_arguments cargs in
      let pp_assignments = gen_parallel_assignment env sigma (Array.of_list assginments) in
      let ni_funcname = ui.fixfunc_c_name in
      let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str ("entry_" ^ ni_funcname) ++ Pp.str ";") in
      let pp_bodies =
        Array.mapi
          (fun j nj ->
            let fj = fary.(j) in
            let uj = Hashtbl.find fixinfo (Context.binder_name nj) in
            let nj_formal_arguments = uj.fixfunc_formal_arguments in
            List.iter
              (fun (c_arg, t) -> add_local_var (c_typename env sigma t) c_arg)
              nj_formal_arguments;
            let nj_formal_argvars = List.map fst nj_formal_arguments in
            let nj_funcname = uj.fixfunc_c_name in
            let pp_label = Pp.str ("entry_" ^ nj_funcname) in
            hv 0 (pp_label ++ Pp.str ":" +++ gen_tail fixinfo gen_ret env2 sigma fj nj_formal_argvars))
          nary in
      pp_assignments +++ pp_goto_entry +++ pp_join_ary (Pp.spc ()) pp_bodies

  | Proj _ -> user_err (Pp.str "gen_tail: unsupported term Proj:" +++ Printer.pr_econstr_env env sigma term)
and gen_assign (fixinfo : fixinfo_t) (ret_var : string) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  let pp = gen_assign1 fixinfo ret_var env sigma term cargs in
  (*Feedback.msg_debug (Pp.str "gen_assign:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_assign1 (fixinfo : fixinfo_t) (ret_var : string) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _
  | Cast _ | CoFix _ ->
      user_err (str "[codegen:gen_assign] unsupported term (" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        genc_assign (Pp.str ret_var) (Pp.str str)
      else
        user_err (Pp.str "[codegen:gen_assign] fix/closure call not supported yet")
  | Const (ctnt,_) ->
      genc_assign (Pp.str ret_var) (gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list cargs))
  | Construct (cstr,_) ->
      genc_assign (Pp.str ret_var) (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list cargs))
  | App (f,args) ->
      let cargs2 =
        List.append
          (Array.to_list (Array.map (fun arg -> carg_of_garg env (destRel sigma arg)) args))
          cargs
      in
      gen_assign1 fixinfo ret_var env sigma f cargs2
  | Case (ci,predicate,item,branches) ->
      gen_match gen_switch_with_break (gen_assign fixinfo ret_var) env sigma ci predicate item branches cargs

  | LetIn (x,e,t,b) ->
      let c_var = local_gensym_with_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      gen_assign fixinfo c_var env sigma e [] +++
      gen_assign fixinfo ret_var env2 sigma b cargs

  | Fix ((ia, i), ((nary, tary, fary) as prec)) ->
      if Array.exists
           (fun n ->
             let ui = Hashtbl.find fixinfo (Context.binder_name n) in
             ui.fixfunc_used_as_call || ui.fixfunc_used_as_closure)
           nary
      then
        (let msg = ref (Pp.mt ()) in
          msg := !msg +++ Pp.hov 0 (Pp.str "[codegen] gen_assign: fix term not purely tail recursive:") +++
                          Pp.hv 0 (Printer.pr_econstr_env env sigma term);
         Array.iter
           (fun n ->
             let ui = Hashtbl.find fixinfo (Context.binder_name n) in
             if ui.fixfunc_used_as_call then
               msg := !msg +++ Pp.hov 0 (Pp.str "recursive function," +++ Pp.str ui.fixfunc_c_name ++ Pp.str ", is used as a call");
             if ui.fixfunc_used_as_closure then
               msg := !msg +++ Pp.hov 0 (Pp.str "recursive function," +++ Pp.str ui.fixfunc_c_name ++ Pp.str ", is used as a closure"))
           nary;
          user_err (Pp.hv 0 !msg));
      let env2 = EConstr.push_rec_types prec env in
      let ui = Hashtbl.find fixinfo (Context.binder_name nary.(i)) in
      let ni_formal_arguments = ui.fixfunc_formal_arguments in
      if List.length cargs < List.length ni_formal_arguments then
        user_err (Pp.str "[codegen] gen_assign: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) ni_formal_arguments cargs in
      let pp_assignments = gen_parallel_assignment env sigma (Array.of_list assginments) in
      let ni_funcname = ui.fixfunc_c_name in
      let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str ("entry_" ^ ni_funcname) ++ Pp.str ";") in
      let exit_label = "exit_" ^ ni_funcname in
      let pp_exit = Pp.hov 0 (Pp.str exit_label ++ Pp.str ":;") in
      let pp_bodies =
        Array.mapi
          (fun j nj ->
            let fj = fary.(j) in
            let uj = Hashtbl.find fixinfo (Context.binder_name nj) in
            let nj_formal_arguments = uj.fixfunc_formal_arguments in
            List.iter
              (fun (c_arg, t) -> add_local_var (c_typename env sigma t) c_arg)
              nj_formal_arguments;
            let nj_formal_argvars = List.map fst nj_formal_arguments in
            let nj_funcname = uj.fixfunc_c_name in
            let pp_label = Pp.str ("entry_" ^ nj_funcname) in
            let gen_ret arg = genc_assign (Pp.str ret_var) arg +++ Pp.hov 0 (Pp.str "goto" +++ Pp.str exit_label ++ Pp.str ";") in
            hv 0 (pp_label ++ Pp.str ":" +++ gen_tail fixinfo gen_ret env2 sigma fj nj_formal_argvars))
          nary in
      pp_assignments +++ pp_goto_entry +++ pp_join_ary (Pp.spc ()) pp_bodies +++ pp_exit

  | Proj _
  | Lambda _ ->
      user_err (str "[codegen:gen_assign] not impelemented (" ++ str (constr_name sigma term) ++ str "): " ++ Printer.pr_econstr_env env sigma term)

let gen_func2_sub (cfunc_name : string) : Pp.t =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (ctnt, ty, body) = get_ctnt_type_body_from_cfunc cfunc_name in
  let body = EConstr.of_constr body in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:1");*)
  (if needs_multiple_functions env sigma body then user_err (Pp.str "[codegen not supported yet] needs multiple function:" +++ Pp.str cfunc_name));
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:2");*)
  let (body, fixinfo) = rename_fix_var env sigma cfunc_name body in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:3");*)
  let ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (argument_name_type_pairs, return_type) = decompose_prod sigma ty in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:4");*)
  let c_fargs = List.rev_map
    (fun (x,t) -> (local_gensym_with_annotated_name x, t))
    argument_name_type_pairs
  in
  (*Feedback.msg_debug (Pp.str "gen_func2_sub:5");*)
  let (vars, pp_body) = local_vars_with (fun () -> hv 0 (gen_tail fixinfo genc_return env sigma body (List.map fst c_fargs))) in
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
        (local_vars_get ()))
    ++
    pp_body))

let gen_function2 (cfunc_name : string) : Pp.t =
  local_gensym_with (fun () -> gen_func2_sub cfunc_name)

let gen_function0 (cfunc_name : string) : Pp.t =
  if !opt_codegen_dev then
    gen_function2 cfunc_name
  else
    gen_function cfunc_name

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

let genc (libref_list : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  List.iter
    (fun libref ->
      let (ctnt, ty, body) = get_ctnt_type_body env libref in
      linear_type_check_term body;
      let fname = Label.to_string (KerName.label (Constant.canonical ctnt)) in
      let ty = EConstr.of_constr ty in
      let body = EConstr.of_constr body in
      let pp = genc_func env sigma fname ty body in
      Feedback.msg_info pp)
    libref_list

let genc_file (fn : string) (libref_list : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (let (temp_fn, ch) = Filename.open_temp_file
    ~perms:0o666 ~temp_dir:(Filename.dirname fn) (Filename.basename fn) ".c" in
  let fmt = Format.formatter_of_out_channel ch in
  List.iter
    (fun libref ->
      let (ctnt, ty, body) = get_ctnt_type_body env libref in
      linear_type_check_term body;
      let fname = Label.to_string (KerName.label (Constant.canonical ctnt)) in
      let ty = EConstr.of_constr ty in
      let body = EConstr.of_constr body in
      let pp = genc_func env sigma fname ty body in
      Pp.pp_with fmt (pp ++ Pp.fnl ()))
    libref_list;
  Format.pp_print_flush fmt ();
  close_out ch;
  Sys.rename temp_fn fn;
  Feedback.msg_info (str ("file generated: " ^ fn)))
