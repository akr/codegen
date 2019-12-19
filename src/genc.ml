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
open Globnames
open Pp
open CErrors

open Cgenutil
open State
open Linear

let c_funcname (fname : string) : string =
  c_id fname

let goto_label (fname : string) : string =
  "entry_" ^ (c_id fname)

let c_typename (ty : Constr.types) : string =
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg -> ind_cfg.c_type
  | None -> c_id (mangle_type ty)

let c_cstrname (ty : Constr.types) (cstru : Constr.pconstructor) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let ((mutind, i), j) = Univ.out_punivs cstru in
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.cstr_configs.(j-1).c_cstr with
      | Some c_cstr -> c_cstr
      | None -> user_err (
        Pp.str "inductive constructor not configured:" ++ Pp.spc () ++
        Id.print ind_cfg.cstr_configs.(j-1).coq_cstr ++ Pp.spc () ++
        Pp.str "for" ++ Pp.spc () ++
        Printer.pr_constr_env env sigma ind_cfg.coq_type))
  | None ->
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.Declarations.mind_packets.(i) in
      let cons_id = oind_body.Declarations.mind_consnames.(j-1) in
      let fname = Id.to_string cons_id in
      c_funcname fname

let case_swfunc (ty : Constr.types) : string =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.c_swfunc with
      | Some c_swfunc -> c_swfunc
      | None -> user_err (
        Pp.str "inductive match configuration not registered:" ++ Pp.spc () ++
        Printer.pr_lconstr_env env sigma ind_cfg.coq_type))
  | None -> c_id ("sw_" ^ (mangle_type ty))

let case_cstrlabel (ty : Constr.types) (j : int) =
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.c_swfunc with
      | Some _ -> ind_cfg.cstr_configs.(j-1).c_caselabel
      | None -> raise (CodeGenError "inductive match configuration not registered")) (* should be called after case_swfunc *)
  | None ->
      let env = Global.env () in
      let indty =
        match Constr.kind ty with
        | Constr.App (f, argsary) -> f
        | _ -> ty
      in
      let (mutind, i) = Univ.out_punivs (Constr.destInd indty) in
      let mutind_body = Environ.lookup_mind mutind env in
      let oneind_body = mutind_body.Declarations.mind_packets.(i) in
      let consname = Id.to_string oneind_body.Declarations.mind_consnames.(j-1) in
      c_id ("case_" ^ consname ^ "_" ^ (mangle_type ty))

let case_cstrfield (ty : Constr.types) (j : int) (k : int) : string =
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.c_swfunc with
      | Some _ -> ind_cfg.cstr_configs.(j-1).c_accessors.(k)
      | None -> raise (CodeGenError "inductive match configuration not registered")) (* should be called after case_swfunc *)
  | None ->
      let env = Global.env () in
      let indty =
        match Constr.kind ty with
        | Constr.App (f, argsary) -> f
        | _ -> ty
      in
      let (mutind, i) = Univ.out_punivs (Constr.destInd indty) in
      let mutind_body = Environ.lookup_mind mutind env in
      let oneind_body = mutind_body.Declarations.mind_packets.(i) in
      let consname = Id.to_string oneind_body.Declarations.mind_consnames.(j-1) in
      c_id ("field" ^ string_of_int k ^ "_" ^ consname ^ "_" ^ (mangle_type ty))

let gensym () : string =
  let n = !gensym_id in
  gensym_id := n + 1;
  "g" ^ string_of_int n

let gensym_with_str (suffix : string) : string =
  gensym () ^ "_" ^ (c_id suffix)

let gensym_with_name (name : Name.t) : string =
  match name with
  | Names.Name.Anonymous -> gensym ()
  | Names.Name.Name id -> gensym () ^ "_" ^ (c_id (Id.to_string id))

let gensym_with_nameopt (nameopt : Name.t option) : string =
  match nameopt with
  | None -> gensym ()
  | Some name -> gensym_with_name name

let local_gensym_id : (int ref) list ref = ref []

let  local_gensym_with (f : unit -> 'a) : 'a =
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

let local_gensym_with_nameopt (nameopt : Name.t option) : string =
  match nameopt with
  | None -> local_gensym ()
  | Some name -> local_gensym_with_name name

let rec argtys_and_rety_of_type (ty : Constr.types) : Constr.types list * Constr.types =
  match Constr.kind ty with
  | Constr.Prod (name, ty', body) ->
      let (argtys, rety) = argtys_and_rety_of_type body in
      (ty :: argtys, rety)
  | _ -> ([], ty)

let rec nargtys_and_rety_of_type (n : int) (ty : Constr.types) : Constr.types list * Constr.types =
  if n == 0 then
    ([], ty)
  else
    match Constr.kind ty with
    | Constr.Prod (name, ty', body) ->
        let (argtys, rety) = nargtys_and_rety_of_type (n-1) body in
        (ty :: argtys, rety)
    | _ -> user_err (Pp.str "too few prods in type")

type context_elt =
  | CtxVar of string
  | CtxRec of
      string *
      (string * Constr.types) array (* fname, argname_argtype_array *)

let rec fargs_and_body (env : Environ.env) (term : Constr.t) : (string * Constr.types) list * Environ.env * Constr.t =
  match Constr.kind term with
  | Constr.Lambda (name, ty, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = Environ.push_rel decl env in
      let var = local_gensym_with_name (Context.binder_name name) in
      let fargs1, env1, body1 = fargs_and_body env2 body in
      let fargs2 = (var, ty) :: fargs1 in
      (fargs2, env1, body1)
  | _ -> ([], env, term)

let fargs_and_body_ary (env : Environ.env)
    (strnameary : string array) (ty : Constr.types)
    (ia : int array) (i : int)
    (nameary : Name.t array)
    (tyary : Constr.types array)
    (funary : Constr.t array) :
    (string *
     Constr.types *
     (string * Constr.types) list *
     context_elt list *
     Environ.env *
     Constr.t) array =
  let fb_ary = Array.map (fun term1 -> fargs_and_body env term1) funary in
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

let genc_farg (farg : string * Constr.types) : Pp.t =
  let (var, ty) = farg in
  hv 2 (str (c_typename ty) ++ spc () ++ str var)

let genc_fargs (fargs : (string * Constr.types) list) : Pp.t =
  match fargs with
  | [] -> str "void"
  | farg1 :: rest ->
      List.fold_left
        (fun pp farg -> pp ++ str "," ++ spc () ++ genc_farg farg)
        (genc_farg farg1)
        rest

let genc_vardecl (ty : Constr.types) (varname : string) : Pp.t =
  hv 0 (str (c_typename ty) ++ spc () ++ str varname ++ str ";")

let genc_varinit (ty : Constr.types) (varname : string) (init : Pp.t) : Pp.t =
  hv 0 (str (c_typename ty) ++ spc () ++ str varname ++ spc () ++ str "=" ++ spc () ++ init ++ str ";")

let genc_assign (lhs : Pp.t) (rhs : Pp.t) : Pp.t =
  hv 0 (lhs ++ spc () ++ str "=" ++ spc () ++ rhs ++ str ";")

let genc_return (arg : Pp.t) : Pp.t =
  hv 0 (str "return" ++ spc () ++ arg ++ str ";")

let genc_void_return (retvar : string) (arg : Pp.t) : Pp.t =
  hv 0 (genc_assign (str retvar) arg ++ spc () ++ str "return;")

let varname_of_rel (context : context_elt list) (i : int) : string =
  match List.nth context (i-1) with
  | CtxVar varname -> varname
  | _ -> raise (Invalid_argument "unexpected context element")

let genc_app (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (f : Constr.t) (argsary : Constr.t array) : Pp.t =
  match Constr.kind f with
  | Constr.Rel i ->
      (match List.nth context (i-1) with
      | CtxVar _ -> user_err (str "indirect call not implemented")
      | CtxRec (fname, _) ->
          let argvars = Array.map (fun arg -> varname_of_rel context (Constr.destRel arg)) argsary in
          let c_fname = c_funcname fname in
          str c_fname ++ str "(" ++
          pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
          str ")")
  | Constr.Const ctntu ->
      let fname = Label.to_string (KerName.label (Constant.canonical (Univ.out_punivs ctntu))) in
      let c_fname = c_funcname fname in
      let argvars = Array.map (fun arg -> varname_of_rel context (Constr.destRel arg)) argsary in
      str c_fname ++ str "(" ++
      pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
      str ")"
  | Constr.Construct cstru ->
      let ty = EConstr.to_constr sigma (Reductionops.nf_all env sigma (Retyping.get_type_of env sigma (EConstr.of_constr (Constr.mkApp (f, argsary))))) in
      (*Feedback.msg_info (Printer.pr_constr_env env sigma ty);*)
      let fname_argn = c_cstrname ty cstru in
      let argvars = Array.map (fun arg -> varname_of_rel context (Constr.destRel arg)) argsary in
      if Array.length argvars = 0 then
        str fname_argn
      else
        str fname_argn ++ str "(" ++
        pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
        str ")"
  | _ -> assert false

let genc_multi_assign (assignments : (string * (string * Constr.types)) array) : Pp.t =
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
              if Pp.ismt !rpp then rpp := pp else rpp := !rpp ++ spc () ++ pp)
            nonblocked_ass;
          loop blocked_ass)
        else
          (let a_lhs, (a_rhs, a_ty) = a in
          let tmp = local_gensym () in
          let pp = genc_varinit a_ty tmp (str a_lhs) in
          (if Pp.ismt !rpp then rpp := pp else rpp := !rpp ++ spc () ++ pp);
          let ass2 = List.map
            (fun (lhs, (rhs, ty)) ->
              if rhs = a_lhs then (lhs, (tmp, ty)) else (lhs, (rhs, ty)))
            ass
          in
          loop ass2)
  in
  loop ass;
  !rpp

let genc_goto (context : context_elt list) (ctxrec : string * (string * Constr.types) array) (argsary : Constr.t array) : Pp.t =
  let fname, argvars = ctxrec in
  (if Array.length argsary <> Array.length argvars then
    user_err (str "partial function invocation not supported yet");
  let fname_argn = goto_label fname in
  let assignments =
    (array_map2
      (fun (var, ty) arg -> (var, (varname_of_rel context (Constr.destRel arg), ty)))
      argvars argsary)
  in
  let pp_assigns = genc_multi_assign assignments in
  let pp_goto = (hv 0 (str "goto" ++ spc () ++ str fname_argn ++ str ";")) in
  if Pp.ismt pp_assigns then pp_goto else pp_assigns ++ spc () ++ pp_goto)

let genc_const (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (ctntu : Constr.pconstant) : Pp.t =
  genc_app env sigma context (Constr.mkConstU ctntu) [| |]

let genc_construct (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (cstru : Constr.pconstructor) : Pp.t =
  genc_app env sigma context (Constr.mkConstructU cstru) [| |]

let split_case_tyf (tyf : Constr.t) : Constr.types * Constr.t =
  match Constr.kind tyf with
  | Constr.Lambda (name, ty, body) -> (ty, body)
  | _ -> user_err (str "unexpected case type function")

let rec strip_outer_lambdas (ndecls : int) (term : Constr.t) : (Names.Name.t Context.binder_annot * Constr.types) list * Constr.t =
  if ndecls = 0 then
    ([], term)
  else
    match Constr.kind term with
    | Constr.Lambda (name, ty, body) ->
        let (decls, innermostbody) = strip_outer_lambdas (ndecls-1) body in
        ((name, ty) :: decls, innermostbody)
    | _ -> user_err (str "case body lambda nesting is not enough")

let genc_case_branch_body (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> Constr.constr -> Pp.t)
    (exprty : Constr.types) (exprvar : string) (ndecls : int)
    (br : Constr.t) (cstr_index : int) : Pp.t =
  let (decls, body) = strip_outer_lambdas ndecls br in
  let decls2 =
    List.map2
      (fun (name, ty) field_index ->
        let name = Context.binder_name name in
        let varname = local_gensym_with_name name in
        let cstr_field = case_cstrfield exprty cstr_index field_index in
        (CtxVar varname, genc_varinit ty varname (str cstr_field ++ str "(" ++ str exprvar ++ str ")")))
       decls
      (iota_list 0 (List.length decls))
  in
  let context2 = List.rev_append (List.map fst decls2) context in
  let decls3 = List.map snd decls2 in
  pp_postjoin_list (spc ()) decls3 ++ bodyfunc env sigma context2 body

let genc_case_branch (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> Constr.constr -> Pp.t)
    (exprty : Constr.types) (exprvar : string) (ndecls : int)
    (br : Constr.t) (cstr_index : int) : Pp.t =
  let cstr_label = case_cstrlabel exprty cstr_index in
  let pp_label = str cstr_label ++ str ":" in
  hv 0 (hv 0 (pp_label ++ spc () ++ str "{") ++ brk (1,2) ++
    hv 0 (genc_case_branch_body env sigma context bodyfunc exprty exprvar ndecls br cstr_index) ++ spc () ++
    str "}")

let genc_case_nobreak (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list) (ci : Constr.case_info) (tyf : Constr.t)
    (expr : Constr.t) (brs : Constr.t array)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> Constr.constr -> Pp.t) : Pp.t =
  let (exprty, rety) = split_case_tyf tyf in
  let exprvar = varname_of_rel context (Constr.destRel expr) in
  if Array.length brs = 1 then
    let ndecls = ci.Constr.ci_cstr_ndecls.(0) in
    let br = brs.(0) in
    let cstr_index = 1 in
    genc_case_branch_body env sigma context bodyfunc exprty exprvar ndecls br cstr_index
  else
    let swfunc = case_swfunc exprty in
    let swexpr = if swfunc = "" then str exprvar else str swfunc ++ str "(" ++ str exprvar ++ str ")" in
    hv 0 (
    hv 0 (str "switch" ++ spc () ++ str "(" ++ swexpr ++ str ")") ++ spc () ++
    str "{" ++ brk (1,2) ++
    hv 0 (
    pp_join_ary (spc ())
      (array_map3
        (genc_case_branch env sigma context bodyfunc exprty exprvar)
        ci.Constr.ci_cstr_ndecls
        brs
        (iota_ary 1 (Array.length brs)))) ++
    spc () ++ str "}")

let genc_case_break (env : Environ.env) (sigma : Evd.evar_map)
    (context : context_elt list) (ci : Constr.case_info) (tyf : Constr.t)
    (expr : Constr.t) (brs : Constr.t array)
    (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> Constr.constr -> Pp.t) : Pp.t =
  genc_case_nobreak env sigma context ci tyf expr brs
    (fun envb sigma context2 body -> bodyfunc envb sigma context2 body ++ spc () ++ str "break;")

let genc_geninitvar (ty : Constr.types) (namehint : Names.Name.t) (init : Pp.t) : Pp.t * string =
  let varname = local_gensym_with_name namehint in
  (genc_varinit ty varname init, varname)

(* not tail position. return a variable *)
let rec genc_body_var (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (namehint : Names.Name.t) (term : Constr.t) (termty : Constr.types) : Pp.t * string =
  match Constr.kind term with
  | Constr.Rel i ->
      (mt (), varname_of_rel context i)
  | Constr.LetIn (name, expr, exprty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
      let name = Context.binder_name name in
      let env2 = Environ.push_rel decl env in
      let (exprbody, exprvarname) = genc_body_var env sigma context name expr exprty in
      let (bodybody, bodyvarname) = genc_body_var env2 sigma (CtxVar exprvarname :: context) namehint body termty in
      (exprbody ++ (if ismt exprbody then mt () else spc ()) ++ bodybody, bodyvarname)
  | Constr.App (f, argsary) ->
      genc_geninitvar termty namehint (genc_app env sigma context f argsary)
  | Constr.Case (ci, tyf, expr, brs) ->
      let varname = local_gensym_with_name namehint in
      (genc_vardecl termty varname ++ spc () ++
       genc_case_break env sigma context ci tyf expr brs
        (fun envb sigma context2 body -> genc_body_assign envb sigma context2 varname body),
      varname)
  | Constr.Const ctntu ->
      genc_geninitvar termty namehint (genc_const env sigma context ctntu)
  | Constr.Construct cstru ->
      genc_geninitvar termty namehint (genc_construct env sigma context cstru)
  | _ -> (user_err (str "not impelemented (genc_body_var:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

(* not tail position. assign to the specified variable *)
and genc_body_assign (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (retvar : string) (term : Constr.t) : Pp.t =
  match Constr.kind term with
  | Constr.Rel i ->
      genc_assign (str retvar) (str (varname_of_rel context i))
  | Constr.LetIn (name, expr, exprty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
      let name = Context.binder_name name in
      let env2 = Environ.push_rel decl env in
      let (exprbody, varname) = genc_body_var env sigma context name expr exprty in
      exprbody ++
      (if ismt exprbody then mt () else spc ()) ++
      genc_body_assign env2 sigma (CtxVar varname :: context) retvar body
  | Constr.App (f, argsary) ->
      genc_assign (str retvar) (genc_app env sigma context f argsary)
  | Constr.Case (ci, tyf, expr, brs) ->
      genc_case_break env sigma context ci tyf expr brs
        (fun envb sigma context2 body -> genc_body_assign envb sigma context2 retvar body)
  | Constr.Const ctntu ->
      genc_assign (str retvar) (genc_const env sigma context ctntu)
  | Constr.Construct cstru ->
      genc_assign (str retvar) (genc_construct env sigma context cstru)
  | _ -> (user_err (str "not impelemented (genc_body_assign:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

(* tail position.  usual return. *)
let rec genc_body_tail (env : Environ.env) (sigma : Evd.evar_map) (context : context_elt list) (term : Constr.t) : Pp.t =
  match Constr.kind term with
  | Constr.Rel i ->
      genc_return (str (varname_of_rel context i))
  | Constr.LetIn (name, expr, exprty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
      let name = Context.binder_name name in
      let env2 = Environ.push_rel decl env in
      let (exprbody, varname) = genc_body_var env sigma context name expr exprty in
      exprbody ++
      (if ismt exprbody then mt () else spc ()) ++
      genc_body_tail env2 sigma (CtxVar varname :: context) body
  | Constr.App (f, argsary) ->
      (match Constr.kind f with
      | Constr.Rel i ->
          (match List.nth context (i-1) with
          | CtxRec (fname, argvars) -> genc_goto context (fname, argvars) argsary
          | _ -> genc_return (genc_app env sigma context f argsary))
      | _ -> genc_return (genc_app env sigma context f argsary))
  | Constr.Case (ci, tyf, expr, brs) ->
      genc_case_nobreak env sigma context ci tyf expr brs genc_body_tail
  | Constr.Const ctntu ->
      genc_return (genc_const env sigma context ctntu)
  | Constr.Construct cstru ->
      genc_return (genc_construct env sigma context cstru)
  | _ -> (user_err (str "not impelemented (genc_body_tail:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

(* tail position.  assign and return. *)
let rec genc_mufun_body_tail (env : Environ.env) (sigma : Evd.evar_map) (retvar : string) (context : context_elt list) (term : Constr.t) : Pp.t =
  match Constr.kind term with
  | Constr.Rel i ->
      genc_void_return retvar (str (varname_of_rel context i))
  | Constr.LetIn (name, expr, exprty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, exprty) in
      let name = Context.binder_name name in
      let env2 = Environ.push_rel decl env in
      let (exprbody, varname) = genc_body_var env sigma context name expr exprty in
      exprbody ++
      (if ismt exprbody then mt () else spc ()) ++
      genc_mufun_body_tail env2 sigma retvar (CtxVar varname :: context) body
  | Constr.App (f, argsary) ->
      (match Constr.kind f with
      | Constr.Rel i ->
          (match List.nth context (i-1) with
          | CtxRec (fname, argvars) -> genc_goto context (fname, argvars) argsary
          | _ -> genc_void_return retvar (genc_app env sigma context f argsary))
      | _ -> genc_void_return retvar (genc_app env sigma context f argsary))
  | Constr.Case (ci, tyf, expr, brs) ->
      genc_case_nobreak env sigma context ci tyf expr brs
        (fun envb sigma -> genc_mufun_body_tail envb sigma retvar)
  | Constr.Const ctntu ->
      genc_void_return retvar (genc_const env sigma context ctntu)
  | Constr.Construct cstru ->
      genc_void_return retvar (genc_construct env sigma context cstru)
  | _ -> (user_err (str "not impelemented (genc_mufun_body_tail:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

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

let rec scan_callsites_rec (env : Environ.env) (sigma : Evd.evar_map) (tail : bool) (context : (int * bool ref * bool ref * bool ref) option list) (term : Constr.t) : unit =
  match Constr.kind term with
  | Constr.Const ctntu -> ()
  | Constr.Construct cstru -> ()
  | Constr.Rel i ->
      found_funref context i
  | Constr.Cast (expr, kind, ty) ->
      scan_callsites_rec env sigma false context expr
  | Constr.LetIn (name, expr, ty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = Environ.push_rel decl env in
      (scan_callsites_rec env sigma false context expr;
      scan_callsites_rec env2 sigma tail (None :: context) body)
  | Constr.App (f, argsary) ->
      ((match Constr.kind f with
      | Constr.Rel i -> found_callsite tail context i (Array.length argsary)
      | _ -> scan_callsites_rec env sigma false context f);
      Array.iter (scan_callsites_rec env sigma false context) argsary)
  | Constr.Case (ci, tyf, expr, brs) ->
      (scan_callsites_rec env sigma false context expr;
      array_iter2
        (fun nargs br ->
          let context2 = ncons nargs None context in
          let (decls, br2) = strip_outer_lambdas nargs br in
          let env2 = Environ.push_rel_context
            (List.map
              (fun (name, ty) -> Context.Rel.Declaration.LocalAssum (name, ty))
              (List.rev decls))
            env in
          scan_callsites_rec env2 sigma tail context2 br2)
        ci.Constr.ci_cstr_nargs brs)
  | Constr.Proj (proj, expr) ->
      scan_callsites_rec env sigma false context expr
  | _ -> user_err ~hdr:"scan_callsites_rec" (hv 0 (str "unexpected term:" ++ spc () ++ Printer.pr_constr_env env sigma term))

let scan_callsites (sigma : Evd.evar_map) (i : int)
    (ntfcb_ary : (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array) :
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
      | None -> assert false)
    (array_rev (Array.of_list context))

let genc_func_single (env : Environ.env) (sigma : Evd.evar_map)
    (fname : string) (ty : Constr.types)
    (fargs : (string * Constr.types) list)
    (context : context_elt list) (body : Constr.t) : Pp.t =
  (*let (ty, fargs, context, body) = fargs_and_body fname term in*)
  let (argtys, rety) = argtys_and_rety_of_type ty in
  (if List.length argtys <> List.length fargs then
    user_err (str ("function value not supported yet: " ^
      string_of_int (List.length argtys) ^ " prods and " ^
      string_of_int (List.length fargs) ^ " lambdas")));
  let c_fname = c_funcname fname in
  hv 0 (
  str "static" ++ spc () ++
  str (c_typename rety) ++ spc () ++
  str c_fname ++ str "(" ++
  hv 0 (genc_fargs fargs) ++
  str ")" ++ spc () ++
  str "{" ++ brk (1,2) ++
  hv 0 (
    genc_body_tail env sigma context body) ++
  spc () ++ str "}")

let find_headcalls
    (ntfcb_ary : (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array)
    (callsites_ary : (bool * bool * bool) array) :
    (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array =
  Array.concat
    (Array.to_list
      (array_map2
        (fun ntfcb (headcall, tailcall, partcall) ->
          if headcall then [| ntfcb |] else [| |])
        ntfcb_ary callsites_ary))

let genc_mufun_struct_one (ntfcb : string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) : Pp.t =
  let nm, ty, fargs, context, envb, body = ntfcb in
  hv 0 (
  str "struct" ++ spc () ++
  str nm ++ spc () ++
  str "{" ++ spc () ++
  pp_postjoin_list (str ";" ++ spc ()) (List.map genc_farg fargs) ++
  str "};")

let genc_mufun_structs
    (ntfcb_ary : (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.map genc_mufun_struct_one ntfcb_ary2)

let genc_mufun_entry (mfnm : string) (i : int) (ntfcb : string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) : Pp.t =
  let nm, ty, fargs, context, envb, body = ntfcb in
  let (argtys, rety) = nargtys_and_rety_of_type (List.length fargs) ty in
  let c_fname = c_funcname nm in
  hv 0 (
  str "static" ++ spc () ++
  str (c_typename rety) ++ spc () ++
  str c_fname ++ str "(" ++
  hv 0 (genc_fargs fargs) ++
  str ")" ++ spc () ++
  str "{" ++ brk (1,2) ++
  hv 0 (
    hv 0 (str "struct" ++ spc () ++ str nm ++ spc () ++ str "args" ++ spc () ++
      str "=" ++ spc () ++ str "{" ++ spc () ++
      pp_join_list (str "," ++ spc ())
        (List.map
          (fun (var, ty) -> hv 0 (str var))
        fargs) ++ spc () ++ str "};") ++ spc () ++
    hv 0 (str (c_typename rety) ++ spc () ++ str "ret;") ++ spc () ++
    hv 0 (str mfnm ++ str "(" ++ int i ++ str "," ++ spc () ++ str "&args," ++ spc () ++ str "&ret);") ++ spc () ++
    hv 0 (str "return" ++ spc () ++ str "ret;")) ++
  spc () ++ str "}")

let genc_mufun_entries (mfnm : string)
    (ntfcb_ary : (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.mapi (genc_mufun_entry mfnm) ntfcb_ary2)

let genc_mufun_forward_decl (mfnm : string) : Pp.t =
  hv 0 (
  str "static" ++ spc () ++
  str "void" ++ spc () ++
  str mfnm ++ str "(" ++
  hv 0 (
    hv 0 (str "int" ++ spc () ++ str "i") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "argsp") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "retp")) ++ str ");")

let genc_mufun_bodies_func (sigma :Evd.evar_map) (mfnm : string) (i : int)
    (ntfcb_ary : (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  hv 0 (
  str "static" ++ spc () ++
  str "void" ++ spc () ++
  str mfnm ++ str "(" ++
  hv 0 (
    hv 0 (str "int" ++ spc () ++ str "i") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "argsp") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "retp")) ++ str ")" ++ spc () ++
  str "{" ++ brk (1,2) ++
  hv 0 (
    pp_join_ary (spc ())
      (Array.map
        (fun (nm, ty, fargs, context, envb, body) ->
           pp_join_list (spc ())
             (List.map
               (fun (var, ty) -> hv 0 (str (c_typename ty) ++ spc () ++ str var ++ str ";"))
               fargs))
        ntfcb_ary) ++ spc () ++
    hv 0 (str "switch" ++ spc () ++ str "(i)") ++ spc () ++ str "{" ++ brk (1,2) ++
      hv 0 (
        pp_join_ary (spc ())
          (Array.mapi
            (fun j (nm, ty, fargs, context, envb, body) ->
              let headcall, tailcall, partcall = callsites_ary.(j) in
              let (argtys, rety) = nargtys_and_rety_of_type (List.length fargs) ty in
              let fname_argn = goto_label nm in
              hv 0 (
                (if j == i then str "default:" else hv 0 (str "case" ++ spc () ++ int j ++ str ":")) ++ brk (1,2) ++
                hv 0 (
                  pp_join_list (spc ())
                    (List.map
                      (fun (var, ty) -> hv 0 (str var ++ spc () ++ str "=" ++ spc () ++ str "((struct" ++ spc () ++ str nm ++ spc () ++ str "*)argsp)->" ++ str var ++ str ";"))
                      fargs) ++ spc () ++
                  (if tailcall then str fname_argn ++ str ":;" ++ spc () else mt ()) ++
                  genc_mufun_body_tail envb sigma ("(*(" ^ c_typename rety ^ " *)retp)") context body ++ spc () ++
                  str "return;")))
            ntfcb_ary)) ++ spc () ++ str "}") ++ spc () ++
    str "}")

let genc_mufun_single_func (sigma : Evd.evar_map) (mfnm : string) (i : int)
    (ntfcb_ary : (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let entry_nm, entry_ty, entry_fargs, entry_context, entry_envb, entry_body = ntfcb_ary.(i) in
  let (entry_argtys, entry_rety) = nargtys_and_rety_of_type (List.length entry_fargs) entry_ty in
  let c_fname = c_funcname entry_nm in
  let label_fname_argn = goto_label entry_nm in
  hv 0 (
  str "static" ++ spc () ++
  str (c_typename entry_rety) ++ spc () ++
  str c_fname ++ str "(" ++
  hv 0 (genc_fargs entry_fargs) ++
  str ")" ++ spc () ++
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
                (fun (var, ty) -> hv 0 (str (c_typename ty) ++ spc () ++ str var ++ str ";"))
                fargs))
        ntfcb_ary) ++
    (if i = 0 then mt () else hv 0 (str "goto" ++ spc () ++ str label_fname_argn ++ str ";") ++ spc ()) ++
    pp_join_ary (spc ())
      (Array.mapi
        (fun j (nm, ty, fargs, context, envb, body) ->
          let headcall, tailcall, partcall = callsites_ary.(j) in
          let fname_argn = goto_label nm in
          hv 0 (
            (if tailcall || (i <> 0 && i == j) then str fname_argn ++ str ":;" ++ spc () else mt ()) ++
            genc_body_tail envb sigma context body))
        ntfcb_ary)) ++
  spc () ++ str "}")

let genc_func_mutual (sigma : Evd.evar_map) (mfnm : string) (i : int)
    (ntfcb_ary : (string * Constr.types * (string * Constr.types) list * context_elt list * Environ.env * Constr.t) array)
    (callsites_ary : (bool * bool * bool) array) : Pp.t =
  let num_entry_funcs = Array.fold_left (+) 0 (Array.map (fun (headcall, tailcall, partcall) -> if headcall then 1 else 0) callsites_ary) in
  if num_entry_funcs = 1 then
    genc_mufun_single_func sigma mfnm i ntfcb_ary callsites_ary
  else
    genc_mufun_structs ntfcb_ary callsites_ary ++ spc () ++
    genc_mufun_forward_decl mfnm ++ spc () ++
    genc_mufun_entries mfnm ntfcb_ary callsites_ary ++ spc () ++
    genc_mufun_bodies_func sigma mfnm i ntfcb_ary callsites_ary

let genc_func (env : Environ.env) (sigma : Evd.evar_map) (fname : string) (ty : Constr.types) (term : Constr.t) : Pp.t =
  local_gensym_with (fun () ->
  match Constr.kind term with
  | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
      let env2 = Environ.push_rec_types (nameary, tyary, funary) env in
      let nameary' = Array.map Context.binder_name nameary in
      let strnameary = Array.mapi (fun j nm ->
          if j = i then
            fname
          else
            let nm = Context.binder_name nm in
            gensym_with_name nm)
        nameary
      in
      let ntfcb_ary = fargs_and_body_ary env2 strnameary ty ia i nameary' tyary funary in
      let callsites_ary = scan_callsites sigma i ntfcb_ary in
      let mfnm = gensym_with_str fname in
      genc_func_mutual sigma mfnm i ntfcb_ary callsites_ary
  | _ ->
      let fargs, envb, body = fargs_and_body env term in
      let context = List.rev_map (fun (var, ty) -> CtxVar var) fargs in
      genc_func_single envb sigma fname ty fargs context body)

let get_ctnt_type_body (env : Environ.env) (name : Libnames.qualid) : Constant.t * Constr.types * Constr.t =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef ctnt ->
      begin match Global.body_of_constant ctnt with
      | Some (b,_) ->
          let (ty, _) = Typeops.type_of_global_in_context env reference in
          (ctnt, ty, b)
      | None -> user_err (Pp.str "can't genc axiom")
      end
  | VarRef _ -> user_err (Pp.str "can't genc VarRef")
  | IndRef _ -> user_err (Pp.str "can't genc IndRef")
  | ConstructRef _ -> user_err (Pp.str "can't genc ConstructRef")

let genc (libref_list : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  List.iter
    (fun libref ->
      let (ctnt, ty, body) = get_ctnt_type_body env libref in
      linear_type_check_term body;
      let fname = Label.to_string (KerName.label (Constant.canonical ctnt)) in
      let pp = genc_func env sigma fname ty body in
      Feedback.msg_info pp)
    libref_list

let genc_file (fn : string) (libref_list : Libnames.qualid list) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (let ch = open_out fn in
  let fmt = Format.formatter_of_out_channel ch in
  List.iter
    (fun libref ->
      let (ctnt, ty, body) = get_ctnt_type_body env libref in
      linear_type_check_term body;
      let fname = Label.to_string (KerName.label (Constant.canonical ctnt)) in
      let pp = genc_func env sigma fname ty body in
      Pp.pp_with fmt (pp ++ Pp.fnl ()))
    libref_list;
  Format.pp_print_flush fmt ();
  close_out ch;
  Feedback.msg_info (str ("file generated: " ^ fn)))
