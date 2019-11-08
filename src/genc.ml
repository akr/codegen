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
open Linear

let array_find_index_opt (p : 'a -> bool) (ary : 'a array) : int option =
  let len = Array.length ary in
  let rec aux i =
    if len <= i then
      None
    else if p (Array.get ary i) then
      Some i
    else
      aux (i + 1)
  in
  aux 0

let array_copy_set (ary : 'a array) (i : int) (v : 'a) : 'a array =
  let ret = Array.copy ary in
  Array.set ret i v;
  ret

let array_find_index (p : 'a -> bool) (ary : 'a array) : int =
  match array_find_index_opt p ary with
  | None -> raise Not_found
  | Some i -> i

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
      | None -> raise (CodeGenError "inductive type not registered")
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

let register_ind_cstr (user_coq_type : Constrexpr.constr_expr) (coq_cstr : Id.t)
    (c_cstr : string) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, coq_type) = nf_interp_constr env sigma user_coq_type in
  let (mutind_body, i, oneind_body, args) = get_ind_coq_type env coq_type in
  let ind_cfg = get_ind_config coq_type in
  let j = match array_find_index_opt (Id.equal coq_cstr) oneind_body.Declarations.mind_consnames with
    | Some j -> j
    | None -> raise (CodeGenError "inductive type constructor not found")
  in
  let cstr_cfg = Array.get ind_cfg.cstr_configs j in
  (match cstr_cfg.c_cstr with
  | Some _ -> raise (CodeGenError "inductive type constructor already registered")
  | None -> ());
  ind_config_map := ConstrMap.add coq_type
    { ind_cfg with
      cstr_configs = array_copy_set ind_cfg.cstr_configs j { cstr_cfg with c_cstr = Some c_cstr } }
    !ind_config_map

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

let c_id str =
  let buf = Buffer.create 0 in
  String.iter
    (fun ch ->
      match ch with
      |'_'|'0'..'9'|'A'..'Z'|'a'..'z' -> Buffer.add_char buf ch
      | _ -> Buffer.add_char buf '_')
    str;
  Buffer.contents buf

let funcname_argnum fname n =
  "n" ^ string_of_int n ^ (c_id fname)

let c_typename ty =
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg -> ind_cfg.c_type
  | None -> c_id (mangle_type ty)

let c_cstrname ty cstru =
  let ((mutind, i), j) = Univ.out_punivs cstru in
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.cstr_configs.(j-1).c_cstr with
      | Some c_cstr -> c_cstr
      | None -> raise (CodeGenError "inductive constructor configuration not registered"))
  | None ->
      let env = Global.env () in
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.Declarations.mind_packets.(i) in
      let cons_id = oind_body.Declarations.mind_consnames.(j-1) in
      let nargs = oind_body.Declarations.mind_consnrealargs.(j-1) in
      let fname = Id.to_string cons_id in
      let fname_argn = funcname_argnum fname nargs in
      fname_argn

let case_swfunc ty =
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.c_swfunc with
      | Some c_swfunc -> c_swfunc
      | None -> raise (CodeGenError "inductive match configuration not registered"))
  | None -> c_id ("sw_" ^ (mangle_type ty))

let case_cstrlabel_short ty j =
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.c_swfunc with
      | Some _ -> ind_cfg.cstr_configs.(j-1).c_caselabel
      | None -> raise (CodeGenError "inductive match configuration not registered"))
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

let case_cstrlabel ty j =
  case_cstrlabel_short ty j

let case_cstrfield_short ty j k =
  match ConstrMap.find_opt ty !ind_config_map with
  | Some ind_cfg ->
      (match ind_cfg.c_swfunc with
      | Some _ -> ind_cfg.cstr_configs.(j-1).c_accessors.(k)
      | None -> raise (CodeGenError "inductive match configuration not registered"))
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

let case_cstrfield ty j k =
  case_cstrfield_short ty j k

let gensym_id = Summary.ref 0 ~name:"CodegenGensymID"

let gensym () =
  let n = !gensym_id in
  gensym_id := n + 1;
  "g" ^ string_of_int n

let gensym_with_str suffix =
  gensym () ^ "_" ^ (c_id suffix)

let gensym_with_name name =
  match name with
  | Names.Name.Anonymous -> gensym ()
  | Names.Name.Name id -> gensym () ^ "_" ^ (c_id (Id.to_string id))

let gensym_with_nameopt nameopt =
  match nameopt with
  | None -> gensym ()
  | Some name -> gensym_with_name name

let local_gensym_id : (int ref) list ref = ref []

let  local_gensym_with f =
  local_gensym_id := (ref 0) :: !local_gensym_id;
  let ret = f () in
  local_gensym_id := List.tl !local_gensym_id;
  ret

let local_gensym () =
  let idref = List.hd !local_gensym_id in
  let n = !idref in
  idref := n + 1;
  "v" ^ string_of_int n

let local_gensym_with_str suffix =
  local_gensym () ^ "_" ^ (c_id suffix)

let local_gensym_with_name name =
  match name with
  | Names.Name.Anonymous -> local_gensym ()
  | Names.Name.Name id -> local_gensym () ^ "_" ^ (c_id (Id.to_string id))

let local_gensym_with_nameopt nameopt =
  match nameopt with
  | None -> local_gensym ()
  | Some name -> local_gensym_with_name name

let rec argtys_and_rety_of_type ty =
  match Constr.kind ty with
  | Constr.Prod (name, ty', body) ->
      let (argtys, rety) = argtys_and_rety_of_type body in
      (ty :: argtys, rety)
  | _ -> ([], ty)

let rec nargtys_and_rety_of_type n ty =
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

let rec fargs_and_body env term =
  match Constr.kind term with
  | Constr.Lambda (name, ty, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = Environ.push_rel decl env in
      let var = local_gensym_with_name (Context.binder_name name) in
      let fargs1, env1, body1 = fargs_and_body env2 body in
      let fargs2 = (var, ty) :: fargs1 in
      (fargs2, env1, body1)
  | _ -> ([], env, term)

let fargs_and_body_ary env fname ty ia i nameary tyary funary =
  let strnameary = Array.mapi (fun j nm -> if j = i then fname else gensym_with_name nm) nameary in
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

let genc_farg farg =
  let (var, ty) = farg in
  hv 2 (str (c_typename ty) ++ spc () ++ str var)

let genc_fargs fargs =
  match fargs with
  | [] -> str "void"
  | farg1 :: rest ->
      List.fold_left
        (fun pp farg -> pp ++ str "," ++ spc () ++ genc_farg farg)
        (genc_farg farg1)
        rest

let genc_vardecl ty varname =
  hv 0 (str (c_typename ty) ++ spc () ++ str varname ++ str ";")

let genc_varinit ty varname init =
  hv 0 (str (c_typename ty) ++ spc () ++ str varname ++ spc () ++ str "=" ++ spc () ++ init ++ str ";")

let genc_assign lhs rhs =
  hv 0 (lhs ++ spc () ++ str "=" ++ spc () ++ rhs ++ str ";")

let genc_return arg =
  hv 0 (str "return" ++ spc () ++ arg ++ str ";")

let genc_void_return retvar arg =
  hv 0 (genc_assign (str retvar) arg ++ spc () ++ str "return;")

let varname_of_rel context i =
  match List.nth context (i-1) with
  | CtxVar varname -> varname
  | _ -> raise (Invalid_argument "unexpected context element")

let genc_app env sigma context f argsary =
  match Constr.kind f with
  | Constr.Rel i ->
      (match List.nth context (i-1) with
      | CtxVar _ -> user_err (str "indirect call not implemented")
      | CtxRec (fname, _) ->
          let argvars = Array.map (fun arg -> varname_of_rel context (Constr.destRel arg)) argsary in
          let fname_argn = funcname_argnum fname (Array.length argvars) in
          str fname_argn ++ str "(" ++
          pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
          str ")")
  | Constr.Const ctntu ->
      let fname = Label.to_string (KerName.label (Constant.canonical (Univ.out_punivs ctntu))) in
      let fname_argn = funcname_argnum fname (Array.length argsary) in
      let argvars = Array.map (fun arg -> varname_of_rel context (Constr.destRel arg)) argsary in
      str fname_argn ++ str "(" ++
      pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
      str ")"
  | Constr.Construct cstru ->
      let ty = EConstr.to_constr sigma (Reductionops.nf_all env sigma (Retyping.get_type_of env sigma (EConstr.of_constr (Constr.mkApp (f, argsary))))) in
      (*Feedback.msg_info (Printer.pr_constr_env env sigma ty);*)
      let fname_argn = c_cstrname ty cstru in
      let argvars = Array.map (fun arg -> varname_of_rel context (Constr.destRel arg)) argsary in
      str fname_argn ++ str "(" ++
      pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
      str ")"
  | _ -> assert false

let genc_multi_assign assignments =
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

let genc_goto context ctxrec argsary =
  let fname, argvars = ctxrec in
  (if Array.length argsary <> Array.length argvars then
    user_err (str "partial function invocation not supported yet");
  let fname_argn = funcname_argnum fname (Array.length argvars) in
  let assignments =
    (array_map2
      (fun (var, ty) arg -> (var, (varname_of_rel context (Constr.destRel arg), ty)))
      argvars argsary)
  in
  let pp_assigns = genc_multi_assign assignments in
  let pp_goto = (hv 0 (str "goto" ++ spc () ++ str fname_argn ++ str ";")) in
  if Pp.ismt pp_assigns then pp_goto else pp_assigns ++ spc () ++ pp_goto)

let genc_const env sigma context ctntu =
  genc_app env sigma context (Constr.mkConstU ctntu) [| |]

let split_case_tyf tyf =
  match Constr.kind tyf with
  | Constr.Lambda (name, ty, body) -> (ty, body)
  | _ -> user_err (str "unexpected case type function")

let rec strip_outer_lambdas ndecls term =
  if ndecls = 0 then
    ([], term)
  else
    match Constr.kind term with
    | Constr.Lambda (name, ty, body) ->
        let (decls, innermostbody) = strip_outer_lambdas (ndecls-1) body in
        ((name, ty) :: decls, innermostbody)
    | _ -> user_err (str "case body lambda nesting is not enough")

let iota_ary m n =
  Array.init n (fun i -> m + i)

let iota_list m n =
  Array.to_list (iota_ary m n)

let array_map3 f a b c =
  let n = Array.length a in
  if Array.length b <> n then raise (Invalid_argument "array_map3");
  if Array.length c <> n then raise (Invalid_argument "array_map3");
  Array.init n (fun i -> f a.(i) b.(i) c.(i))

let constr_name term =
  match Constr.kind term with
  | Constr.Rel _ -> "Rel"
  | Constr.Var _ -> "Var"
  | Constr.Meta _ -> "Meta"
  | Constr.Evar _ -> "Evar"
  | Constr.Sort _ -> "Sort"
  | Constr.Cast _ -> "Cast"
  | Constr.Prod _ -> "Prod"
  | Constr.Lambda _ -> "Lambda"
  | Constr.LetIn _ -> "LetIn"
  | Constr.App _ -> "App"
  | Constr.Const _ -> "Const"
  | Constr.Ind _ -> "Ind"
  | Constr.Construct _ -> "Construct"
  | Constr.Case _ -> "Case"
  | Constr.Fix _ -> "Fix"
  | Constr.CoFix _ -> "CoFix"
  | Constr.Proj _ -> "Proj"
  | Constr.Int _ -> "Int"

let genc_case_branch_body env (sigma : Evd.evar_map) context (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> Constr.constr -> Pp.t) exprty exprvar ndecls br cstr_index =
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

let genc_case_branch env sigma context bodyfunc exprty exprvar ndecls br cstr_index =
  let cstr_label = case_cstrlabel exprty cstr_index in
  let pp_label = str cstr_label ++ str ":" in
  hv 0 (hv 0 (pp_label ++ spc () ++ str "{") ++ brk (1,2) ++
    hv 0 (genc_case_branch_body env sigma context bodyfunc exprty exprvar ndecls br cstr_index) ++ spc () ++
    str "}")

let genc_case_nobreak env sigma context ci tyf expr brs (bodyfunc : Environ.env -> Evd.evar_map -> context_elt list -> Constr.constr -> Pp.t) =
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

let genc_case_break env sigma context ci tyf expr brs bodyfunc =
  genc_case_nobreak env sigma context ci tyf expr brs
    (fun envb sigma context2 body -> bodyfunc envb sigma context2 body ++ spc () ++ str "break;")

let genc_geninitvar ty (namehint : Names.Name.t) init =
  let varname = local_gensym_with_name namehint in
  (genc_varinit ty varname init, varname)

(* not tail position. return a variable *)
let rec genc_body_var env sigma context (namehint : Names.Name.t) term termty =
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
  | _ -> (user_err (str "not impelemented (genc_body_var:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

(* not tail position. assign to the specified variable *)
and genc_body_assign env sigma context retvar term =
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

  | _ -> (user_err (str "not impelemented (genc_body_assign:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

(* tail position.  usual return. *)
let rec genc_body_tail env sigma context term =
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

  | _ -> (user_err (str "not impelemented (genc_body_tail:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

(* tail position.  assign and return. *)
let rec genc_body_void_tail env sigma retvar context term =
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
      genc_body_void_tail env2 sigma retvar (CtxVar varname :: context) body
  | Constr.App (f, argsary) ->
      (match Constr.kind f with
      | Constr.Rel i ->
          (match List.nth context (i-1) with
          | CtxRec (fname, argvars) -> genc_goto context (fname, argvars) argsary
          | _ -> genc_void_return retvar (genc_app env sigma context f argsary))
      | _ -> genc_void_return retvar (genc_app env sigma context f argsary))
  | Constr.Case (ci, tyf, expr, brs) ->
      genc_case_nobreak env sigma context ci tyf expr brs
        (fun envb sigma -> genc_body_void_tail envb sigma retvar)
  | Constr.Const ctntu ->
      genc_void_return retvar (genc_const env sigma context ctntu)

  | _ -> (user_err (str "not impelemented (genc_body_void_tail:" ++ str (constr_name term) ++ str "): " ++ Printer.pr_constr_env env sigma term))

(*
let rec copy_term term =
  match Constr.kind term with
x | Term.Rel i -> Term.mkRel i
  | Term.Var name -> Term.mkVar name
  | Term.Meta i -> Term.mkMeta i
  | Term.Evar (ekey, termary) -> Term.mkEvar (ekey, (Array.map copy_term termary))
  | Term.Sort s -> Term.mkSort s
  | Term.Cast (expr, kind, ty) -> Term.mkCast (copy_term expr, kind, copy_term ty)
  | Term.Prod (name, ty, body) -> Term.mkProd (name, copy_term ty, copy_term body)
  | Term.Lambda (name, ty, body) -> Term.mkLambda (name, copy_term ty, copy_term body)
x | Term.LetIn (name, expr, ty, body) -> Term.mkLetIn (name, copy_term expr, copy_term ty, copy_term body)
x | Term.App (f, argsary) -> Term.mkApp (copy_term f, Array.map copy_term argsary)
  | Term.Const ctntu -> Term.mkConstU ctntu
  | Term.Ind iu -> Term.mkIndU iu
  | Term.Construct cstru -> Term.mkConstructU cstru
x | Term.Case (ci, tyf, expr, brs) -> Term.mkCase (ci, copy_term tyf, copy_term expr, Array.map copy_term brs)
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      Term.mkFix ((ia, i), (nameary, Array.map copy_term tyary, Array.map copy_term funary))
  | Term.CoFix (i, (nameary, tyary, funary)) ->
      Term.mkCoFix (i, (nameary, Array.map copy_term tyary, Array.map copy_term funary))
  | Term.Proj (proj, expr) ->
      Term.mkProj (proj, copy_term expr)
*)

let found_funref context i =
  match List.nth context (i-1) with
  | None -> ()
  | Some callsites ->
      let nargs, headcall, tailcall, partcall = callsites in
      partcall := true

let found_callsite tail context i n =
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

let rec scan_callsites_rec env sigma tail context term =
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

let scan_callsites sigma i ntfcb_ary =
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

let genc_func_single env sigma fname ty fargs context body =
  (*let (ty, fargs, context, body) = fargs_and_body fname term in*)
  let (argtys, rety) = argtys_and_rety_of_type ty in
  (if List.length argtys <> List.length fargs then
    user_err (str ("function value not supported yet: " ^
      string_of_int (List.length argtys) ^ " prods and " ^
      string_of_int (List.length fargs) ^ " lambdas")));
  let fname_argn = funcname_argnum fname (List.length argtys) in
  hv 0 (
  str "static" ++ spc () ++
  str (c_typename rety) ++ spc () ++
  str fname_argn ++ str "(" ++
  hv 0 (genc_fargs fargs) ++
  str ")" ++ spc () ++
  str "{" ++ brk (1,2) ++
  hv 0 (
    genc_body_tail env sigma context body) ++
  spc () ++ str "}")

let find_headcalls ntfcb_ary callsites_ary =
  Array.concat
    (Array.to_list
      (array_map2
        (fun ntfcb (headcall, tailcall, partcall) ->
          if headcall then [| ntfcb |] else [| |])
        ntfcb_ary callsites_ary))

let genc_mufun_struct_one ntfcb =
  let nm, ty, fargs, context, envb, body = ntfcb in
  hv 0 (
  str "struct" ++ spc () ++
  str nm ++ spc () ++
  str "{" ++ spc () ++
  pp_postjoin_list (str ";" ++ spc ()) (List.map genc_farg fargs) ++
  str "};")

let genc_mufun_structs ntfcb_ary callsites_ary =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.map genc_mufun_struct_one ntfcb_ary2)

let genc_mufun_entry mfnm i ntfcb =
  let nm, ty, fargs, context, envb, body = ntfcb in
  let (argtys, rety) = nargtys_and_rety_of_type (List.length fargs) ty in
  let fname_argn = funcname_argnum nm (List.length argtys) in
  hv 0 (
  str "static" ++ spc () ++
  str (c_typename rety) ++ spc () ++
  str fname_argn ++ str "(" ++
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

let genc_mufun_entries mfnm ntfcb_ary callsites_ary =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.mapi (genc_mufun_entry mfnm) ntfcb_ary2)

let genc_mufun_forward_decl mfnm =
  hv 0 (
  str "static" ++ spc () ++
  str "void" ++ spc () ++
  str mfnm ++ str "(" ++
  hv 0 (
    hv 0 (str "int" ++ spc () ++ str "i") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "argsp") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "retp")) ++ str ");")

let genc_mufun_bodies_func sigma mfnm i ntfcb_ary callsites_ary =
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
              let fname_argn = funcname_argnum nm (List.length argtys) in
              hv 0 (
                (if j == i then str "default:" else hv 0 (str "case" ++ spc () ++ int j ++ str ":")) ++ brk (1,2) ++
                hv 0 (
                  pp_join_list (spc ())
                    (List.map
                      (fun (var, ty) -> hv 0 (str var ++ spc () ++ str "=" ++ spc () ++ str "((struct" ++ spc () ++ str nm ++ spc () ++ str "*)argsp)->" ++ str var ++ str ";"))
                      fargs) ++ spc () ++
                  (if tailcall then str fname_argn ++ str ":;" ++ spc () else mt ()) ++
                  genc_body_void_tail envb sigma ("(*(" ^ c_typename rety ^ " *)retp)") context body ++ spc () ++
                  str "return;")))
            ntfcb_ary)) ++ spc () ++ str "}") ++ spc () ++
    str "}")

let genc_mufun_single_func sigma mfnm i ntfcb_ary callsites_ary =
  let entry_nm, entry_ty, entry_fargs, entry_context, entry_envb, entry_body = ntfcb_ary.(i) in
  let (entry_argtys, entry_rety) = nargtys_and_rety_of_type (List.length entry_fargs) entry_ty in
  let entry_fname_argn = funcname_argnum entry_nm (List.length entry_argtys) in
  hv 0 (
  str "static" ++ spc () ++
  str (c_typename entry_rety) ++ spc () ++
  str entry_fname_argn ++ str "(" ++
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
    (if i = 0 then mt () else hv 0 (str "goto" ++ spc () ++ str entry_fname_argn ++ str ";") ++ spc ()) ++
    pp_join_ary (spc ())
      (Array.mapi
        (fun j (nm, ty, fargs, context, envb, body) ->
          let headcall, tailcall, partcall = callsites_ary.(j) in
          let (argtys, rety) = nargtys_and_rety_of_type (List.length fargs) ty in
          let fname_argn = funcname_argnum nm (List.length argtys) in
          hv 0 (
            (if tailcall || (i <> 0 && i == j) then str fname_argn ++ str ":;" ++ spc () else mt ()) ++
            genc_body_tail envb sigma context body))
        ntfcb_ary)) ++
  spc () ++ str "}")

let genc_func_mutual sigma mfnm i ntfcb_ary callsites_ary =
  let num_entry_funcs = Array.fold_left (+) 0 (Array.map (fun (headcall, tailcall, partcall) -> if headcall then 1 else 0) callsites_ary) in
  if num_entry_funcs = 1 then
    genc_mufun_single_func sigma mfnm i ntfcb_ary callsites_ary
  else
    genc_mufun_structs ntfcb_ary callsites_ary ++ spc () ++
    genc_mufun_forward_decl mfnm ++ spc () ++
    genc_mufun_entries mfnm ntfcb_ary callsites_ary ++ spc () ++
    genc_mufun_bodies_func sigma mfnm i ntfcb_ary callsites_ary

let genc_func env sigma fname ty term =
  local_gensym_with (fun () ->
  match Constr.kind term with
  | Constr.Fix ((ia, i), (nameary, tyary, funary)) ->
      let env2 = Environ.push_rec_types (nameary, tyary, funary) env in
      let nameary = Array.map Context.binder_name nameary in
      let ntfcb_ary = fargs_and_body_ary env2 fname ty ia i nameary tyary funary in
      let callsites_ary = scan_callsites sigma i ntfcb_ary in
      let mfnm = gensym_with_str fname in
      genc_func_mutual sigma mfnm i ntfcb_ary callsites_ary
  | _ ->
      let fargs, envb, body = fargs_and_body env term in
      let context = List.rev_map (fun (var, ty) -> CtxVar var) fargs in
      genc_func_single envb sigma fname ty fargs context body)

let get_name_type_body env (name : Libnames.qualid) =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef ctnt ->
      begin match Global.body_of_constant ctnt with
      | Some (b,_) ->
          let name = Label.to_string (KerName.label (Constant.canonical ctnt)) in
          let (ty, _) = Typeops.type_of_global_in_context env reference in
          (name, ty, b)
      | None -> user_err (Pp.str "can't genc axiom")
      end
  | VarRef _ -> user_err (Pp.str "can't genc VarRef")
  | IndRef _ -> user_err (Pp.str "can't genc IndRef")
  | ConstructRef _ -> user_err (Pp.str "can't genc ConstructRef")

let genc libref_list =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  List.iter
    (fun libref ->
      let (name, ty, body) = get_name_type_body env libref in
      linear_type_check_term body;
      let pp = genc_func env sigma name ty body in
      Feedback.msg_info pp)
    libref_list

let genc_file fn libref_list =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (let ch = open_out fn in
  let fmt = Format.formatter_of_out_channel ch in
  List.iter
    (fun libref ->
      let (name, ty, body) = get_name_type_body env libref in
      linear_type_check_term body;
      let pp = (genc_func env sigma name ty body) ++ Pp.fnl () in
      Pp.pp_with fmt pp)
    libref_list;
  Format.pp_print_flush fmt ();
  close_out ch;
  Feedback.msg_info (str ("file generated: " ^ fn)))
