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
open Goptions

open Monoutil

let c_id str =
  let buf = Buffer.create 0 in
  String.iter
    (fun ch ->
      match ch with
      |'_'|'0'..'9'|'A'..'Z'|'a'..'z' -> Buffer.add_char buf ch
      | _ -> Buffer.add_char buf '_')
    str;
  Buffer.contents buf

let c_mangle_type ty = c_id (mangle_type ty)

let case_swfunc ty = c_id ("sw_" ^ (mangle_type ty))

let case_cstrlabel_short ty j =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let indty =
    match Term.kind_of_term ty with
    | Term.App (f, argsary) -> f
    | _ -> ty
  in
  let (mutind, i) = Univ.out_punivs (Term.destInd indty) in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  let consname = Id.to_string oneind_body.Declarations.mind_consnames.(j-1) in
  c_id ("case_" ^ consname ^ "_" ^ (mangle_type ty))

let case_cstrlabel ty j =
  case_cstrlabel_short ty j

let case_cstrfield_short ty j k =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let indty =
    match Term.kind_of_term ty with
    | Term.App (f, argsary) -> f
    | _ -> ty
  in
  let (mutind, i) = Univ.out_punivs (Term.destInd indty) in
  let mutind_body = Environ.lookup_mind mutind env in
  let oneind_body = mutind_body.Declarations.mind_packets.(i) in
  let consname = Id.to_string oneind_body.Declarations.mind_consnames.(j-1) in
  c_id ("field" ^ string_of_int k ^ "_" ^ consname ^ "_" ^ (mangle_type ty))

let case_cstrfield ty j k =
  case_cstrfield_short ty j k

let gensym_id = Summary.ref 0 ~name:"MonomorphizationGensymID"

let gensym () =
  let n = !gensym_id in
  gensym_id := n + 1;
  "v" ^ string_of_int n

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

let rec argtys_and_rety_of_type ty =
  match Term.kind_of_term ty with
  | Term.Prod (name, ty', body) ->
      let (argtys, rety) = argtys_and_rety_of_type body in
      (ty :: argtys, rety)
  | _ -> ([], ty)

let rec nargtys_and_rety_of_type n ty =
  if n == 0 then
    ([], ty)
  else
    match Term.kind_of_term ty with
    | Term.Prod (name, ty', body) ->
        let (argtys, rety) = nargtys_and_rety_of_type (n-1) body in
        (ty :: argtys, rety)
    | _ -> error "too few prods in type"

type context_elt =
  | CtxVar of string
  | CtxRec of string * (string * Term.types) array (* fname, argname_argtype_array *)

let rec fargs_and_body term =
  match Term.kind_of_term term with
  | Term.Lambda (name, ty, body) ->
      let fargs1, body1 = fargs_and_body body in
      let var = gensym_with_name name in
      let fargs2 = (var, ty) :: fargs1 in
      (fargs2, body1)
  | _ -> ([], term)

let fargs_and_body_ary fname ty ia i nameary tyary funary =
  let strnameary = Array.mapi (fun j nm -> if j = i then fname else gensym_with_name nm) nameary in
  let fb_ary = Array.map (fun term1 -> fargs_and_body term1) funary in
  let ctxrec_ary = Array.map
    (fun j ->
      let nm = strnameary.(j) in
      let fargs, body = fb_ary.(j) in
      CtxRec (nm, Array.of_list fargs))
    (iota_ary 0 (Array.length funary))
  in
  let ctxrec_list = Array.to_list ctxrec_ary in
  let fb_ary2 = array_map2
    (fun ty (fargs, body) ->
      let context1 = List.rev_map (fun (var, ty) -> CtxVar var) fargs in
      let context2 = List.append context1 (List.rev ctxrec_list) in
      (ty, fargs, context2, body))
    tyary fb_ary
  in
  array_map2 (fun nm (ty, fargs, context, body) -> (nm, ty, fargs, context, body)) strnameary fb_ary2

let genc_farg farg =
  let (var, ty) = farg in
  hv 2 (str (c_mangle_type ty) ++ spc () ++ str var)

let genc_fargs fargs =
  match fargs with
  | [] -> str "void"
  | farg1 :: rest ->
      List.fold_left
        (fun pp farg -> pp ++ str "," ++ spc () ++ genc_farg farg)
        (genc_farg farg1)
        rest

let genc_vardecl ty varname =
  hv 0 (str (c_mangle_type ty) ++ spc () ++ str varname ++ str ";")

let genc_varinit ty varname init =
  hv 0 (str (c_mangle_type ty) ++ spc () ++ str varname ++ spc () ++ str "=" ++ spc () ++ init ++ str ";")

let genc_assign lhs rhs =
  hv 0 (lhs ++ spc () ++ str "=" ++ spc () ++ rhs ++ str ";")

let genc_return arg =
  hv 0 (str "return" ++ spc () ++ arg ++ str ";")

let genc_void_return retvar arg =
  hv 0 (genc_assign (str retvar) arg ++ spc () ++ str "return;")

let funcname_argnum fname n =
  "n" ^ string_of_int n ^ (c_id fname)

let varname_of_rel context i =
  match List.nth context (i-1) with
  | CtxVar varname -> varname
  | _ -> raise (Invalid_argument "unexpected context element")

let genc_app context f argsary =
  match Term.kind_of_term f with
  | Term.Rel i ->
      (match List.nth context (i-1) with
      | CtxVar _ -> error "indirect call not implemented"
      | CtxRec (fname, _) ->
          let argvars = Array.map (fun arg -> varname_of_rel context (Term.destRel arg)) argsary in
          let fname_argn = funcname_argnum fname (Array.length argvars) in
          str fname_argn ++ str "(" ++
          pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
          str ")")
  | Term.Const ctntu ->
      let fname = Label.to_string (KerName.label (Constant.canonical (Univ.out_punivs ctntu))) in
      let fname_argn = funcname_argnum fname (Array.length argsary) in
      let argvars = Array.map (fun arg -> varname_of_rel context (Term.destRel arg)) argsary in
      str fname_argn ++ str "(" ++
      pp_join_ary (str "," ++ spc ()) (Array.map (fun av -> str av) argvars) ++
      str ")"
  | Term.Construct cstru ->
      let ((mutind, i), j) = Univ.out_punivs cstru in
      let env = Global.env () in
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.Declarations.mind_packets.(i) in
      let cons_id = oind_body.Declarations.mind_consnames.(j-1) in
      let fname = Id.to_string cons_id in
      let fname_argn = funcname_argnum fname (Array.length argsary) in
      let argvars = Array.map (fun arg -> varname_of_rel context (Term.destRel arg)) argsary in
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
          let tmp = gensym () in
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
    error ("partial function invocation not supported yet"));
  let fname_argn = funcname_argnum fname (Array.length argvars) in
  let assignments =
    (array_map2
      (fun (var, ty) arg -> (var, (varname_of_rel context (Term.destRel arg), ty)))
      argvars argsary)
  in
  let pp_assigns = genc_multi_assign assignments in
  let pp_goto = (hv 0 (str "goto" ++ spc () ++ str fname_argn ++ str ";")) in
  if Pp.ismt pp_assigns then pp_goto else pp_assigns ++ spc () ++ pp_goto

let genc_const context ctntu =
  genc_app context (Term.mkConstU ctntu) [| |]

let split_case_tyf tyf =
  match Term.kind_of_term tyf with
  | Term.Lambda (name, ty, body) -> (ty, body)
  | _ -> error "unexpected case type function"

let rec strip_outer_lambdas ndecls term =
  if ndecls = 0 then
    ([], term)
  else
    match Term.kind_of_term term with
    | Term.Lambda (name, ty, body) ->
        let (decls, innermostbody) = strip_outer_lambdas (ndecls-1) body in
        ((name, ty) :: decls, innermostbody)
    | _ -> error "case body lambda nesting is not enough"

let iota_ary m n =
  Array.init n (fun i -> m + i)

let iota_list m n =
  Array.to_list (iota_ary m n)

let array_map3 f a b c =
  let n = Array.length a in
  if Array.length b <> n then raise (Invalid_argument "array_map3");
  if Array.length c <> n then raise (Invalid_argument "array_map3");
  Array.init n (fun i -> f a.(i) b.(i) c.(i))

let genc_case_branch_body context bodyfunc exprty exprvar ndecls br cstr_index =
  let (decls, body) = strip_outer_lambdas ndecls br in
  let decls2 =
    List.map2
      (fun (name, ty) field_index ->
        let varname = gensym_with_name name in
        let cstr_field = case_cstrfield exprty cstr_index field_index in
        (CtxVar varname, genc_varinit ty varname (str cstr_field ++ str "(" ++ str exprvar ++ str ")")))
       decls
      (iota_list 0 (List.length decls))
  in
  let context2 = List.rev_append (List.map fst decls2) context in
  let decls3 = List.map snd decls2 in
  pp_postjoin_list (spc ()) decls3 ++ bodyfunc context2 body

let genc_case_branch context bodyfunc exprty exprvar ndecls br cstr_index =
  let cstr_label = case_cstrlabel exprty cstr_index in
  let pp_label = str cstr_label ++ str ":" in
  hv 0 (hv 0 (pp_label ++ spc () ++ str "{") ++ brk (1,2) ++
    hv 0 (genc_case_branch_body context bodyfunc exprty exprvar ndecls br cstr_index) ++ spc () ++
    str "}")

let genc_case_nobreak context ci tyf expr brs bodyfunc =
  let (exprty, rety) = split_case_tyf tyf in
  let exprvar = varname_of_rel context (Term.destRel expr) in
  if Array.length brs = 1 then
    let ndecls = ci.Constr.ci_cstr_ndecls.(0) in
    let br = brs.(0) in
    let cstr_index = 1 in
    genc_case_branch_body context bodyfunc exprty exprvar ndecls br cstr_index
  else
    hvb 0 ++
    hv 0 (str "switch" ++ spc () ++ str "(" ++
      str (case_swfunc exprty) ++ str "(" ++
      str exprvar ++ str "))") ++ spc () ++
    str "{" ++ brk (1,2) ++
    hvb 0 ++
    pp_join_ary (spc ())
      (array_map3
        (genc_case_branch context bodyfunc exprty exprvar)
        ci.Constr.ci_cstr_ndecls
        brs
        (iota_ary 1 (Array.length brs))) ++
    close () ++
    spc () ++ str "}" ++
    close ()

let genc_case_break context ci tyf expr brs bodyfunc =
  genc_case_nobreak context ci tyf expr brs
    (fun context2 body -> bodyfunc context2 body ++ spc () ++ str "break;")

let genc_geninitvar ty namehint init =
  let varname = gensym_with_name namehint in
  (genc_varinit ty varname init, varname)

(* not tail position. return a variable *)
let rec genc_body_var context namehint term termty =
  match Term.kind_of_term term with
  | Term.Rel i ->
      (mt (), varname_of_rel context i)
  | Term.LetIn (name, expr, exprty, body) ->
      let (exprbody, varname) = genc_body_var context name expr exprty in
      genc_body_var (CtxVar varname :: context) namehint body termty
  | Term.App (f, argsary) ->
      genc_geninitvar termty namehint (genc_app context f argsary)
  | Term.Case (ci, tyf, expr, brs) ->
      let varname = gensym_with_name namehint in
      (genc_vardecl termty varname ++ spc () ++
       genc_case_break context ci tyf expr brs
        (fun context2 body -> genc_body_assign context2 varname body),
      varname)
  | Term.Const ctntu ->
      genc_geninitvar termty namehint (genc_const context ctntu)
  | _ -> (Feedback.msg_error (str "not impelemented: " ++ Printer.pr_constr term); error "not implemented")

(* not tail position. assign to the specified variable *)
and genc_body_assign context retvar term =
  match Term.kind_of_term term with
  | Term.Rel i ->
      genc_assign (str retvar) (str (varname_of_rel context i))
  | Term.LetIn (name, expr, exprty, body) ->
      let (exprbody, varname) = genc_body_var context name expr exprty in
      genc_body_assign (CtxVar varname :: context) retvar body
  | Term.App (f, argsary) ->
      genc_assign (str retvar) (genc_app context f argsary)
  | Term.Case (ci, tyf, expr, brs) ->
      genc_case_break context ci tyf expr brs
        (fun context2 body -> genc_body_assign context2 retvar body)
  | Term.Const ctntu ->
      genc_assign (str retvar) (genc_const context ctntu)

  | _ -> (Feedback.msg_error (str "not impelemented: " ++ Printer.pr_constr term); error "not implemented")

(* tail position.  usual return. *)
let rec genc_body_tail context term =
  match Term.kind_of_term term with
  | Term.Rel i ->
      genc_return (str (varname_of_rel context i))
  | Term.LetIn (name, expr, exprty, body) ->
      let (exprbody, varname) = genc_body_var context name expr exprty in
      exprbody ++ (if ismt exprbody then mt () else spc ()) ++ genc_body_tail (CtxVar varname :: context) body
  | Term.App (f, argsary) ->
      (match Term.kind_of_term f with
      | Term.Rel i ->
          (match List.nth context (i-1) with
          | CtxRec (fname, argvars) -> genc_goto context (fname, argvars) argsary
          | _ -> genc_return (genc_app context f argsary))
      | _ -> genc_return (genc_app context f argsary))
  | Term.Case (ci, tyf, expr, brs) ->
      genc_case_nobreak context ci tyf expr brs genc_body_tail
  | Term.Const ctntu ->
      genc_return (genc_const context ctntu)

  | _ -> (Feedback.msg_error (str "not impelemented: " ++ Printer.pr_constr term); error "not implemented")

(* tail position.  assign and return. *)
let rec genc_body_void_tail retvar context term =
  match Term.kind_of_term term with
  | Term.Rel i ->
      genc_void_return retvar (str (varname_of_rel context i))
  | Term.LetIn (name, expr, exprty, body) ->
      let (exprbody, varname) = genc_body_var context name expr exprty in
      exprbody ++ (if ismt exprbody then mt () else spc ()) ++ genc_body_void_tail retvar (CtxVar varname :: context) body
  | Term.App (f, argsary) ->
      (match Term.kind_of_term f with
      | Term.Rel i ->
          (match List.nth context (i-1) with
          | CtxRec (fname, argvars) -> genc_goto context (fname, argvars) argsary
          | _ -> genc_void_return retvar (genc_app context f argsary))
      | _ -> genc_void_return retvar (genc_app context f argsary))
  | Term.Case (ci, tyf, expr, brs) ->
      genc_case_nobreak context ci tyf expr brs (genc_body_void_tail retvar)
  | Term.Const ctntu ->
      genc_void_return retvar (genc_const context ctntu)

  | _ -> (Feedback.msg_error (str "not impelemented: " ++ Printer.pr_constr term); error "not implemented")

(*
let rec copy_term term =
  match Term.kind_of_term term with
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

let rec scan_callsites_rec tail context term =
  match Term.kind_of_term term with
  | Term.Const ctntu -> ()
  | Term.Construct cstru -> ()
  | Term.Rel i ->
      found_funref context i
  | Term.Cast (expr, kind, ty) ->
      scan_callsites_rec false context expr
  | Term.LetIn (name, expr, ty, body) ->
      (scan_callsites_rec false context expr;
      scan_callsites_rec tail (None :: context) body)
  | Term.App (f, argsary) ->
      ((match Term.kind_of_term f with
      | Term.Rel i -> found_callsite tail context i (Array.length argsary)
      | _ -> scan_callsites_rec false context f);
      Array.iter (scan_callsites_rec false context) argsary)
  | Term.Case (ci, tyf, expr, brs) ->
      (scan_callsites_rec false context expr;
      array_iter2
        (fun nargs br ->
          let context2 = ncons nargs None context in
          let br2 = snd (strip_outer_lambdas nargs br) in
          scan_callsites_rec tail context2 br2)
        ci.Constr.ci_cstr_nargs brs)
  | Term.Proj (proj, expr) ->
      scan_callsites_rec false context expr
  | _ -> errorlabstrm "scan_callsites_rec" (hv 0 (str "unexpected term:" ++ spc () ++ Printer.pr_constr term))

let scan_callsites i ntfcb_ary =
  let context = Array.to_list (array_rev (Array.mapi
    (fun j (nm, ty, fargs, ctx, body) ->
      Some (List.length fargs, ref (j = i), ref false, ref false))
    ntfcb_ary))
  in
  Array.iter
    (fun (nm, ty, fargs, ctx, body) ->
      scan_callsites_rec true (ncons (List.length fargs) None context) body)
    ntfcb_ary;
  Array.map
    (fun callsites_opt ->
      match callsites_opt with
      | Some (nargs, headcall, tailcall, partcall) -> (!headcall, !tailcall, !partcall)
      | None -> assert false)
    (array_rev (Array.of_list context))

let genc_func_single fname ty fargs context body =
  (*let (ty, fargs, context, body) = fargs_and_body fname term in*)
  let (argtys, rety) = argtys_and_rety_of_type ty in
  (if List.length argtys <> List.length fargs then
    error ("function value not supported yet: " ^
      string_of_int (List.length argtys) ^ " prods and " ^
      string_of_int (List.length fargs) ^ " lambdas"));
  let fname_argn = funcname_argnum fname (List.length argtys) in
  hvb 0 ++
  str (c_mangle_type rety) ++ spc () ++
  str fname_argn ++ str "(" ++
  hv 0 (genc_fargs fargs) ++
  str ")" ++ spc () ++
  str "{" ++ brk (1,2) ++
  hv 0 (
    genc_body_tail context body) ++
  spc () ++ str "}" ++
  close ()

let find_headcalls ntfcb_ary callsites_ary =
  Array.concat
    (Array.to_list
      (array_map2
        (fun ntfcb (headcall, tailcall, partcall) ->
          if headcall then [| ntfcb |] else [| |])
        ntfcb_ary callsites_ary))

let genc_mufun_struct_one ntfcb =
  let nm, ty, fargs, context, body = ntfcb in
  hvb 0 ++
  str "struct" ++ spc () ++
  str nm ++ spc () ++
  str "{" ++ spc () ++
  pp_postjoin_list (str ";" ++ spc ()) (List.map genc_farg fargs) ++
  str "};" ++
  close ()

let genc_mufun_structs ntfcb_ary callsites_ary =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.map genc_mufun_struct_one ntfcb_ary2)

let genc_mufun_entry mfnm i ntfcb =
  let nm, ty, fargs, context, body = ntfcb in
  let (argtys, rety) = nargtys_and_rety_of_type (List.length fargs) ty in
  let fname_argn = funcname_argnum nm (List.length argtys) in
  hvb 0 ++
  str (c_mangle_type rety) ++ spc () ++
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
    hv 0 (str (c_mangle_type rety) ++ spc () ++ str "ret;") ++ spc () ++
    hv 0 (str mfnm ++ str "(" ++ int i ++ str "," ++ spc () ++ str "&args," ++ spc () ++ str "&ret);") ++ spc () ++
    hv 0 (str "return" ++ spc () ++ str "ret;")) ++
  spc () ++ str "}" ++
  close ()

let genc_mufun_entries mfnm ntfcb_ary callsites_ary =
  let ntfcb_ary2 = find_headcalls ntfcb_ary callsites_ary in
  pp_join_ary (spc ())
    (Array.mapi (genc_mufun_entry mfnm) ntfcb_ary2)

let genc_mufun_forward_decl mfnm =
  hvb 0 ++
  str "void" ++ spc () ++
  str mfnm ++ str "(" ++
  hv 0 (
    hv 0 (str "int" ++ spc () ++ str "i") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "argsp") ++ str "," ++ spc () ++
    hv 0 (str "void*" ++ spc () ++ str "retp")) ++ str ");" ++
  close ()

let genc_mufun_bodies_func mfnm i ntfcb_ary callsites_ary =
  hvb 0 ++
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
        (fun (nm, ty, fargs, context, body) ->
           pp_join_list (spc ())
             (List.map
               (fun (var, ty) -> hv 0 (str (c_mangle_type ty) ++ spc () ++ str var ++ str ";"))
               fargs))
        ntfcb_ary) ++ spc () ++
    hv 0 (str "switch" ++ spc () ++ str "(i)") ++ spc () ++ str "{" ++ brk (1,2) ++
      hv 0 (
        pp_join_ary (spc ())
          (Array.mapi
            (fun j (nm, ty, fargs, context, body) ->
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
                  genc_body_void_tail ("(*(" ^ c_mangle_type rety ^ " *)retp)") context body ++ spc () ++
                  str "return;")))
            ntfcb_ary)) ++ spc () ++ str "}") ++ spc () ++
    str "}" ++
    close ()

let genc_mufun_single_func mfnm i ntfcb_ary callsites_ary =
  let entry_nm, entry_ty, entry_fargs, entry_context, entry_body = ntfcb_ary.(i) in
  let (entry_argtys, entry_rety) = nargtys_and_rety_of_type (List.length entry_fargs) entry_ty in
  let entry_fname_argn = funcname_argnum entry_nm (List.length entry_argtys) in
  hvb 0 ++
  str (c_mangle_type entry_rety) ++ spc () ++
  str entry_fname_argn ++ str "(" ++
  hv 0 (genc_fargs entry_fargs) ++
  str ")" ++ spc () ++
  str "{" ++ brk (1,2) ++
  hv 0 (
    pp_postjoin_ary (spc ())
      (Array.mapi
        (fun j (nm, ty, fargs, context, body) ->
          if j = i then
            mt ()
          else
            pp_join_list (spc ())
              (List.map
                (fun (var, ty) -> hv 0 (str (c_mangle_type ty) ++ spc () ++ str var ++ str ";"))
                fargs))
        ntfcb_ary) ++
    (if i = 0 then mt () else hv 0 (str "goto" ++ spc () ++ str entry_fname_argn ++ str ";") ++ spc ()) ++
    pp_join_ary (spc ())
      (Array.mapi
        (fun j (nm, ty, fargs, context, body) ->
          let headcall, tailcall, partcall = callsites_ary.(j) in
          let (argtys, rety) = nargtys_and_rety_of_type (List.length fargs) ty in
          let fname_argn = funcname_argnum nm (List.length argtys) in
          hv 0 (
            (if tailcall || (i <> 0 && i == j) then str fname_argn ++ str ":;" ++ spc () else mt ()) ++
            genc_body_tail context body))
        ntfcb_ary)) ++
  spc () ++ str "}" ++
  close ()

let genc_func_mutual mfnm i ntfcb_ary callsites_ary =
  let num_entry_funcs = Array.fold_left (+) 0 (Array.map (fun (headcall, tailcall, partcall) -> if headcall then 1 else 0) callsites_ary) in
  if num_entry_funcs = 1 then
    genc_mufun_single_func mfnm i ntfcb_ary callsites_ary
  else
    genc_mufun_structs ntfcb_ary callsites_ary ++ spc () ++
    genc_mufun_forward_decl mfnm ++ spc () ++
    genc_mufun_entries mfnm ntfcb_ary callsites_ary ++ spc () ++
    genc_mufun_bodies_func mfnm i ntfcb_ary callsites_ary

let genc_func fname ty term =
  match Term.kind_of_term term with
  | Term.Fix ((ia, i), (nameary, tyary, funary)) ->
      let ntfcb_ary = fargs_and_body_ary fname ty ia i nameary tyary funary in
      let callsites_ary = scan_callsites i ntfcb_ary in
      let mfnm = gensym_with_str fname in
      genc_func_mutual mfnm i ntfcb_ary callsites_ary
  | _ ->
      let fargs, body = fargs_and_body term in
      let context = List.rev_map (fun (var, ty) -> CtxVar var) fargs in
      genc_func_single fname ty fargs context body

let get_name_type_body (name : Libnames.reference) =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef ctnt ->
      begin match Global.body_of_constant ctnt with
      | Some b ->
          let name = Label.to_string (KerName.label (Constant.canonical ctnt)) in
          let ty = Global.type_of_global_unsafe reference in
          (name, ty, b)
      | None -> error "can't genc axiom"
      end
  | VarRef _ -> error "can't genc VarRef"
  | IndRef _ -> error "can't genc IndRef"
  | ConstructRef _ -> error "can't genc ConstructRef"

let genc libref_list =
  List.iter
    (fun libref ->
      let (name, ty, body) = get_name_type_body libref in
      let pp = genc_func name ty body in
      Feedback.msg_info pp)
    libref_list

let genc_file fn libref_list =
  (let ch = open_out fn in
  let fmt = Format.formatter_of_out_channel ch in
  List.iter
    (fun libref ->
      let (name, ty, body) = get_name_type_body libref in
      let pp = (genc_func name ty body) ++ Pp.fnl () in
      Pp.pp_with fmt pp)
    libref_list;
  Format.pp_flush_formatter fmt;
  close_out ch;
  Feedback.msg_info (str ("file generated: " ^ fn)))
