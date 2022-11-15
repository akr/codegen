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
open Constr
open EConstr

open Cgenutil
open State
open Induc
open Specialize

type body_root_t =
| BodyRootTopfunc of (bool * string) (* (static, primary_cfunc) *)
| BodyRootClosure of Id.t (* closure_id *)
| BodyRootFixfunc of Id.t (* fixfunc_id *)

type body_var_t =
| BodyVarFixfunc of Id.t (* fixfunc_id *)
| BodyVarArg of (string * c_typedata)
| BodyVarVoidArg of (string * c_typedata)

type bodyhead_t = {
  bodyhead_root : body_root_t;
  bodyhead_vars : body_var_t list; (* outermost first (left to right) *)
  bodyhead_return_type : c_typedata;
}

type genchunk_t = {
  genchunk_bodyhead_list : bodyhead_t list;
  genchunk_env : Environ.env;
  genchunk_exp : EConstr.t;
  genchunk_fixfunc_impls : Id.Set.t;
  genchunk_fixfunc_gotos : Id.Set.t;
  genchunk_fixfunc_calls : Id.Set.t;
  genchunk_closure_impls : Id.Set.t;
}

type entry_type_t =
| EntryTypeTopfunc of (bool * string) (* (static, primary_cfunc) *)
| EntryTypeFixfunc of Id.t (* fixfunc_id *)
| EntryTypeClosure of Id.t (* closure_id *)

type entry_func_t = {
  entryfunc_type : entry_type_t;
  entryfunc_body : bodyhead_t;
}

type fixterm_t = {
  fixterm_id : Id.t;
  fixterm_inlinable : bool;
}

let _ = ignore (fun x -> x.fixterm_id)

type fixfunc_t = {
  fixfunc_fixterm : fixterm_t;
  fixfunc_id : Id.t;
  fixfunc_used_for_call : bool;
  fixfunc_used_for_goto : bool;
  fixfunc_bodyhead : bodyhead_t;
  fixfunc_formal_arguments_without_void : (string * c_typedata) list; (* [(varname1, vartype1); ...] *) (* vartype is not void *)
  fixfunc_is_higher_order : bool; (* means that arguments contain function *)

  fixfunc_topfunc : (bool * string) option; (* (static, cfunc_name) *)
  fixfunc_sibling : (bool * string) option; (* (static, cfunc_name) *)
  fixfunc_c_name : string;

  fixfunc_cfunc : (bool * string) option; (* (static, cfunc_name) *)

  fixfunc_extra_arguments : (string * c_typedata) list; (* [(varname1, vartype1); ...] *) (* vartype is not void *)
  (* extra arguments are mostly same for fix-bouded functions in a fix-term.
    However, they can be different for primary function and siblings.
    In such case, extra arguments are all bounded variables by lambda and let-in and not filtered. *)

  fixfunc_label : string option;
}

let _ = ignore (fun x -> x.fixfunc_bodyhead)

type fixfunc_table = (Id.t, fixfunc_t) Hashtbl.t

type sibling_t = {
  sibling_static : bool;
  sibling_cfunc : string;
  sibling_fixfunc_id : Id.t;
}

let primary_entry_label (c_name : string) : string = "entry_" ^ c_name
let sibling_entry_label (c_name : string) : string = "entry_" ^ c_name
let fixfunc_entry_label (c_name : string) : string = c_name (* fixfuncs has already unique prefix, "fixfuncN_" *)
let fixfunc_exit_label (c_name : string) : string = "exit_" ^ c_name

let cfunc_of_fixfunc (fixfunc : fixfunc_t) : string =
  snd (Option.get fixfunc.fixfunc_cfunc)

type closure_t = {
  closure_id : Id.t;
  closure_c_name : string;
  closure_c_func_type : c_typedata;
  closure_args : (string * c_typedata) list;
  closure_vars : (string * c_typedata) list;
  closure_label : string option;
}
type closure_table = (Id.t, closure_t) Hashtbl.t

let closure_struct_tag clo = "codegen_closure_struct_"^clo.closure_c_name
let closure_struct_type clo = { c_type_left="struct "^(closure_struct_tag clo); c_type_right="" }
let closure_entry_function_prefix = "codegen_closre_entry_"
let closure_func_name clo = closure_entry_function_prefix^clo.closure_c_name
let closure_entry_label (c_name : string) : string = "closure_entry_" ^ c_name

let closure_args_struct_type (c_name : string) : string =
  "struct codegen_closure_args_" ^ c_name

let fixfunc_args_struct_type (c_name : string) : string =
  "struct codegen_fixfunc_args_" ^ c_name

let topfunc_args_struct_type (c_name : string) : string =
  "struct codegen_topfunc_args_" ^ c_name

let body_function_name (primary_cfunc : string) : string =
  "codegen_body_function_" ^ primary_cfunc

let get_closure_id (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Id.t =
  match EConstr.kind sigma term with
  | Lambda (x,t,b) ->
      (* Since codegen renames variables uniquely, the name of argument (x) is unique to identify this closure. *)
      id_of_annotated_name x
  | Fix ((ks, j), (nary, tary, fary)) ->
      id_of_annotated_name nary.(j)
  | _ ->
      user_err (Pp.str "[codegen:bug] unexpected closure term:" +++ Printer.pr_econstr_env env sigma term)

let pr_args (arg : (string * c_typedata) list) : Pp.t =
  Pp.str "[" ++
  pp_joinmap_list (Pp.str ",")
    (fun (x,t) -> Pp.str "(" ++ Pp.str (compose_c_decl t x) ++ Pp.str ")")
    arg ++
  Pp.str "]"

let show_fixfunc_table (env : Environ.env) (sigma : Evd.evar_map) (fixfunc_tbl : fixfunc_table) : unit =
  Hashtbl.iter
    (fun fixfunc_id fixfunc ->
      msg_debug_hov (Pp.str "[codegen:show_fixfunc_table]" +++
        Pp.str (Id.to_string fixfunc_id) ++ Pp.str ":" +++
        Pp.v 0 (
        Pp.str "inlinable=" ++ Pp.bool fixfunc.fixfunc_fixterm.fixterm_inlinable +++
        Pp.str "used_for_call=" ++ Pp.bool fixfunc.fixfunc_used_for_call +++
        Pp.str "used_for_goto=" ++ Pp.bool fixfunc.fixfunc_used_for_goto +++
        Pp.str "formal_arguments_without_void=" ++ pr_args fixfunc.fixfunc_formal_arguments_without_void +++
        Pp.str "topfunc=" ++ (match fixfunc.fixfunc_topfunc with None -> Pp.str "None" | Some (static,cfunc) -> Pp.str ("Some(" ^ (if static then "true" else "false") ^ "," ^ cfunc ^ ")")) +++
        Pp.str "sibling=" ++ (match fixfunc.fixfunc_sibling with None -> Pp.str "None" | Some (static,cfunc) -> Pp.str ("Some(" ^ (if static then "true" else "false") ^ "," ^ cfunc ^ ")")) +++
        Pp.str "c_name=" ++ Pp.str fixfunc.fixfunc_c_name +++
        Pp.str "fixfunc_cfunc=" ++ (match fixfunc.fixfunc_cfunc with None -> Pp.str "None" | Some (static,cfunc) -> Pp.str ("Some(" ^ (if static then "true" else "false") ^ "," ^ cfunc ^ ")")) +++
        Pp.str "extra_arguments=(" ++ pp_joinmap_list (Pp.str ",") (fun (farg, c_ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str (compose_c_abstract_decl c_ty)) fixfunc.fixfunc_extra_arguments ++ Pp.str ")" +++
        Pp.str "fixfunc_label=" ++ Pp.str (match fixfunc.fixfunc_label with None -> "None" | Some s -> "(Some " ^ s ^ ")") +++
        Pp.mt ())
      ))
    fixfunc_tbl

let _ = ignore show_fixfunc_table

let show_genchunks (sigma : Evd.evar_map) (genchunks : genchunk_t list) : unit =
  msg_debug_hov (Pp.str "[codegen:show_genchunks]" +++
    pp_sjoinmap_list
      (fun genchunk ->
        Pp.hv 2 (
          Pp.hov 2 (Pp.str "bodyhead_list=[" ++
            Pp.hov 0 (
            pp_sjoinmap_list
              (fun bodyhead ->
                (match bodyhead.bodyhead_root with
                | BodyRootTopfunc (static,primary_cfunc) -> Pp.str ("Topfunc:" ^ primary_cfunc ^ if static then "(static)" else "")
                | BodyRootFixfunc fixfunc_id -> Pp.str ("Fixfunc:" ^ Id.to_string fixfunc_id)
                | BodyRootClosure closure_id -> Pp.str ("Closure:" ^ Id.to_string closure_id)
                ) ++
                Pp.str "[" ++
                Pp.hov 0 (
                pp_sjoinmap_list
                  (fun bodyvar ->
                    match bodyvar with
                    | BodyVarFixfunc fixfunc_id -> Pp.str "Fixfunc:" ++ Id.print fixfunc_id
                    | BodyVarArg (var, c_ty) -> Pp.str "Arg:" ++ Pp.str var ++ Pp.str ":" ++ pr_c_abstract_decl c_ty
                    | BodyVarVoidArg (var, c_ty) -> Pp.str "VoidArg:" ++ Pp.str var ++ Pp.str ":" ++ pr_c_abstract_decl c_ty)
                  bodyhead.bodyhead_vars) ++
                Pp.str "]" ++
                Pp.str "[" ++
                pr_c_abstract_decl bodyhead.bodyhead_return_type ++
                Pp.str "]")
              genchunk.genchunk_bodyhead_list)
            ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "fixfunc_impls=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements genchunk.genchunk_fixfunc_impls) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "fixfunc_gotos=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements genchunk.genchunk_fixfunc_gotos) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "fixfunc_calls=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements genchunk.genchunk_fixfunc_calls) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "closure_impls=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements genchunk.genchunk_closure_impls) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "genchunk=" +++ Printer.pr_econstr_env genchunk.genchunk_env sigma genchunk.genchunk_exp)
          ))
      genchunks)

let _ = ignore show_genchunks

let rec fix_body_list (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) :
    (((*env including fixfunc names but without lambdas of fixfunc*)Environ.env *
      (*env including fixfunc names and lambdas of fixfunc*)Environ.env *
      (*fixfunc name*)Names.Name.t Context.binder_annot *
      (*fixfunc type*)EConstr.types *
      (*fargs*)(Names.Name.t Context.binder_annot * EConstr.types) list) list *
     ((*env for body*)Environ.env *
      (*body*)EConstr.t)) list =
  match EConstr.kind sigma term with
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ntfary = CArray.map3 (fun n t f -> (n,t,f)) nary tary fary in
      let ntf_j = ntfary.(j) in
      Array.blit ntfary 0 ntfary 1 j; ntfary.(0) <- ntf_j; (* move ntfary.(j) to the beginning *)
      List.concat_map
        (fun (n,t,f) ->
          let (f_fargs, f_body) = decompose_lam sigma f in
          let env3 = env_push_assums env2 f_fargs in
          let l = fix_body_list env3 sigma f_body in
          match l with
          | [] -> assert false
          | (context, env_body) :: rest ->
              ((env2,env3,n,t,f_fargs)::context, env_body) :: rest)
        (Array.to_list ntfary)
  | _ ->
      [([], (env, term))]

let rec c_args_and_ret_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((string * c_typedata) list) * c_typedata =
  match EConstr.kind sigma term with
  | Prod (x,t,b) ->
      let env2 = env_push_assum env x t in
      let (rest_args, ret_type) = c_args_and_ret_type env2 sigma b in
      (((str_of_annotated_name x, c_typename env sigma t) :: rest_args), ret_type)
  | _ ->
      ([], c_typename env sigma term)

let c_args_without_void_and_ret_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((string * c_typedata) list) * c_typedata =
  let (args, ret) = c_args_and_ret_type env sigma term in
  let args_without_void = List.filter (fun (var, c_ty) -> not (c_type_is_void c_ty)) args in
  (args_without_void, ret)

let rec make_fixterm_tbl (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (Environ.env * EConstr.t) Id.Map.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:make_fixterm_tbl] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:make_fixterm_tbl] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel _ -> Id.Map.empty
  | Const _ | Construct _ -> Id.Map.empty
  | Proj _ -> Id.Map.empty
  | App (f, args) ->
      make_fixterm_tbl env sigma f
  | LetIn (x,e,t,b) ->
      let env2 = env_push_def env x e t in
      let m1 = make_fixterm_tbl env sigma e in
      let m2 = make_fixterm_tbl env2 sigma b in
      disjoint_id_map_union m1 m2
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let ms = Array.map2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          make_fixterm_tbl env2 sigma body)
        bl bl0
      in
      disjoint_id_map_union_ary ms
  | Lambda (x,t,b) ->
      let env2 = env_push_assum env x t in
      make_fixterm_tbl env2 sigma b
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let tbls = Array.map (make_fixterm_tbl env2 sigma) fary in
      let tbl = disjoint_id_map_union_ary tbls in
      let fixterm_id = id_of_annotated_name nary.(j) in
      Id.Map.add fixterm_id (env, term) tbl

let make_fixfunc_fixterm_tbl (sigma : Evd.evar_map) ~(fixterm_tbl : (Environ.env * EConstr.t) Id.Map.t) : Id.t Id.Map.t =
  Id.Map.fold
    (fun fixterm_id (env,term) tbl ->
      let ((ks, j), (nary, tary, fary)) = destFix sigma term in
      Array.fold_left
        (fun tbl x -> Id.Map.add (id_of_annotated_name x) fixterm_id tbl)
        tbl nary)
    fixterm_tbl
    Id.Map.empty

(*
  Currently only closures are represented as a pointer to stack-allocated data.
  A pointer to stack-allocated data cannot return (because returning deallocates the stack frame).
  Also, it cannot pass to argument of tail recursive call if it is translated to goto.
  It is because the closure can be overwritten after goto.
  (Conceptually, the stack frame is deallocated at goto.)
  Thus, codegen disables tail recursion elimination if argments of a fixfunc contains function.
*)
let rec is_higher_order_function (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  match EConstr.kind sigma ty with
  | Prod (x,t,b) ->
      (match Linear.component_types env sigma t with
      | None -> true (* function found *)
      | Some _ ->
          let env2 = env_push_assum env x t in
          is_higher_order_function env2 sigma b)
  | _ -> false

let make_higher_order_fixfunc_tbl (sigma : Evd.evar_map) ~(fixterm_tbl : (Environ.env * EConstr.t) Id.Map.t) : bool Id.Map.t =
  Id.Map.fold
    (fun fixterm_id (env,term) tbl ->
      let ((ks, j), (nary, tary, fary)) = destFix sigma term in
      CArray.fold_left2
        (fun tbl x t -> Id.Map.add (id_of_annotated_name x) (is_higher_order_function env sigma t) tbl)
        tbl nary tary)
    fixterm_tbl
    Id.Map.empty

(*
  make_inlinable_fixterm_tbl implementes TR[term]_numargs in doc/codegen.tex.
*)
(*
  make_inlinable_fixterm_tbl_rec implements (R,N,T) = RNT[term] in doc/codegen.tex.
  R is a map from fix-bounded IDs to bool.
  R[n] = true if n is fix-bounded function which is inlinable (only used for goto so do not need to be a real function).
  R[n] = false if n is fix-bounded function not inlinable.
  R can also be usable to determine an ID is fix-bounded function or not.
*)
let make_inlinable_fixterm_tbl ~(higher_order_fixfunc_tbl : bool Id.Map.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool Id.Map.t =
  let rec make_inlinable_fixterm_tbl_lamfix (env : Environ.env) (term : EConstr.t) :
      (* this lambda/fix is inlinable or not *) bool *
      (* fixterms inlinable or not *) bool Id.Map.t *
      (* variables at non-tail position *) IntSet.t *
      (* variables at tail position *) IntSet.t =
    (*msg_debug_hov (Pp.str "[codegen:make_inlinable_fixterm_tbl_lamfix] start:" +++
      Printer.pr_econstr_env env sigma term); *)
    let result = make_inlinable_fixterm_tbl_lamfix1 env term in
    (*
    let (tailrec_fixfuncs, nontailset, tailset) = result in
    msg_debug_hov (Pp.str "[codegen:make_inlinable_fixterm_tbl_lamfix] end:" +++
      Printer.pr_econstr_env env sigma term +++
      Pp.str "inlinable-fixterms={" ++
      pp_sjoinmap_list
        (fun (fixfunc_id, inlinable) ->
          if inlinable then
            Id.print fixfunc_id
          else
            Pp.mt ())
        (Id.Map.bindings tailrec_fixfuncs) ++
      Pp.str "}" +++
      Pp.str "non-inlinable-fixterms={" ++
      pp_sjoinmap_list
        (fun (fixfunc_id, inlinable) ->
          if inlinable then
            Pp.mt ()
          else
            Id.print fixfunc_id)
        (Id.Map.bindings tailrec_fixfuncs) ++
      Pp.str "}" +++
      Pp.str "nontailset={" ++
      pp_joinmap_list (Pp.str ",")
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name)
        (IntSet.elements nontailset) ++
      Pp.str "}" +++
      Pp.str "tailset={" ++
      pp_joinmap_list (Pp.str ",")
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name
          )
        (IntSet.elements tailset) ++
      Pp.str "}");
      *)
    result
  and make_inlinable_fixterm_tbl_lamfix1 (env : Environ.env) (term : EConstr.t) :
      (* this lambda/fix is inlinable or not *) bool *
      (* fixterms inlinable or not *) bool Id.Map.t *
      (* variables at non-tail position *) IntSet.t *
      (* variables at tail position *) IntSet.t =
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:make_inlinable_fixterm_tbl_lamfix] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ ->
        user_err (Pp.str "[codegen:make_inlinable_fixterm_tbl_lamfix] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Lambda (x,t,b) ->
        let env2 = env_push_assum env x t in
        let (inlinable_here, inlinablemap_b, nontailset_b, tailset_b) = make_inlinable_fixterm_tbl_lamfix env2 b in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        (inlinable_here, inlinablemap_b, nontailset_b, tailset_b)
    | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
        let h = Array.length nary in
        let env2 = EConstr.push_rec_types prec env in
        let fixfuncs_result = Array.map (make_inlinable_fixterm_tbl_lamfix env2) fary in
        let inlinable_here_fs = Array.for_all (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> inlinable_here) fixfuncs_result in
        let tailset_fs = intset_union_ary (Array.map (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> tailset_f) fixfuncs_result) in
        let nontailset_fs = intset_union_ary (Array.map (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> nontailset_f) fixfuncs_result) in
        let inlinablemap_fs = disjoint_id_map_union_ary (Array.map (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> inlinablemap_f) fixfuncs_result) in
        let fixfunc_referenced_at_nontail_position = IntSet.exists ((>=) h) nontailset_fs in
        let tailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) tailset_fs) in
        let nontailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) nontailset_fs) in
        let fixterm_is_higher_order = Array.exists (fun x -> Id.Map.find (id_of_annotated_name x) higher_order_fixfunc_tbl) nary in
        if not inlinable_here_fs ||
           fixfunc_referenced_at_nontail_position ||
           fixterm_is_higher_order then
          (* At least one fix-bounded function is used at
            non-tail position or argument position.
            Or, at least one fix-bounded function has a function in arguments.
            Assuming fix-bounded functions are strongly-connected,
            there is no tail position in this fix-term. *)
          let nontailset = IntSet.union tailset_fs' nontailset_fs' in
          let inlinablemap_fs' =
            Array.fold_left
              (fun fs name -> Id.Map.add (id_of_annotated_name name) false fs)
              inlinablemap_fs
              nary
          in
          (false, inlinablemap_fs', nontailset, IntSet.empty)
        else
          let inlinablemap_fs' =
            Array.fold_left
              (fun fs name -> Id.Map.add (id_of_annotated_name name) true fs)
              inlinablemap_fs
              nary
          in
          (true, inlinablemap_fs', nontailset_fs', tailset_fs')
    | _ ->
        let (inlinablemap, nontailset, tailset) = make_inlinable_fixterm_tbl_exp env term in
        (true, inlinablemap, nontailset, tailset)
  and make_inlinable_fixterm_tbl_exp (env : Environ.env) (term : EConstr.t) :
      (* fixterms inlinable or not *) bool Id.Map.t *
      (* variables at non-tail position *) IntSet.t *
      (* variables at tail position *) IntSet.t =
    (*msg_debug_hov (Pp.str "[codegen:make_inlinable_fixterm_tbl_exp] start:" +++
      Printer.pr_econstr_env env sigma term); *)
    let result = make_inlinable_fixterm_tbl_exp1 env term in
    (*
    let (tailrec_fixfuncs, nontailset, tailset) = result in
    msg_debug_hov (Pp.str "[codegen:make_inlinable_fixterm_tbl_exp] end:" +++
      Printer.pr_econstr_env env sigma term +++
      Pp.str "inlinable-fixterms={" ++
      pp_sjoinmap_list
        (fun (fixfunc_id, inlinable) ->
          if inlinable then
            Id.print fixfunc_id
          else
            Pp.mt ())
        (Id.Map.bindings tailrec_fixfuncs) ++
      Pp.str "}" +++
      Pp.str "non-inlinable-fixterms={" ++
      pp_sjoinmap_list
        (fun (fixfunc_id, inlinable) ->
          if inlinable then
            Pp.mt ()
          else
            Id.print fixfunc_id)
        (Id.Map.bindings tailrec_fixfuncs) ++
      Pp.str "}" +++
      Pp.str "nontailset={" ++
      pp_joinmap_list (Pp.str ",")
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name)
        (IntSet.elements nontailset) ++
      Pp.str "}" +++
      Pp.str "tailset={" ++
      pp_joinmap_list (Pp.str ",")
        (fun i ->
          let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
          Pp.int i ++ Pp.str "=" ++ Name.print name
          )
        (IntSet.elements tailset) ++
      Pp.str "}");
      *)
    result
  and make_inlinable_fixterm_tbl_exp1 (env : Environ.env) (term : EConstr.t) :
      (* fixterms inlinable or not *) bool Id.Map.t *
      (* variables at non-tail position *) IntSet.t *
      (* variables at tail position *) IntSet.t =
    let (term, args) = decompose_appvect sigma term in
    (if not (CArray.is_empty args) then
      match EConstr.kind sigma term with
      | Rel _ | Const _ | Construct _ | Fix _ -> ()
      | _ -> user_err (Pp.str "[codegen] unexpected term in function position:" +++ Printer.pr_econstr_env env sigma term));
    let args_set = Array.fold_left (fun set arg -> IntSet.add (destRel sigma arg) set) IntSet.empty args in
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:make_inlinable_fixterm_tbl_exp] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
        user_err (Pp.str "[codegen:make_inlinable_fixterm_tbl_exp] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Rel i -> (Id.Map.empty, args_set, IntSet.singleton i)
    | Const _ | Construct _ -> (Id.Map.empty, args_set, IntSet.empty)
    | Proj (proj, e) ->
        (* e must be a Rel which type is inductive (non-function) type *)
        (Id.Map.empty, IntSet.empty, IntSet.empty)
    | LetIn (x,e,t,b) ->
        let env2 = env_push_def env x e t in
        let (inlinablemap_e, nontailset_e, tailset_e) = make_inlinable_fixterm_tbl_exp env e in
        let (inlinablemap_b, nontailset_b, tailset_b) = make_inlinable_fixterm_tbl_exp env2 b in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        let nontailset = intset_union3 tailset_e nontailset_e nontailset_b in
        let inlinablemap = disjoint_id_map_union inlinablemap_e inlinablemap_b in
        (inlinablemap, nontailset, tailset_b)
    | Case (ci,u,pms,p,iv,item,bl) ->
        let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
        (* item cannot contain fix-term because item must be a Rel which type is inductive (non-function) type *)
        let branches_result = Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            let n = Array.length nas in
            let (inlinablemap_br, nontailset_br, tailset_br) = make_inlinable_fixterm_tbl_exp env2 body in
            let tailset_br = IntSet.map (fun i -> i - n) (IntSet.filter ((<) n) tailset_br) in
            let nontailset_br = IntSet.map (fun i -> i - n) (IntSet.filter ((<) n) nontailset_br) in
            (inlinablemap_br, nontailset_br, tailset_br))
          bl bl0
        in
        let tailset = intset_union_ary (Array.map (fun (inlinablemap_br, nontailset_br, tailset_br) -> tailset_br) branches_result) in
        let nontailset = intset_union_ary (Array.map (fun (inlinablemap_br, nontailset_br, tailset_br) -> nontailset_br) branches_result) in
        let inlinablemap = disjoint_id_map_union_ary (Array.map (fun (inlinablemap_br, nontailset_br, tailset_br) -> inlinablemap_br) branches_result) in
        (inlinablemap, nontailset, tailset)
    | Lambda _ ->
        if CArray.is_empty args then (* closure creation *)
          let (inlinable_here, inlinablemap, nontailset, tailset) = make_inlinable_fixterm_tbl_lamfix env term in
          let nontailset' = IntSet.union tailset nontailset in
          (inlinablemap, nontailset', IntSet.empty)
        else
          assert false
    | Fix _ ->
        if CArray.is_empty args then (* closure creation *)
          let (inlinable_here, inlinablemap, nontailset, tailset) = make_inlinable_fixterm_tbl_lamfix env term in
          let nontailset' = IntSet.union tailset nontailset in
          (inlinablemap, nontailset', IntSet.empty)
        else
          let (inlinable_here, inlinablemap, nontailset, tailset) = make_inlinable_fixterm_tbl_lamfix env term in
          (inlinablemap, IntSet.union nontailset args_set, tailset)
  in
  let (inlinable_here, inlinablemap, nontailset, tailset) = make_inlinable_fixterm_tbl_lamfix env term in
  inlinablemap

let determine_fixfunc_call_or_goto (tail_position : bool) (fixfunc_is_higher_order : bool) (fixterm_is_inlinable : bool)
    ~call:(thunk_for_call : unit -> 'a) ~goto:(thunk_for_goto : unit -> 'a) : 'a =
  if tail_position then
    if fixfunc_is_higher_order then
      thunk_for_call ()
    else
      thunk_for_goto ()
  else
    if fixterm_is_inlinable then
      thunk_for_goto ()
    else
      thunk_for_call ()

let bodyhead_fargs (bodyhead : bodyhead_t) : (string * c_typedata) list =
  let { bodyhead_root=bodyroot; bodyhead_vars=bodyvars } = bodyhead in
  List.filter_map (function BodyVarArg (var, c_ty) -> Some (var, c_ty) | _ -> None) bodyvars

let bodyhead_fixfunc_fargs_with_void (bodyhead : bodyhead_t) (fixfunc_id : Id.t) : (string * c_typedata) list =
  let pred = function BodyVarFixfunc var_fixfunc_id -> Id.equal var_fixfunc_id fixfunc_id | _ -> false in
  let vars = List.tl (list_find_suffix pred bodyhead.bodyhead_vars) in
  List.filter_map
    (function
      | BodyVarArg (var, c_ty) -> Some (var, c_ty)
      | BodyVarVoidArg (var, c_ty) -> Some (var, c_ty)
      | BodyVarFixfunc fixfunc_id -> None)
    vars

let bodyhead_fixfunc_fargs_without_void (bodyhead : bodyhead_t) (fixfunc_id : Id.t) : (string * c_typedata) list =
  let pred = function BodyVarFixfunc var_fixfunc_id -> Id.equal var_fixfunc_id fixfunc_id | _ -> false in
  let vars = List.tl (list_find_suffix pred bodyhead.bodyhead_vars) in
  List.filter_map
    (function
      | BodyVarArg (var, c_ty) -> Some (var, c_ty)
      | BodyVarVoidArg (var, c_ty) -> None
      | BodyVarFixfunc fixfunc_id -> None)
    vars

let _ = ignore bodyhead_fixfunc_fargs_with_void

let obtain_function_genchunks
    ~(higher_order_fixfunc_tbl : bool Id.Map.t) ~(inlinable_fixterm_tbl : bool Id.Map.t)
    ~(static_and_primary_cfunc : bool * string)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    genchunk_t list =
  let rec obtain_function_genchunks_lamfix ~(tail_position : bool) ~(individual_body : bool) ~(bodyroot : body_root_t) ~(bodyvars : body_var_t list) (env : Environ.env) (term : EConstr.t) :
      (genchunk_t Seq.t * (*genchunk_bodyhead_list*)bodyhead_t list * (*fixfunc_impls*)Id.Set.t * (*fixfunc_gotos*)Id.Set.t * (*fixfunc_calls*)Id.Set.t * (*closurr_defs*)Id.Set.t) =
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:obtain_function_genchunks_lamfix] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ ->
        user_err (Pp.str "[codegen:obtain_function_genchunks_lamfix] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Lambda (x,t,b) ->
        let env2 = env_push_assum env x t in
        let bodyvars2 =
          let c_ty = c_typename env sigma t in
          if c_type_is_void c_ty then
            BodyVarVoidArg (str_of_annotated_name x, c_ty) :: bodyvars
          else
            BodyVarArg (str_of_annotated_name x, c_ty) :: bodyvars
        in
        obtain_function_genchunks_lamfix ~tail_position ~individual_body ~bodyroot ~bodyvars:bodyvars2 env2 b
    | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
        let env2 = EConstr.push_rec_types prec env in
        let h = Array.length nary in
        let nary' = Array.init h (fun i -> if i = 0 then nary.(j) else if i <= j then nary.(i-1) else nary.(i)) in
        (*let tary' = Array.init h (fun i -> if i = 0 then tary.(j) else if i <= j then tary.(i-1) else tary.(i)) in*)
        let fary' = Array.init h (fun i -> if i = 0 then fary.(j) else if i <= j then fary.(i-1) else fary.(i)) in
        let result_ary =
          (CArray.map2_i
            (fun i x f ->
              let fixfunc_id = id_of_annotated_name x in
              if i = 0 then
                let bodyvars2 = BodyVarFixfunc fixfunc_id :: bodyvars in
                obtain_function_genchunks_lamfix ~tail_position ~individual_body ~bodyroot ~bodyvars:bodyvars2 env2 f
              else
                let bodyroot2 = BodyRootFixfunc fixfunc_id in
                let bodyvars2 = [BodyVarFixfunc fixfunc_id] in
                obtain_function_genchunks_lamfix ~tail_position ~individual_body ~bodyroot:bodyroot2 ~bodyvars:bodyvars2 env2 f)
            nary' fary')
        in
        let genchunks = concat_array_seq (Array.map (fun (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> genchunks) result_ary) in
        let bodyhead_list = List.concat (CArray.map_to_list (fun (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> bodyhead_list) result_ary) in
        let fixfunc_impls0 = idset_union_ary (Array.map (fun (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_impls) result_ary) in
        let fixfunc_gotos = idset_union_ary (Array.map (fun (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_gotos) result_ary) in
        let fixfunc_calls = idset_union_ary (Array.map (fun (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_calls) result_ary) in
        let closure_impls = idset_union_ary (Array.map (fun (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> closure_impls) result_ary) in
        let fixfunc_impls = Id.Set.union fixfunc_impls0 (idset_of_array (Array.map id_of_annotated_name nary)) in
        (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
    | _ ->
        let (genchunks, bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = obtain_function_genchunks_body ~tail_position env term in
        let bodyhead_list2 = {
            bodyhead_root = bodyroot;
            bodyhead_vars = (List.rev bodyvars);
            bodyhead_return_type = c_typename env sigma (Reductionops.nf_all env sigma (Retyping.get_type_of env sigma term));
          } :: bodyhead_list in
        if individual_body then
          let fixfunc_ids =
            List.filter_map
              (fun bodyvar ->
                match bodyvar with
                | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
                | _ -> None)
              bodyvars
          in
          let genchunk = {
            genchunk_bodyhead_list = bodyhead_list2;
            genchunk_env = env;
            genchunk_exp = term;
            genchunk_fixfunc_impls = Id.Set.union (Id.Set.of_list fixfunc_ids) fixfunc_impls;
            genchunk_fixfunc_gotos = fixfunc_gotos;
            genchunk_fixfunc_calls = fixfunc_calls;
            genchunk_closure_impls = closure_impls;
          } in
          (Seq.cons genchunk genchunks, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
        else
          (genchunks, bodyhead_list2, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
  and obtain_function_genchunks_body ~(tail_position : bool) (env : Environ.env) (term : EConstr.t) :
      (genchunk_t Seq.t * (*bodyhead_list*)bodyhead_t list * (*fixfunc_impls*)Id.Set.t * (*fixfunc_gotos*)Id.Set.t * (*fixfunc_calls*)Id.Set.t * (*closurr_defs*)Id.Set.t) =
    let (term, args) = decompose_appvect sigma term in
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:obtain_function_genchunks_body] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
        user_err (Pp.str "[codegen:obtain_function_genchunks_body] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Rel i ->
        if CArray.is_empty args then
          (Seq.empty, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
        else (* application *)
          let id = id_of_name (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)) in
          let (fixfunc_gotos, fixfunc_calls) =
            match Id.Map.find_opt id higher_order_fixfunc_tbl with
            | None -> (Id.Set.empty, Id.Set.empty) (* closure call *)
            | Some fixfunc_is_higher_order ->
                let fixterm_is_inlinable = Id.Map.find id inlinable_fixterm_tbl in
                determine_fixfunc_call_or_goto tail_position fixfunc_is_higher_order fixterm_is_inlinable
                  ~call:(fun () -> (Id.Set.empty, Id.Set.singleton id))
                  ~goto:(fun () -> (Id.Set.singleton id, Id.Set.empty))
          in
          (Seq.empty, [], Id.Set.empty, fixfunc_gotos, fixfunc_calls, Id.Set.empty)
    | Const _ | Construct _ -> (Seq.empty, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
    | Proj (proj, e) -> (Seq.empty, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
    | LetIn (x,e,t,b) ->
        let env2 = env_push_def env x e t in
        let (genchunks1, body_entries1, fixfunc_impls1, fixfunc_gotos1, fixfunc_calls1, closure_impls1) = obtain_function_genchunks_body ~tail_position:false env e in
        let (genchunks2, body_entries2, fixfunc_impls2, fixfunc_gotos2, fixfunc_calls2, closure_impls2) = obtain_function_genchunks_body ~tail_position env2 b in
        (Seq.append genchunks1 genchunks2,
         List.append body_entries1 body_entries2,
         Id.Set.union fixfunc_impls1 fixfunc_impls2,
         Id.Set.union fixfunc_gotos1 fixfunc_gotos2,
         Id.Set.union fixfunc_calls1 fixfunc_calls2,
         Id.Set.union closure_impls1 closure_impls2)
    | Case (ci,u,pms,p,iv,item,bl) ->
        let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
        let result_ary =
          (Array.map2
            (fun (nas,body) (ctx,_) ->
              let env2 = EConstr.push_rel_context ctx env in
              obtain_function_genchunks_body ~tail_position env2 body)
            bl bl0)
        in
        let genchunks = concat_array_seq (Array.map (fun (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> genchunks) result_ary) in
        let genchunk_body_list = List.concat (CArray.map_to_list (fun (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> genchunk_body_list) result_ary) in
        let fixfunc_impls = idset_union_ary (Array.map (fun (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_impls) result_ary) in
        let fixfunc_gotos = idset_union_ary (Array.map (fun (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_gotos) result_ary) in
        let fixfunc_calls = idset_union_ary (Array.map (fun (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_calls) result_ary) in
        let closure_impls = idset_union_ary (Array.map (fun (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> closure_impls) result_ary) in
        (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
    | Lambda (x,t,b) ->
        if CArray.is_empty args then (* closure creation *)
          let cloid = get_closure_id env sigma term in
          let (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = obtain_function_genchunks_lamfix ~tail_position:true ~individual_body:true ~bodyroot:(BodyRootClosure cloid) ~bodyvars:[] env term in
          let closure_impls2 = Id.Set.add cloid closure_impls in
          (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls2)
        else
          assert false
    | Fix ((ks, j), ((nary, tary, fary))) ->
        if CArray.is_empty args then (* closure creation *)
          (let cloid = get_closure_id env sigma term in
          assert (not tail_position);
          let (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = obtain_function_genchunks_lamfix ~tail_position:true ~individual_body:true ~bodyroot:(BodyRootClosure cloid) ~bodyvars:[] env term in
          let closure_impls2 = Id.Set.add cloid closure_impls in
          (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls2))
        else
          let fixterm_id = id_of_annotated_name nary.(j) in
          let inlinable = Id.Map.find fixterm_id inlinable_fixterm_tbl in
          let (tail_position2, individual_body) =
            if not tail_position then
              if inlinable then
                (* inlinable fixpoint at head position causes inheritance of tail_position *)
                (false, false) (* A_K via GENBODY^{AT} *)
              else
                (true, true) (* B_K via GENBODY^{AN}: individual function will be generated *)
            else
              (true, false) (* B_K via GENBODY^{B} *)
          in
          let (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = obtain_function_genchunks_lamfix ~tail_position:tail_position2 ~individual_body ~bodyroot:(BodyRootFixfunc fixterm_id) ~bodyvars:[] env term in
          if individual_body then
            (genchunks, genchunk_body_list, Id.Set.empty, Id.Set.empty, Id.Set.singleton fixterm_id, Id.Set.empty)
          else
            (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
  in
  let (genchunks, genchunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = obtain_function_genchunks_lamfix ~tail_position:true ~individual_body:true ~bodyroot:(BodyRootTopfunc static_and_primary_cfunc) ~bodyvars:[] env term in
  let result = List.of_seq genchunks in
  (*show_genchunks sigma result;*)
  result

let make_used_for_call_set (genchunks : genchunk_t list) : Id.Set.t =
  idset_union_list (List.map (fun genchunk -> genchunk.genchunk_fixfunc_calls) genchunks)

let make_used_for_goto_set (genchunks : genchunk_t list) : Id.Set.t =
  idset_union_list (List.map (fun genchunk -> genchunk.genchunk_fixfunc_gotos) genchunks)

let make_fixfunc_bodyhead_tbl (genchunks : genchunk_t list) : bodyhead_t Id.Map.t =
  List.fold_left
    (fun tbl genchunk ->
      List.fold_left
        (fun tbl bodyhead ->
          List.fold_left
            (fun tbl bodyvar ->
              match bodyvar with
              | BodyVarFixfunc fixfunc_id ->
                  Id.Map.add fixfunc_id bodyhead tbl
              | _ -> tbl)
            tbl bodyhead.bodyhead_vars)
        tbl genchunk.genchunk_bodyhead_list)
    Id.Map.empty genchunks

let make_closure_bodyhead_tbl (genchunks : genchunk_t list) : bodyhead_t Id.Map.t =
  List.fold_left
    (fun tbl genchunk ->
      List.fold_left
        (fun tbl bodyhead ->
          match bodyhead.bodyhead_root with
          | BodyRootClosure closure_id -> Id.Map.add closure_id bodyhead tbl
          | _ -> tbl)
        tbl genchunk.genchunk_bodyhead_list)
    Id.Map.empty genchunks

let make_topfunc_tbl (sigma : Evd.evar_map) (term : EConstr.t) ~(static_and_primary_cfunc : bool * string) : (bool * string) Id.Map.t =
  let (fargs, term') = decompose_lam sigma term in
  match EConstr.kind sigma term' with
  | Fix ((ks, j), (nary, tary, fary)) ->
      let fixfunc_id = id_of_annotated_name nary.(j) in
      Id.Map.add fixfunc_id static_and_primary_cfunc Id.Map.empty
  | _ -> Id.Map.empty

let make_sibling_tbl (sibling_entfuncs : sibling_t list) : (bool * string) Id.Map.t =
  List.fold_left
    (fun sibling_tbl { sibling_static=static; sibling_cfunc=sibling_cfunc_name; sibling_fixfunc_id=fixfunc_id } ->
      Id.Map.add fixfunc_id (static, sibling_cfunc_name) sibling_tbl)
    Id.Map.empty
    sibling_entfuncs

let make_c_names_tbl
    ~(fixfunc_fixterm_tbl : Id.t Id.Map.t)
    ~(used_for_call_set : Id.Set.t)
    ~(topfunc_tbl : (bool * string) Id.Map.t)
    ~(sibling_tbl : (bool * string) Id.Map.t) : string Id.Map.t =
  idmap_of_list
    (List.map
      (fun (fixfunc_id, _) ->
        let c_name =
          match (Id.Map.find_opt fixfunc_id topfunc_tbl), (Id.Map.find_opt fixfunc_id sibling_tbl) with
          | Some (_,cfunc), _ -> cfunc
          | None, Some (_,cfunc) -> cfunc
          | None, None ->
              if Id.Set.mem fixfunc_id used_for_call_set then
                global_gensym_with_id fixfunc_id
              else
                Id.to_string fixfunc_id
        in
        (fixfunc_id, c_name))
      (Id.Map.bindings fixfunc_fixterm_tbl))

(*
  fixterm_free_variables computes variables which may be references at run time,
  for each fixterm.
  So it doesn't consider types of LetIn, Lambda and Fix,
  parameters, match predicates invert of Case.
*)

let rec fixterm_free_variables_rec (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) ~(result : (Id.t, Id.Set.t) Hashtbl.t) : Id.Set.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:fixterm_free_variables_rec] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:fixterm_free_variables_rec] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      let decl = Environ.lookup_rel i env in
      let name = Context.Rel.Declaration.get_name decl in
      Id.Set.singleton (id_of_name name)
  | Const _ | Construct _ -> Id.Set.empty
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
      let env2 = env_push_def env x e t in
      let id = id_of_annotated_name x in
      let fv_e = fixterm_free_variables_rec env sigma e ~result in
      let fv_b = fixterm_free_variables_rec env2 sigma b ~result in
      Id.Set.union fv_e (Id.Set.remove id fv_b)
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let item_id =
        let i = destRel sigma item in
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        id_of_name name
      in
      let fv_branches =
        Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            let fv_body = fixterm_free_variables_rec env2 sigma body ~result in
            let ids = Array.fold_left
              (fun ids annotated_name -> Id.Set.add (id_of_annotated_name annotated_name) ids)
              Id.Set.empty nas
            in
            Id.Set.diff fv_body ids)
          bl bl0
      in
      Array.fold_right Id.Set.union fv_branches (Id.Set.singleton item_id)
  | Lambda (x,t,b) ->
      let env2 = env_push_assum env x t in
      let id = id_of_annotated_name x in
      let fv_b = fixterm_free_variables_rec env2 sigma b ~result in
      Id.Set.remove id fv_b
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
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
      Hashtbl.add result (id_of_annotated_name nary.(j)) fv;
      fv

let fixterm_free_variables (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) : (Id.t, Id.Set.t) Hashtbl.t =
  let result = Hashtbl.create 0 in
  ignore (fixterm_free_variables_rec env sigma term ~result);
  result

let check_eq_extra_arguments exargs1 exargs2 =
  if exargs1 <> exargs2 then
    user_err (Pp.str "[codegen:bug] exargs length differ:" +++ pr_args exargs1 +++ Pp.str "<>" +++ pr_args exargs2)

let _ = ignore check_eq_extra_arguments

(*
  compute_naive_extra_arguments computes extra arguments in "naive" way:
  It contains all variables in env except fix-bounded functions.
  Note that the result is ordered from outside to inside of the term.
*)
let compute_naive_extra_arguments ~(fixfunc_fixterm_tbl : Id.t Id.Map.t) (env : Environ.env) (sigma : Evd.evar_map) : (string * c_typedata) list =
  let n = Environ.nb_rel env in
  let exargs = ref [] in
  for i = 1 to n do
    let decl = Environ.lookup_rel i env in
    let x = Context.Rel.Declaration.get_name decl in
    let t = Context.Rel.Declaration.get_type decl in
    let id = id_of_name x in
    if not (Id.Map.mem id fixfunc_fixterm_tbl) then (* Don't include fix-bounded functions *)
      let c_ty = c_typename env sigma (EConstr.of_constr t) in
      if not (c_type_is_void c_ty) then
        exargs := (str_of_name x, c_ty) :: !exargs
  done;
  !exargs

let compute_precise_extra_arguments
    ~(fixfunc_fixterm_tbl : Id.t Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (fixterm_free_variables : (Id.t, Id.Set.t) Hashtbl.t) :
    ((*fixterm_id*)Id.t, (*extra_arguments*)Id.Set.t) Hashtbl.t =
  let fixfunc_ids =
    Id.Map.fold
      (fun fixfunc_id fixterm_id set ->
        Id.Set.add fixfunc_id set)
      fixfunc_fixterm_tbl
      Id.Set.empty
  in
  let fixterm_extra_arguments = Hashtbl.create 0 in
  Hashtbl.iter
    (fun fixterm_id fixterm_fv ->
      let q = ref fixterm_fv in
      let extra_arguments = ref Id.Set.empty in
      while not (Id.Set.is_empty !q) do
        let id = Id.Set.choose !q in
        q := Id.Set.remove id !q;
        if not (Id.Set.mem id !extra_arguments) then
          (extra_arguments := Id.Set.add id !extra_arguments;
          match Id.Map.find_opt id fixfunc_fixterm_tbl with
          | None -> ()
          | Some fixterm2_id ->
            match Hashtbl.find_opt fixterm_free_variables fixterm2_id with
            | None -> ()
            | Some fv ->
                q := Id.Set.union !q fv)
      done;
      Hashtbl.add fixterm_extra_arguments fixterm_id
        (Id.Set.diff !extra_arguments fixfunc_ids))
    fixterm_free_variables;
  fixterm_extra_arguments

let make_extra_arguments_tbl
    ~(fixfunc_fixterm_tbl : Id.t Id.Map.t)
    ~(fixterm_tbl : (Environ.env * EConstr.t) Id.Map.t)
    ~(topfunc_tbl : (bool * string) Id.Map.t)
    ~(sibling_tbl : (bool * string) Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t)
    (genchunks : genchunk_t list) : ((string * c_typedata) list) Id.Map.t =
  let fixterm_free_variables = fixterm_free_variables env sigma term in
  let precise_extra_arguments_sets = compute_precise_extra_arguments ~fixfunc_fixterm_tbl env sigma fixterm_free_variables in
  let bodyhead_list = List.concat_map (fun genchunk -> genchunk.genchunk_bodyhead_list) genchunks in
  let result = ref Id.Map.empty in
  List.iter
    (fun bodyhead ->
      let fixfunc_ids =
        List.filter_map
          (function
            | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
            | _ -> None)
          bodyhead.bodyhead_vars
      in
      match fixfunc_ids with
      | [] -> ()
      | fixfunc_id :: inner_fixfunc_ids ->
          let fixterm_id = Id.Map.find fixfunc_id fixfunc_fixterm_tbl in
          let (fixterm_env, _) = Id.Map.find fixterm_id fixterm_tbl in
          let naive_extra_arguments = compute_naive_extra_arguments ~fixfunc_fixterm_tbl fixterm_env sigma in
          let extra_arguments =
            match (Id.Map.mem fixfunc_id topfunc_tbl), (Id.Map.mem fixfunc_id sibling_tbl) with
            | false, false ->
                let precise_set = Hashtbl.find precise_extra_arguments_sets fixterm_id in
                List.filter
                  (fun (varname, vartype) ->
                    Id.Set.mem (Id.of_string varname) precise_set)
                  naive_extra_arguments
            | _, _ ->
                naive_extra_arguments
          in
          result := Id.Map.add fixfunc_id extra_arguments !result;
          let bodyvars1 = List.tl (list_find_suffix (function BodyVarFixfunc var_fixfunc_id -> Id.equal var_fixfunc_id fixfunc_id | _ -> false) bodyhead.bodyhead_vars) in
          let rev_exargs = ref (List.rev extra_arguments) in
          List.iter
            (function
              | BodyVarArg (var, c_ty) ->
                  rev_exargs := (var, c_ty) :: !rev_exargs
              | BodyVarVoidArg _ -> ()
              | BodyVarFixfunc fixfunc_id ->
                  result := Id.Map.add fixfunc_id (List.rev !rev_exargs) !result)
            bodyvars1)
    bodyhead_list;
  !result

let make_cfunc_tbl
    ~(used_for_call_set : Id.Set.t)
    ~(sibling_tbl : (bool * string) Id.Map.t)
    (sigma : Evd.evar_map) (genchunks : genchunk_t list) : (bool * string) Id.Map.t =
  let bodyhead_list = List.concat_map (fun genchunk -> genchunk.genchunk_bodyhead_list) genchunks in
  let result = ref Id.Map.empty in
  List.iter
    (fun bodyhead ->
      let fixfunc_ids =
        List.filter_map
          (function
            | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
            | _ -> None)
          bodyhead.bodyhead_vars
      in
      let static_and_cfunc_name =
        match bodyhead.bodyhead_root with
        | BodyRootTopfunc (static, primary_cfunc)  -> Some (static, primary_cfunc)
        | BodyRootClosure _
        | BodyRootFixfunc _ ->
            match fixfunc_ids with
            | [] -> None
            | first_fixfunc_id :: _ ->
                match Id.Map.find_opt first_fixfunc_id sibling_tbl with
                | Some (sibling_static, sibling_cfunc_name) -> Some (sibling_static, sibling_cfunc_name)
                | None ->
                    let used_for_call = List.exists (fun fixfunc_id -> Id.Set.mem fixfunc_id used_for_call_set) fixfunc_ids in
                    if used_for_call then
                      Some (true, global_gensym_with_id first_fixfunc_id)
                    else
                      None
      in
      match static_and_cfunc_name with
      | Some (static, cfunc_name) ->
          List.iter
            (fun fixfunc_id ->
              result := Id.Map.add fixfunc_id (static, cfunc_name) !result)
            fixfunc_ids
      | None -> ())
    bodyhead_list;
  !result

let rec find_closures ~(found : Environ.env -> EConstr.t -> Id.t option -> unit)
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:find_closures] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:find_closures] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Lambda (x,t,b) ->
      let env2 = env_push_assum env x t in
      find_closures ~found env2 sigma b
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      Array.iter (find_closures ~found env2 sigma) fary
  | _ -> find_closures_exp ~found env sigma None term
and find_closures_exp ~(found : Environ.env -> EConstr.t -> Id.t option -> unit)
    (env : Environ.env) (sigma : Evd.evar_map) (var_to_bind : Id.t option) (term : EConstr.t) =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:find_closures_exp] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:find_closures_exp] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | LetIn (x,e,t,b) ->
      let env2 = env_push_def env x e t in
      let let_var = id_of_annotated_name x in
      find_closures_exp ~found env sigma (Some let_var) e;
      find_closures_exp ~found env2 sigma var_to_bind b
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      (Array.iter2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          find_closures_exp ~found env2 sigma var_to_bind body)
        bl bl0)
  | Rel _ -> ()
  | Const _ -> ()
  | Construct _ -> ()
  | Proj _ -> ()
  | App (f,args) -> (* The function position can be a fixpoint.  The fixpoint itself is not a closure generation but its genchunks may have closure generations. *)
      find_closures ~found env sigma f
  | Lambda _ -> (* closure generation found *)
      found env term var_to_bind;
      find_closures ~found env sigma term
  | Fix _ -> (* closure generation found *)
      found env term var_to_bind;
      find_closures ~found env sigma term

let collect_closure_terms (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (Environ.env * EConstr.t * Id.t option) list =
  let result = ref [] in
  find_closures env sigma term
    ~found:(fun closure_env closure_exp var_to_bind ->
      result := (closure_env, closure_exp, var_to_bind) :: !result);
  List.rev !result

let make_closure_c_name_tbl (sigma : Evd.evar_map) (closure_terms : (Environ.env * EConstr.t * Id.t option) list) : string Id.Map.t =
  idmap_of_list
    (List.map
      (fun (closure_env, closure_exp, var_to_bind) ->
        let closure_id = get_closure_id closure_env sigma closure_exp in
        let cloname =
          match var_to_bind with
          | None -> global_gensym ()
          | Some id -> global_gensym_with_id id
        in
        (closure_id, cloname))
      closure_terms)

let split_function_genchunks (genchunks : genchunk_t list) : genchunk_t list list =
  let genchunks = Array.of_list genchunks in
  let n = Array.length genchunks in
  (*msg_debug_hov (Pp.str "[codegen:split_function_genchunks] num_genchunks=" ++ Pp.int n);*)
  let id_int_map =
    CArray.fold_left_i
      (fun i id_int_map genchunk ->
        Id.Set.fold
          (fun fixfunc_def_id id_int_map ->
            (*msg_debug_hov (Pp.str "[codegen:split_function_genchunks]" +++
              Pp.str "i=" ++ Pp.int i +++
              Pp.str "body_fixfunc_impl=" ++ Id.print fixfunc_def_id);*)
            Id.Map.add fixfunc_def_id i id_int_map)
          genchunk.genchunk_fixfunc_impls id_int_map)
      Id.Map.empty genchunks
  in
  let u = unionfind_make n in
  Array.iteri
    (fun i genchunk ->
      Id.Set.iter
        (fun fixfunc_id -> unionfind_union u i (Id.Map.find fixfunc_id id_int_map))
        genchunk.genchunk_fixfunc_gotos)
    genchunks;
  List.map
    (List.map (fun i -> genchunks.(i)))
    (unionfind_sets u)

let entfuncs_of_bodyhead
    ~(used_for_call_set : Id.Set.t)
    ~(sibling_tbl : (bool * string) Id.Map.t)
    (bodyhead : bodyhead_t) : entry_func_t list =
  let { bodyhead_root=bodyroot; bodyhead_vars=bodyvars } = bodyhead in
  let normal_ent =
    match bodyroot with
    | BodyRootTopfunc (primary_static, primary_cfunc) ->
        Some (EntryTypeTopfunc (primary_static, primary_cfunc))
    | BodyRootFixfunc _
    | BodyRootClosure _ ->
        (let fixfunc_ids =
          List.filter_map
            (function
              | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
              | _ -> None)
            bodyvars
        in
        match fixfunc_ids with
        | [] -> None
        | first_fixfunc_id :: _ ->
            match Id.Map.find_opt first_fixfunc_id sibling_tbl with
            | Some _ ->
                Some (EntryTypeFixfunc first_fixfunc_id)
            | None ->
                List.find_map
                  (fun fixfunc_id ->
                    if Id.Set.mem fixfunc_id used_for_call_set then
                      Some (EntryTypeFixfunc first_fixfunc_id)
                    else
                      None)
                  fixfunc_ids)
  in
  let closure_ent =
    match bodyroot with
    | BodyRootClosure cloid -> Some (EntryTypeClosure cloid)
    | _ -> None
  in
  (match normal_ent with Some nent -> [{entryfunc_type=nent; entryfunc_body=bodyhead}] | None -> []) @
  (match closure_ent with Some cent -> [{entryfunc_type=cent; entryfunc_body=bodyhead}] | None -> [])

let make_labels_tbl
    ~(used_for_call_set : Id.Set.t)
    ~(used_for_goto_set : Id.Set.t)
    ~(sibling_tbl : (bool * string) Id.Map.t)
    ~(cfunc_tbl : (bool * string) Id.Map.t)
    ~(closure_c_name_tbl : string Id.Map.t)
    (genchunks : genchunk_t list) ~(first_entfunc : entry_func_t) : string Id.Map.t * string Id.Map.t =
  let bodyhead_list = List.concat_map (fun genchunk -> genchunk.genchunk_bodyhead_list) genchunks in
  let fixfunc_label_tbl = ref Id.Map.empty in
  let closure_label_tbl = ref Id.Map.empty in
  List.iter
    (fun bodyhead ->
      let fixfunc_ids =
        List.filter_map
          (function
            | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
            | _ -> None)
          bodyhead.bodyhead_vars
      in
      let (fixfunc_is_first, closure_is_first) =
        if List.mem first_entfunc (entfuncs_of_bodyhead ~used_for_call_set ~sibling_tbl bodyhead) then
          match first_entfunc.entryfunc_type with
          | EntryTypeTopfunc _ | EntryTypeFixfunc _ -> (true, false)
          | EntryTypeClosure _ -> (false, true)
        else
          (false, false)
      in
      msg_debug_hov (Pp.str "[codegen:make_labels_tbl]" +++
        Pp.str "bodyroot=" ++
          (match bodyhead.bodyhead_root with
          | BodyRootTopfunc (static,primary_cfunc) -> Pp.str ("Topfunc:" ^ primary_cfunc)
          | BodyRootFixfunc fixfunc_id -> Pp.str ("Fixfunc:" ^ Id.to_string fixfunc_id)
          | BodyRootClosure closure_id -> Pp.str ("Closure:" ^ Id.to_string closure_id)) +++
        Pp.str "fixfunc_is_first=" ++ Pp.bool fixfunc_is_first +++
        Pp.str "closure_is_first=" ++ Pp.bool closure_is_first);
      let fixfunc_label =
        match fixfunc_ids with
        | [] -> None
        | first_fixfunc_id :: _ ->
            if ((Id.Map.mem first_fixfunc_id cfunc_tbl && not fixfunc_is_first) || (* gen_func_multi requires labels to jump for each entry functions except first one *)
                List.exists (fun fixfunc_id -> Id.Set.mem fixfunc_id used_for_goto_set) fixfunc_ids) (* Anyway, labels are required if internal goto use them *)
            then
              (let label =
                match bodyhead.bodyhead_root with
                | BodyRootTopfunc (static,primary_cfunc) -> primary_entry_label primary_cfunc
                | BodyRootFixfunc fixfunc_id ->
                    (match Id.Map.find_opt fixfunc_id sibling_tbl with
                    | Some (static,sibling_cfunc) -> sibling_entry_label sibling_cfunc
                    | None -> fixfunc_entry_label (Id.to_string first_fixfunc_id))
                | BodyRootClosure closure_id ->
                    fixfunc_entry_label (Id.to_string first_fixfunc_id)
              in
              (*msg_debug_hov (Pp.str "[codegen:make_labels_tbl]" +++
                Pp.str "fixfunc_is_first=" ++ Pp.bool fixfunc_is_first +++
                Pp.str "exists_fixfunc_used_for_goto=" ++ Pp.bool (List.exists (fun fixfunc -> fixfunc.fixfunc_used_for_goto) fixfuncs));*)
              List.iter
                (fun fixfunc_id ->
                  fixfunc_label_tbl := Id.Map.add fixfunc_id label !fixfunc_label_tbl)
                fixfunc_ids;
              Some label)
            else
              None
      in
      (match bodyhead.bodyhead_root with
      | BodyRootClosure closure_id ->
          let closure_c_name = Id.Map.find closure_id closure_c_name_tbl in
          if not closure_is_first then
            let label =
              match fixfunc_label with
              | Some label -> label
              | None -> closure_entry_label closure_c_name
            in
            closure_label_tbl := Id.Map.add closure_id label !closure_label_tbl
      | _ -> ()))
    bodyhead_list;
  (!fixfunc_label_tbl, !closure_label_tbl)

let label_of_bodyhead ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) (bodyhead : bodyhead_t) : string option =
  let fixfunc_ids =
    List.filter_map
      (function
        | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
        | _ -> None)
      bodyhead.bodyhead_vars
  in
  let fixfunc_label =
    match fixfunc_ids with
    | [] -> None
    | fixfunc_id :: _ ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        fixfunc.fixfunc_label
  in
  let closure_label =
    match bodyhead.bodyhead_root with
    | BodyRootClosure cloid ->
        let clo = Hashtbl.find closure_tbl cloid in
        (match clo.closure_label with
        | Some clolabel ->
            (match fixfunc_label with
            | None -> clo.closure_label
            | Some fixlabel -> (assert (fixlabel = clolabel); None))
        | None -> None)
    | _ -> None
  in
  match fixfunc_label with
  | Some _ -> fixfunc_label
  | None -> closure_label

let make_fixfunc_table (fixfuncs : fixfunc_t list) : fixfunc_table =
  let fixfunc_tbl = Hashtbl.create 0 in
  List.iter (fun fixfunc -> Hashtbl.add fixfunc_tbl fixfunc.fixfunc_id fixfunc) fixfuncs;
  fixfunc_tbl

let collect_fixpoints
    ~(fixterm_tbl : (Environ.env * EConstr.t) Id.Map.t)
    ~(higher_order_fixfunc_tbl : bool Id.Map.t)
    ~(inlinable_fixterm_tbl : bool Id.Map.t)
    ~(used_for_call_set : Id.Set.t)
    ~(used_for_goto_set : Id.Set.t)
    ~(fixfunc_bodyhead_tbl : bodyhead_t Id.Map.t)
    ~(topfunc_tbl : (bool * string) Id.Map.t)
    ~(sibling_tbl : (bool * string) Id.Map.t)
    ~(extra_arguments_tbl : ((string * c_typedata) list) Id.Map.t)
    ~(c_names_tbl : string Id.Map.t)
    ~(cfunc_tbl : (bool * string) Id.Map.t)
    ~(fixfunc_label_tbl : string Id.Map.t)
    (sigma : Evd.evar_map) : fixfunc_table =
  let fixfuncs =
    Id.Map.fold
      (fun fixterm_id (env,term) seq ->
        let ((ks, j), (nary, tary, fary)) = destFix sigma term in
        let fixterm = {
          fixterm_id = fixterm_id;
          fixterm_inlinable = Id.Map.find fixterm_id inlinable_fixterm_tbl;
        } in
        let fixfuncs =
          Array.to_seq
            (Array.map2
              (fun name ty ->
                let fixfunc_id = id_of_annotated_name name in
                let bodyhead = Id.Map.find fixfunc_id fixfunc_bodyhead_tbl in
                let formal_arguments_without_void = bodyhead_fixfunc_fargs_without_void bodyhead fixfunc_id in
                {
                  fixfunc_fixterm = fixterm;
                  fixfunc_id = fixfunc_id;
                  fixfunc_used_for_call = Id.Set.mem fixfunc_id used_for_call_set;
                  fixfunc_used_for_goto = Id.Set.mem fixfunc_id used_for_goto_set;
                  fixfunc_bodyhead = bodyhead;
                  fixfunc_formal_arguments_without_void = formal_arguments_without_void;
                  fixfunc_is_higher_order = Id.Map.find fixfunc_id higher_order_fixfunc_tbl;
                  fixfunc_topfunc = Id.Map.find_opt fixfunc_id topfunc_tbl;
                  fixfunc_sibling = Id.Map.find_opt fixfunc_id sibling_tbl;
                  fixfunc_c_name = Id.Map.find fixfunc_id c_names_tbl;
                  fixfunc_cfunc = Id.Map.find_opt fixfunc_id cfunc_tbl;
                  fixfunc_extra_arguments = Stdlib.Option.value (Id.Map.find_opt fixfunc_id extra_arguments_tbl) ~default:[];
                  fixfunc_label = Id.Map.find_opt fixfunc_id fixfunc_label_tbl;
                })
              nary tary)
        in
        Seq.append fixfuncs seq)
      fixterm_tbl
      Seq.empty
  in
  make_fixfunc_table (List.of_seq fixfuncs)

let closure_tbl_of_list (closure_list : closure_t list) : closure_table =
  let closure_tbl = Hashtbl.create 0 in
  List.iter
    (fun clo -> Hashtbl.add closure_tbl clo.closure_id clo)
    closure_list;
  closure_tbl

let collect_closures
    ~(closure_bodyhead_tbl : bodyhead_t Id.Map.t)
    ~(extra_arguments_tbl : ((string * c_typedata) list) Id.Map.t)
    ~(closure_c_name_tbl : string Id.Map.t)
    ~(closure_label_tbl : string Id.Map.t)
    (sigma : Evd.evar_map) (closure_terms : (Environ.env * EConstr.t * Id.t option) list) : closure_table =
  let closures = ref [] in
  List.iter
    (fun (closure_env, closure_exp, var_to_bind) ->
      (*msg_debug_hov (Pp.str "[codegen:collect_closures] closure_exp=" ++ Printer.pr_econstr_env closure_env sigma closure_exp);*)
      let cloid = get_closure_id closure_env sigma closure_exp in
      let cloname = Id.Map.find cloid closure_c_name_tbl in
      let bodyhead = Id.Map.find cloid closure_bodyhead_tbl in
      let args = bodyhead_fargs bodyhead in
      let arg_types = List.map snd args in
      let c_closure_function_ty = c_closure_type arg_types bodyhead.bodyhead_return_type in
      let fv_index_set = free_variables_index_set closure_env sigma closure_exp in
      let vars = List.concat_map
        (fun index ->
          (*msg_debug_hov (Pp.str "[codegen:collect_closures] index=" ++ Pp.int index);*)
          let decl = EConstr.lookup_rel index closure_env in
          let id = id_of_name (Context.Rel.Declaration.get_name decl) in
          let ty = Context.Rel.Declaration.get_type decl in
          let env_for_ty = Environ.pop_rel_context index closure_env in
          (*msg_debug_hov (Pp.str "[codegen:collect_closures] ty=" ++ Printer.pr_econstr_env env_for_ty sigma ty);*)
          let c_ty = c_typename env_for_ty sigma ty in
          match Id.Map.find_opt id extra_arguments_tbl with
          | None ->
              [(Id.to_string id, c_ty)]
          | Some extra_arguments -> extra_arguments)
        (IntSet.elements fv_index_set)
      in
      let vars = List.sort_uniq (fun (str1,c_ty1) (str2,c_ty2) -> String.compare str1 str2) vars in
      closures := {
          closure_id=cloid;
          closure_c_name=cloname;
          closure_c_func_type=c_closure_function_ty;
          closure_args = args;
          closure_vars=vars;
          closure_label = Id.Map.find_opt cloid closure_label_tbl;
        } :: !closures)
    closure_terms;
  closure_tbl_of_list !closures

(* the reslut of used_variables is used to avoid
   useless accessor call and assignment in translation of match-expression *)
let rec used_variables (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Id.Set.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:used_variables] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:used_variables] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Const _ | Construct _ -> Id.Set.empty
  | Rel i ->
      let name = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
      Id.Set.singleton (id_of_name name)
  | Lambda (x,t,b) ->
      let env2 = env_push_assum env x t in
      used_variables env2 sigma b
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      Array.fold_left
        (fun set f -> Id.Set.union set (used_variables env2 sigma f))
        Id.Set.empty
        fary
  | LetIn (x,e,t,b) ->
      let env2 = env_push_def env x e t in
      Id.Set.union
        (used_variables env sigma e)
        (used_variables env2 sigma b)
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      Id.Set.union
        (used_variables env sigma item)
        (CArray.fold_left2
          (fun set (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            Id.Set.union set (used_variables env2 sigma body))
          Id.Set.empty
          bl bl0)
  | App (f,args) ->
      Id.Set.union
        (used_variables env sigma f)
        (Array.fold_left
          (fun set arg -> Id.Set.union set (used_variables env sigma arg))
          Id.Set.empty
          args)
  | Proj (proj, e) -> used_variables env sigma e

let local_gensym_id : (int ref) option ref = ref None

(*
let command_show_local_gensym_id () =
  match !local_gensym_id with
  | None -> Feedback.msg_info (Pp.str "[codegen] local_gensym_id = None")
  | Some _ -> Feedback.msg_info (Pp.str "[codegen] local_gensym_id = Some")
*)

let local_gensym_with (f : unit -> 'a) : 'a =
  (if !local_gensym_id <> None then
    user_err (Pp.str "[codegen:bug] nested invocation of local_gensym_with"));
  local_gensym_id := Some (ref 0);
  try
    let ret = f () in
    local_gensym_id := None;
    ret
  with
    ex ->
      (local_gensym_id := None;
      raise ex)

let local_gensym () : string =
  match !local_gensym_id with
  | None -> user_err (Pp.str "[codegen:bug] local_gensym is called outside of local_gensym_with");
  | Some idref ->
      (let n = !idref in
      idref := n + 1;
      "tmp" ^ string_of_int n)

let local_vars : ((c_typedata * string) list ref) option ref = ref None

let local_vars_with (f : unit -> 'a) : (c_typedata * string) list * 'a =
  (if !local_vars <> None then
    user_err (Pp.str "[codegen:bug] nested invocation of local_vars_with"));
  let vars = ref [] in
  local_vars := Some vars;
  try
    let ret = f () in
    local_vars := None;
    (List.rev !vars, ret)
  with
    ex ->
      (local_vars := None;
      raise ex)

let add_local_var (c_ty : c_typedata) (c_var : string) : unit =
  match !local_vars with
  | None -> user_err (Pp.str "[codegen:bug] add_local_var is called outside of local_vars_with");
  | Some vars ->
      (match List.find_opt (fun (c_type1, c_var1) -> c_var1 = c_var) !vars with
      | Some (c_type1, c_var1) ->
          if c_type1 <> c_ty then
            user_err (Pp.str "[codegen:bug] add_local_var : inconsistent typed variable")
          else
            ()
      | None -> vars := (c_ty, c_var) :: !vars)

let carg_of_garg (env : Environ.env) (i : int) : string =
  let x = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
  str_of_name x

let gen_assignment (lhs : Pp.t) (rhs : Pp.t) : Pp.t =
  Pp.hov 0 (lhs +++ Pp.str "=" +++ rhs ++ Pp.str ";")

let gen_funcall (c_fname : string) (argvars : string array) : Pp.t =
  Pp.str c_fname ++ Pp.str "(" ++
  pp_join_ary (Pp.str "," ++ Pp.spc ()) (Array.map Pp.str argvars) ++
  Pp.str ")"

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
    Pp.str c_fname
  else
    gen_funcall c_fname argvars

let gen_switch_without_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  Pp.v 0 (
  Pp.hov 0 (Pp.str "switch" +++ Pp.str "(" ++ swexpr ++ Pp.str ")") +++
  vbrace (pp_sjoinmap_ary
    (fun (caselabel, pp_branch) ->
      Pp.str caselabel ++ Pp.str ":" ++ Pp.brk (1,2) ++ Pp.v 0 pp_branch)
    branches))

let gen_switch_with_break (swexpr : Pp.t) (branches : (string * Pp.t) array) : Pp.t =
  gen_switch_without_break swexpr
    (Array.map
      (fun (caselabel, pp_branch) ->
        (caselabel, pp_branch +++ Pp.str "break;"))
      branches)

let gen_case_fragments (env : Environ.env) (sigma : Evd.evar_map) (item : EConstr.t) :
    ((*h*)int *
     (*item_type*)Constr.types *
     (*item_cvar*)string * (*c_deallocations*)Pp.t array *
     (*caselabel_accessorcalls*)(string * Pp.t array) array) =
  (*msg_debug_hov (Pp.str "[codegen] gen_match:1");*)
  let item_relindex = destRel sigma item in
  let item_type = Context.Rel.Declaration.get_type (Environ.lookup_rel item_relindex env) in
  (*msg_debug_hov (Pp.str "[codegen] gen_match: item_type=" ++ Printer.pr_econstr_env env sigma (EConstr.of_constr item_type));*)
  let item_cvar = carg_of_garg env item_relindex in
  let ind = fst (Constr.destInd (if Constr.isApp item_type then fst (Constr.destApp item_type) else item_type)) in
  let (mutind, ind_index) = ind in
  let mind_body = Environ.lookup_mind mutind env in
  let oind_body = mind_body.Declarations.mind_packets.(ind_index) in
  let h = Array.length oind_body.Declarations.mind_consnames in
  (*let result_type = Retyping.get_type_of env sigma term in*)
  (*let result_type = Reductionops.nf_all env sigma result_type in*)
  (*msg_debug_hov (Pp.str "[codegen] gen_match:2");*)
  let c_deallocations =
    if Linear.is_linear env sigma (EConstr.of_constr item_type) then
      let deallocator_for_type =
        lazy (match ConstrMap.find_opt item_type !deallocator_cfunc_map with
              | None -> Pp.mt () (* some linear type, such as immediate struct containing linear type member, don't need deallocator. *)
              | Some dealloc_cfunc ->
                  Pp.str dealloc_cfunc ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ");")
      in
      (* all arguments to an inductive type are parameters because we don't support indexed types *)
      let params = if Constr.isApp item_type then snd (Constr.destApp item_type) else [||] in
      Array.map
        (fun i ->
          let cstr = (ind, i+1) in
          let cstr_exp = Constr.mkApp (Constr.mkConstruct cstr, params) in
          (*msg_debug_hov (Pp.str "[codegen:gen_match] cstr_exp:" +++ Printer.pr_constr_env env sigma cstr_exp);*)
          match ConstrMap.find_opt cstr_exp !deallocator_cfunc_map with
          | None -> Lazy.force deallocator_for_type
          | Some dealloc_cfunc ->
              Pp.str dealloc_cfunc ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ");")
        (iota_ary 0 h)
    else
      Array.make h (Pp.mt ())
  in
  (*msg_debug_hov (Pp.str "[codegen] gen_match:3");*)
  let gen_accessor_call access =
    Pp.str access ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ")"
  in
  let caselabel_accessorcalls =
    Array.map
      (fun j ->
        (*msg_debug_hov (Pp.str "[codegen] gen_match:30");*)
        (case_cstrlabel env sigma (EConstr.of_constr item_type) j,
         Array.map
           (fun i -> gen_accessor_call (case_cstrmember env sigma (EConstr.of_constr item_type) j i))
           (iota_ary 0 oind_body.Declarations.mind_consnrealargs.(j-1))))
      (iota_ary 1 h)
  in
  (h, item_type, item_cvar, c_deallocations, caselabel_accessorcalls)

let gen_match (used_vars : Id.Set.t) (gen_switch : Pp.t -> (string * Pp.t) array -> Pp.t)
    (gen_branch_body : Environ.env -> Evd.evar_map -> EConstr.t -> Pp.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (ci : case_info) (item : EConstr.t)
    (branches : EConstr.t Constr.pcase_branch array * (EConstr.rel_context * EConstr.t) array) : Pp.t =
  let (h, item_type, item_cvar, c_deallocations, caselabel_accessorcalls) = gen_case_fragments env sigma item in
  let gen_assign_member accessor_calls ctx =
    let m = Array.length accessor_calls in
    let env2 = EConstr.push_rel_context ctx env in
    let c_vars = Array.map
      (fun i ->
        let env3 = Environ.pop_rel_context (i-1) env2 in
        let decl = Environ.lookup_rel 1 env3 in
        let (x, _, t) = Context.Rel.Declaration.to_tuple decl in
        let c_id = id_of_annotated_name x in
        let c_var = Id.to_string c_id in
        (if Id.Set.mem c_id used_vars then
          let env4 = Environ.pop_rel_context 1 env3 in
          let t = EConstr.of_constr t in
          (let c_ty = c_typename env4 sigma t in
          if not (c_type_is_void c_ty) then
            add_local_var c_ty c_var);
          Some c_var
        else
          None))
      (array_rev (iota_ary 1 m))
    in
    let c_member_access =
      pp_sjoin_ary
        (Array.map2
          (fun c_var_opt accessor_call ->
            match c_var_opt with
            | Some c_var ->
                gen_assignment (Pp.str c_var) accessor_call
            | None -> Pp.mt ())
          c_vars accessor_calls)
    in
    c_member_access
  in
  let gen_branch accessor_calls c_deallocation br =
    let ((nas, branch_body), (ctx, _)) = br in
    let env2 = EConstr.push_rel_context ctx env in
    let c_member_access = gen_assign_member accessor_calls ctx in
    let c_branch_body = gen_branch_body env2 sigma branch_body in
    c_member_access +++ c_deallocation +++ c_branch_body
  in
  (*msg_debug_hov (Pp.str "[codegen] gen_match:4");*)
  let (bl, bl0) = branches in
  if h = 1 then
    ((*msg_debug_hov (Pp.str "[codegen] gen_match:5");*)
    let accessorcalls = snd caselabel_accessorcalls.(0) in
    let c_deallocation = c_deallocations.(0) in
    let branch = (bl.(0), bl0.(0)) in
    gen_branch accessorcalls c_deallocation branch)
  else
    ((*msg_debug_hov (Pp.str "[codegen] gen_match:6");*)
    let swfunc = case_swfunc env sigma (EConstr.of_constr item_type) in
    let swexpr = if swfunc = "" then
                   Pp.str item_cvar
                 else
                   Pp.str swfunc ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ")" in
    (*msg_debug_hov (Pp.str "[codegen] gen_match:7");*)
    gen_switch swexpr
      (array_map4
        (fun (caselabel, accessorcalls) c_deallocation b b0 ->
          (caselabel, gen_branch accessorcalls c_deallocation (b, b0)))
        caselabel_accessorcalls c_deallocations bl bl0))

let gen_proj (env : Environ.env) (sigma : Evd.evar_map)
    (pr : Projection.t) (item : EConstr.t)
    (gen_cont : Pp.t -> Pp.t) : Pp.t =
  let (h, item_type, item_cvar, c_deallocations, caselabel_accessorcalls) = gen_case_fragments env sigma item in
  assert (h = 1);
  let accessorcall = (snd caselabel_accessorcalls.(0)).(Projection.arg pr) in
  let c_deallocation = c_deallocations.(0) in
  c_deallocation +++ gen_cont accessorcall

let gen_parallel_assignment (assignments : ((*lhs*)string * (*rhs*)string * (*type*)c_typedata) array) : Pp.t =
  let assign = Array.to_list assignments in
  let assign = List.filter (fun (lhs, rhs, ty) -> lhs <> rhs) assign in
  let rpp = ref (Pp.mt ()) in
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
              let pp = gen_assignment (Pp.str lhs) (Pp.str rhs) in
              rpp := !rpp +++ pp)
            nonblocked_assign;
          loop blocked_assign)
        else
          (let (a_lhs, a_rhs, a_ty) = a in
          let tmp = local_gensym () in
          add_local_var a_ty tmp;
          let pp = gen_assignment (Pp.str tmp) (Pp.str a_lhs) in
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

let add_local_vars_in_fix_body_list (sigma : Evd.evar_map) fix_bodies =
  List.iter
    (fun (context, env_body) ->
      List.iter
        (fun (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) ->
          let env = ref fixfunc_env2 in
          List.iter
            (fun (x,t) ->
              (let c_ty = c_typename !env sigma t in
              if not (c_type_is_void c_ty) then
                add_local_var c_ty (str_of_annotated_name x));
              env := env_push_assum !env x t)
            (List.rev fixfunc_fargs))
        context)
    fix_bodies

type head_cont = {
  head_cont_ret_var : string option; (* None for void type context *)
  head_cont_exit_label : string option;
}

let gen_head_cont ?(omit_void_exp : bool = false) (cont : head_cont) (exp : Pp.t) : Pp.t =
  (match cont.head_cont_ret_var with
  | None -> if omit_void_exp then Pp.mt () else Pp.hov 0 (exp ++ Pp.str ";")
  | Some c_var -> gen_assignment (Pp.str c_var) exp) +++
  match cont.head_cont_exit_label with
  | None -> Pp.mt ()
  | Some label -> Pp.hov 0 (Pp.str "goto" +++ Pp.str label ++ Pp.str ";")

let rec gen_head ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) ~(used_vars : Id.Set.t) ~(cont : head_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
  let pp = gen_head1 ~fixfunc_tbl ~closure_tbl ~used_vars ~cont env sigma term in
  (*msg_debug_hov (Pp.str "[codegen] gen_head:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_head1 ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) ~(used_vars : Id.Set.t) ~(cont : head_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
  let (term, argsary) = decompose_appvect sigma term in
  let cargs_without_void =
    (List.filter_map
      (fun arg ->
        let arg_ty = Retyping.get_type_of env sigma arg in
        if ind_is_void_type env sigma arg_ty then
          None
        else
          Some (carg_of_garg env (destRel sigma arg)))
      (Array.to_list argsary))
  in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:gen_head] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
      user_err (Pp.str "[codegen:gen_head] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if CArray.is_empty argsary then
        let str = carg_of_garg env i in
        gen_head_cont ~omit_void_exp:true cont (Pp.str str)
      else
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        (match Hashtbl.find_opt fixfunc_tbl (id_of_name name) with
        | None -> (* closure invocation *)
            let closure_var = carg_of_garg env i in
            let pp = gen_funcall ("(*" ^ closure_var ^ ")") (Array.of_list (rcons cargs_without_void closure_var)) in
            gen_head_cont cont pp
        | Some fixfunc ->
            if fixfunc.fixfunc_fixterm.fixterm_inlinable then
              let assignments =
                List.map2
                  (fun (lhs, c_ty) rhs -> (lhs, rhs, c_ty))
                  fixfunc.fixfunc_formal_arguments_without_void
                  cargs_without_void
              in
              let pp_assignments = gen_parallel_assignment (Array.of_list assignments) in
              let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str (Option.get fixfunc.fixfunc_label) ++ Pp.str ";") in
              pp_assignments +++ pp_goto_entry
            else
              gen_head_cont cont
                (gen_funcall (cfunc_of_fixfunc fixfunc)
                  (Array.append
                    (Array.of_list (List.map fst fixfunc.fixfunc_extra_arguments))
                    (Array.of_list cargs_without_void))))

  | Const (ctnt,_) ->
      gen_head_cont cont (gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list cargs_without_void))
  | Construct (cstr,_) ->
      gen_head_cont ~omit_void_exp:true cont (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list cargs_without_void))
  | Case (ci,u,pms,p,iv,item,bl) ->
      assert (CArray.is_empty argsary);
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let gen_switch =
        match cont.head_cont_exit_label with
        | None -> gen_switch_with_break
        | Some _ -> gen_switch_without_break
      in
      gen_match used_vars gen_switch (gen_head ~fixfunc_tbl ~closure_tbl ~used_vars ~cont) env sigma ci item (bl,bl0)
  | Proj (pr, item) ->
      ((if not (CArray.is_empty argsary) then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_proj env sigma pr item (gen_head_cont ~omit_void_exp:true cont))
  | LetIn (x,e,t,b) ->
      assert (CArray.is_empty argsary);
      let c_var = str_of_annotated_name x in
      let env2 = env_push_def env (Context.nameR (Id.of_string c_var)) e t in
      let cont1 =
        let c_ty = c_typename env sigma t in
        if c_type_is_void c_ty then
          { head_cont_ret_var = None;
            head_cont_exit_label = None; }
        else
          (add_local_var c_ty c_var;
          { head_cont_ret_var = Some c_var;
            head_cont_exit_label = None; })
      in
      gen_head ~fixfunc_tbl ~closure_tbl ~used_vars ~cont:cont1 env sigma e +++
      gen_head ~fixfunc_tbl ~closure_tbl ~used_vars ~cont env2 sigma b
  | Lambda _ | Fix _ when Array.length argsary = 0 ->
      let cloid = get_closure_id env sigma term in
      let clo = Hashtbl.find closure_tbl cloid in
      let clo_struct_ty = closure_struct_type clo in
      let clo_func = closure_func_name clo in
      let clo_var = local_gensym () in
      add_local_var clo_struct_ty clo_var;
      gen_assignment (Pp.str (clo_var^".closure_func")) (Pp.str clo_func) +++
      pp_sjoinmap_list
        (fun (var,ty) -> gen_assignment (Pp.str (clo_var^"."^var)) (Pp.str var))
        clo.closure_vars +++
      gen_head_cont cont (Pp.str ("&"^clo_var^".closure_func"))
  | Lambda _ -> assert false
  | Fix ((ks, j), ((nary, tary, fary))) ->
      let fixfunc_j = Hashtbl.find fixfunc_tbl (id_of_annotated_name nary.(j)) in
      if not fixfunc_j.fixfunc_fixterm.fixterm_inlinable then
        gen_head_cont cont
          (gen_funcall (cfunc_of_fixfunc fixfunc_j)
            (Array.append
              (Array.of_list (List.map fst fixfunc_j.fixfunc_extra_arguments))
              (Array.of_list cargs_without_void)))
      else
        let assignments =
          List.map2
            (fun (lhs, c_ty) rhs -> (lhs, rhs, c_ty))
            fixfunc_j.fixfunc_formal_arguments_without_void
            cargs_without_void
        in
        let pp_assignments = gen_parallel_assignment (Array.of_list assignments) in
        let (cont2, pp_exit) =
          match cont.head_cont_exit_label with
          | None ->
              let exit_label = fixfunc_exit_label fixfunc_j.fixfunc_c_name in
              ({ cont with head_cont_exit_label = Some exit_label },
               Pp.hov 0 (Pp.str exit_label ++ Pp.str ":"))
          | Some _ ->
              (cont, Pp.mt ())
        in
        let fix_bodies = fix_body_list env sigma term in
        add_local_vars_in_fix_body_list sigma fix_bodies;
        let pp_fixfuncs =
          List.map
            (fun (context, (body_env, body)) ->
              let pp_label =
                let (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) = List.hd context in
                let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name fixfunc_name) in
                match fixfunc_i.fixfunc_label with
                | None -> Pp.mt ()
                | Some label -> Pp.str label ++ Pp.str ":"
              in
              pp_label +++ gen_head ~fixfunc_tbl ~closure_tbl ~used_vars ~cont:cont2 body_env sigma body)
            fix_bodies
        in
        pp_assignments +++ pp_sjoin_list pp_fixfuncs +++ pp_exit

type tail_cont = { tail_cont_return_type: c_typedata; tail_cont_multifunc: bool }

let gen_tail_cont ?(omit_void_exp : bool = false) (cont : tail_cont) (exp : Pp.t) : Pp.t =
  if c_type_is_void cont.tail_cont_return_type then
    if omit_void_exp then
      Pp.str "return;"
    else
      Pp.hov 0 (exp ++ Pp.str ";") +++ Pp.str "return;"
  else
    if cont.tail_cont_multifunc then
      let retvar = "(*(" ^ compose_c_abstract_decl (c_type_pointer_to cont.tail_cont_return_type) ^ ")codegen_ret)" in
      gen_assignment (Pp.str retvar) exp +++ Pp.str "return;"
    else
      Pp.hov 0 (Pp.str "return" +++ exp ++ Pp.str ";")

let rec gen_tail ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) ~(used_vars : Id.Set.t) ~(cont : tail_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
  (*msg_debug_hov (Pp.str "[codegen] gen_tail start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "(" ++
    pp_sjoinmap_list Pp.str cargs ++
    Pp.str ")");*)
  let pp = gen_tail1 ~fixfunc_tbl ~closure_tbl ~used_vars ~cont env sigma term in
  (*msg_debug_hov (Pp.str "[codegen] gen_tail return:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_tail1 ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) ~(used_vars : Id.Set.t) ~(cont : tail_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
  let (term, argsary) = decompose_appvect sigma term in
  let cargs_without_void =
    (List.filter_map
      (fun arg ->
        let arg_ty = Retyping.get_type_of env sigma arg in
        if ind_is_void_type env sigma arg_ty then
          None
        else
          Some (carg_of_garg env (destRel sigma arg)))
      (Array.to_list argsary))
  in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:gen_tail] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
      user_err (Pp.str "[codegen:gen_tail] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if CArray.is_empty argsary then
        let str = carg_of_garg env i in
        gen_tail_cont ~omit_void_exp:true cont (Pp.str str)
      else
        let key = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
        let fixfunc_opt = Hashtbl.find_opt fixfunc_tbl (id_of_name key) in
        (match fixfunc_opt with
        | None -> (* closure invocation *)
            let closure_var = carg_of_garg env i in
            let pp = gen_funcall ("(*" ^ closure_var ^ ")") (Array.of_list (rcons cargs_without_void closure_var)) in
            gen_tail_cont cont pp
        | Some fixfunc ->
            if List.length cargs_without_void < List.length fixfunc.fixfunc_formal_arguments_without_void then
              user_err (Pp.str "[codegen] gen_tail: partial application for fix-bounded-variable (higher-order term not supported yet):" +++
                Printer.pr_econstr_env env sigma term);
            if not fixfunc.fixfunc_is_higher_order then
              let assignments =
                List.map2
                  (fun (lhs, c_ty) rhs -> (lhs, rhs, c_ty))
                  fixfunc.fixfunc_formal_arguments_without_void
                  cargs_without_void
              in
              let pp_assignments = gen_parallel_assignment (Array.of_list assignments) in
              let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str (Option.get fixfunc.fixfunc_label) ++ Pp.str ";") in
              pp_assignments +++ pp_goto_entry
            else
              gen_tail_cont cont
                (gen_funcall (cfunc_of_fixfunc fixfunc)
                  (Array.append
                    (Array.of_list (List.map fst fixfunc.fixfunc_extra_arguments))
                    (Array.of_list cargs_without_void))))
  | Const (ctnt,_) ->
      let pp = gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list cargs_without_void) in
      gen_tail_cont cont pp
  | Construct (cstr,univ) ->
      gen_tail_cont ~omit_void_exp:true cont (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list cargs_without_void))
  | Lambda (x,t,b) ->
      user_err (Pp.str "[codegen] gen_tail: lambda term without argument (higher-order term not supported yet):" +++
        Printer.pr_econstr_env env sigma term)
  | Case (ci,u,pms,p,iv,item,bl) ->
      assert (CArray.is_empty argsary);
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      gen_match used_vars gen_switch_without_break (gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont) env sigma ci item (bl,bl0)
  | Proj (pr, item) ->
      ((if not (CArray.is_empty argsary) then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_proj env sigma pr item (gen_tail_cont ~omit_void_exp:true cont))
  | LetIn (x,e,t,b) ->
      assert (CArray.is_empty argsary);
      let c_var = str_of_annotated_name x in
      let env2 = env_push_def env (Context.nameR (Id.of_string c_var)) e t in
      let cont1 =
        let c_ty = c_typename env sigma t in
        if c_type_is_void c_ty then
          { head_cont_ret_var = None;
            head_cont_exit_label = None; }
        else
          (add_local_var c_ty c_var;
          { head_cont_ret_var = Some c_var;
            head_cont_exit_label = None; })
      in
      gen_head ~fixfunc_tbl ~closure_tbl ~used_vars ~cont:cont1 env sigma e +++
      gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont env2 sigma b

  | Fix ((ks, j), (nary, tary, fary)) ->
      let fixfunc_j = Hashtbl.find fixfunc_tbl (id_of_annotated_name nary.(j)) in
      if List.length cargs_without_void < List.length fixfunc_j.fixfunc_formal_arguments_without_void then
        user_err (Pp.str "[codegen] gen_tail: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assignments =
        List.map2
          (fun (lhs, c_ty) rhs ->  (lhs, rhs, c_ty))
          fixfunc_j.fixfunc_formal_arguments_without_void
          cargs_without_void
      in
      let pp_assignments = gen_parallel_assignment (Array.of_list assignments) in
      let fix_bodies = fix_body_list env sigma term in
      add_local_vars_in_fix_body_list sigma fix_bodies;
      let pp_fixfuncs =
        List.map
          (fun (context, (body_env, body)) ->
            let pp_label =
              let (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) = List.hd context in
              let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name fixfunc_name) in
              match fixfunc_i.fixfunc_label with
              | None -> Pp.mt () (* Not reached.  Currently, fix-term in top-call are decomposed by obtain_function_genchunks and gen_tail is not used for it. *)
              | Some label -> Pp.str label ++ Pp.str ":"
            in
            pp_label +++ gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont body_env sigma body)
          fix_bodies
      in
      pp_assignments +++ pp_sjoin_list pp_fixfuncs

let gen_function_header ~(static : bool) (return_type : c_typedata) (c_name : string)
    (formal_arguments : (string * c_typedata) list) : Pp.t =
  let pp_static = (if static then Pp.str "static" else Pp.mt ()) in
  let pp_parameters =
    Pp.str "(" ++
    (if formal_arguments = [] then
      Pp.str "void"
    else
      (pp_joinmap_list (Pp.str "," ++ Pp.spc ())
        (fun (c_arg, c_ty) ->
          Pp.hov 0 (pr_c_decl c_ty (Pp.str c_arg)))
        formal_arguments)) ++
    Pp.str ")"
  in
  Pp.hov 0 (pp_static +++ pr_c_decl return_type (Pp.str c_name ++ Pp.hov 0 (pp_parameters)))

let pr_members (args : (string * c_typedata) list) : Pp.t =
  pp_sjoinmap_list
    (fun (c_arg, c_ty) -> Pp.hov 0 (pr_c_decl c_ty (Pp.str c_arg) ++ Pp.str ";"))
    args

let gen_closure_struct (clo : closure_t) : Pp.t =
  Pp.hv 0 (
  Pp.str ("struct " ^ closure_struct_tag clo) +++
  hovbrace (
    pr_members [("closure_func", c_type_pointer_to clo.closure_c_func_type)] +++
    pr_members clo.closure_vars
  ) ++ Pp.str ";")

let gen_closure_load_vars_assignments (clo : closure_t) (var : string) : (string * string) list =
  (List.map
    (fun (c_arg, c_ty) ->
      (c_arg,
       (var ^ "->" ^ c_arg)))
    clo.closure_vars)

let gen_closure_load_args_assignments (clo : closure_t) (var : string) : (string * string) list =
  List.append
    (List.map
      (fun (c_arg, c_ty) ->
        (c_arg,
         ("((" ^ closure_args_struct_type clo.closure_c_name ^ " *)" ^ var ^ ")->" ^ c_arg)))
      clo.closure_args)
    (gen_closure_load_vars_assignments clo ("((" ^ closure_args_struct_type clo.closure_c_name ^ " *)" ^ var ^ ")->closure"))

let pointer_to_void = { c_type_left="void *"; c_type_right="" }

let gen_func_single
    ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table)
    ~(entfunc : entry_func_t)
    ~(genchunks : genchunk_t list)
    (sigma : Evd.evar_map)
    (used_vars : Id.Set.t) : Pp.t * Pp.t =
  let bodyhead = entfunc.entryfunc_body in
  let (static, primary_cfunc) =
    match entfunc.entryfunc_type with
    | EntryTypeTopfunc (static, primary_cfunc) -> (static, primary_cfunc)
    | EntryTypeFixfunc fixfunc_id ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        (Option.get fixfunc.fixfunc_cfunc)
    | EntryTypeClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        (true, closure_func_name clo)
  in
  let (pp_struct_closure, pp_closure_assigns, closure_vars) =
    match entfunc.entryfunc_type with
    | EntryTypeClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        let casted_var = "((struct " ^ closure_struct_tag clo ^ " *)closure)" in
        (gen_closure_struct clo,
         pp_sjoinmap_list
           (fun (lhs, rhs) -> gen_assignment (Pp.str lhs) (Pp.str rhs))
           (gen_closure_load_vars_assignments clo casted_var),
         clo.closure_vars)
    | _ ->
        (Pp.mt (), Pp.mt (), [])
  in
  let c_fargs =
    match entfunc.entryfunc_type with
    | EntryTypeTopfunc _ -> bodyhead_fargs entfunc.entryfunc_body
    | EntryTypeFixfunc fixfunc_id ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        (*msg_debug_hov (Pp.str "[codegen:gen_func_single:c_fargs:EntryTypeFixfunc] fixfunc_extra_arguments=" ++ pr_args fixfunc.fixfunc_extra_arguments);
        msg_debug_hov (Pp.str "[codegen:gen_func_single:c_fargs:EntryTypeFixfunc] bodyhead_fargs=" ++ pr_args (bodyhead_fargs entfunc.entryfunc_body));*)
        fixfunc.fixfunc_extra_arguments @ (bodyhead_fargs entfunc.entryfunc_body)
    | EntryTypeClosure closure_id ->
        (bodyhead_fargs entfunc.entryfunc_body) @ [("closure", pointer_to_void)]
  in
  let return_type = bodyhead.bodyhead_return_type in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun genchunk ->
          let bodyhead = List.hd genchunk.genchunk_bodyhead_list in
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (bodyhead_fargs bodyhead);
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            closure_vars;
          let cont = { tail_cont_return_type = return_type; tail_cont_multifunc = false } in
          let label_opt = label_of_bodyhead ~fixfunc_tbl ~closure_tbl bodyhead in
          pp_closure_assigns +++
          (match label_opt with None -> Pp.mt () | Some l -> Pp.str (l ^ ":")) +++
          gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont genchunk.genchunk_env sigma genchunk.genchunk_exp)
        genchunks)
  in
  let local_vars = List.filter
    (fun (c_ty, c_var) ->
      match List.find_opt (fun (c_var1, ty1) -> c_var = c_var1) c_fargs with
      | Some _ -> false (* xxx: check type mismach *)
      | None -> true)
    local_vars
  in
  (pp_struct_closure +++
   gen_function_header ~static return_type primary_cfunc c_fargs ++ Pp.str ";",
   Pp.v 0 (
   gen_function_header ~static return_type primary_cfunc c_fargs +++
   vbrace (
     pp_sjoinmap_list
       (fun (c_ty, c_var) -> Pp.hov 0 (pr_c_decl c_ty (Pp.str c_var) ++ Pp.str ";"))
       local_vars
     +++
     pp_body)))

let pr_entry_function ~(static:bool) (c_funcname : string) (func_enum_index : string)
    (args_struct_type : string) (formal_arguments : (string * c_typedata) list) (return_type : c_typedata)
    (body_function_name : string) : Pp.t =
  let null = "((void*)0)" in (* We don't use NULL because it needs stddef.h.  nullptr can be used in C2x. *)
  let (pp_vardecl_args, pp_struct_arg) =
    if CList.is_empty formal_arguments then
      (Pp.mt (), null)
    else
      (Pp.hov 2
        (Pp.str args_struct_type +++
         Pp.str "codegen_args" +++
         Pp.str "=" +++
         hovbrace (
           (pp_joinmap_list (Pp.str "," ++ Pp.spc ())
             (fun (c_arg, t) -> Pp.str c_arg)
             formal_arguments)) ++
         Pp.str ";"),
       "&codegen_args")
  in
  let (pp_vardecl_ret, pp_return_arg) =
    if c_type_is_void return_type then
      (Pp.mt (), null)
    else
      (Pp.hov 2 (pr_c_decl return_type (Pp.str "codegen_ret") ++ Pp.str ";"), "&codegen_ret")
  in
  let pp_call =
    Pp.hov 2 (Pp.str body_function_name ++
              Pp.str "(" ++
              Pp.str func_enum_index ++ Pp.str "," +++
              Pp.str pp_struct_arg ++ Pp.str "," +++
              Pp.str pp_return_arg ++ Pp.str ");")
  in
  let pp_return =
    if c_type_is_void return_type then
      Pp.str "return;"
    else
      Pp.str "return codegen_ret;"
  in
  Pp.v 0 (
    gen_function_header ~static return_type c_funcname formal_arguments +++
    vbrace (
      pp_vardecl_args +++
      pp_vardecl_ret +++
      pp_call +++
      pp_return))

let func_index_enum_tag_name primary_cfunc = "codegen_func_indextype_" ^ primary_cfunc

let topfunc_enum_index primary_cfunc = "codegen_topfunc_index_" ^ primary_cfunc
let fixfunc_enum_index fixfunc_c_name = "codegen_fixfunc_index_" ^ fixfunc_c_name
let closure_enum_index closure_c_name = "codegen_closure_index_" ^ closure_c_name

let pr_case (case_value : string option) (assigns : (string * string) list) (goto_label : string option) : Pp.t =
  let pp_case =
    (match case_value with
    | None -> Pp.str "default:"
    | Some value -> Pp.hov 0 (Pp.str "case" +++ Pp.str value ++ Pp.str ":"))
  in
  let pp_semicolon =
    if assigns = [] && goto_label = None then
      (* label (case label and default label here) needs following statement *)
      Pp.str ";"
    else
      Pp.mt ()
  in
  let pp_assigns =
    pp_sjoinmap_list
      (fun (lhs, rhs) -> gen_assignment (Pp.str lhs) (Pp.str rhs))
      assigns
  in
  let pp_goto =
    match goto_label with
    | None -> Pp.mt ()
    | Some label -> Pp.hov 0 (Pp.str "goto" +++ Pp.str label ++ Pp.str ";")
  in
  pp_case ++ pp_semicolon ++ Pp.brk (1,2) ++
  Pp.v 0 (
    pp_assigns +++
    pp_goto)

let pr_multi_topfunc_defs (bodyhead : bodyhead_t) (static : bool) (primary_cfunc : string) (body_function_name : string) : Pp.t =
  let formal_arguments = bodyhead_fargs bodyhead in
  let return_type = bodyhead.bodyhead_return_type in
  (if CList.is_empty formal_arguments then
    Pp.mt ()
  else
    (Pp.hv 0 (
      Pp.str (topfunc_args_struct_type primary_cfunc) +++
      hovbrace (pr_members formal_arguments) ++ Pp.str ";"))) +++
  pr_entry_function ~static primary_cfunc (topfunc_enum_index primary_cfunc)
    (topfunc_args_struct_type primary_cfunc)
    formal_arguments return_type
    body_function_name

let pr_multi_topfunc_case (bodyhead : bodyhead_t) (primary_cfunc : string) : Pp.t =
  let formal_arguments = bodyhead_fargs bodyhead in
  pr_case None
    (List.map
      (fun (c_arg, t) ->
          (c_arg,
           ("((" ^ topfunc_args_struct_type primary_cfunc ^ " *)codegen_args)->" ^ c_arg)))
      formal_arguments)
    None (* no need to goto label because EntryTypeTopfunc is always at last *)

let pr_multi_fixfunc_defs (bodyhead : bodyhead_t) (fixfunc : fixfunc_t) (body_function_name : string) : Pp.t =
  let (static, cfunc) = Option.get fixfunc.fixfunc_cfunc in
  let return_type = bodyhead.bodyhead_return_type in
  let arguments = fixfunc.fixfunc_extra_arguments @ fixfunc.fixfunc_formal_arguments_without_void in
  (if CList.is_empty arguments then
    Pp.mt ()
  else
    (Pp.hv 0 (
    Pp.str (fixfunc_args_struct_type fixfunc.fixfunc_c_name) +++
    hovbrace (pr_members arguments) ++ Pp.str ";"))) +++
  pr_entry_function ~static cfunc (fixfunc_enum_index fixfunc.fixfunc_c_name)
    (fixfunc_args_struct_type fixfunc.fixfunc_c_name)
    arguments
    return_type
    body_function_name

let pr_multi_fixfunc_case (is_last : bool) (fixfunc : fixfunc_t) : Pp.t =
  let case_value = if is_last then None else Some (fixfunc_enum_index fixfunc.fixfunc_c_name) in
  let goto = if is_last then None else Some (Option.get fixfunc.fixfunc_label) in
  pr_case case_value
    (List.append
      (List.map
        (fun (c_arg, t) ->
          (c_arg,
           ("((" ^ fixfunc_args_struct_type fixfunc.fixfunc_c_name ^ " *)codegen_args)->" ^ c_arg)))
        fixfunc.fixfunc_extra_arguments)
      (List.map
        (fun (c_arg, c_ty) ->
          (c_arg,
           ("((" ^ fixfunc_args_struct_type fixfunc.fixfunc_c_name ^ " *)codegen_args)->" ^ c_arg)))
        fixfunc.fixfunc_formal_arguments_without_void))
    goto

let pr_multi_closure_defs (bodyhead : bodyhead_t) (clo : closure_t) (body_function_name : string) : Pp.t =
  gen_closure_struct clo +++
  (Pp.hv 0 (
    Pp.str (closure_args_struct_type clo.closure_c_name) +++
    hovbrace (
      pr_members clo.closure_args +++
      pr_members [("closure", c_type_pointer_to (closure_struct_type clo))]
    ) ++ Pp.str ";")) +++
  pr_entry_function ~static:true (closure_func_name clo) (closure_enum_index clo.closure_c_name)
    (closure_args_struct_type clo.closure_c_name)
    (List.append clo.closure_args [("closure", pointer_to_void)])
    bodyhead.bodyhead_return_type
    body_function_name

let pr_multi_closure_case (clo : closure_t) : Pp.t =
  pr_case (Some (closure_enum_index clo.closure_c_name))
    (gen_closure_load_args_assignments clo "codegen_args")
    (Some (Option.get (clo.closure_label)))

let gen_func_multi
    ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table)
    ~(entry_funcs : entry_func_t list)
    ~(genchunks : genchunk_t list)
    (env : Environ.env) (sigma : Evd.evar_map)
    (used_vars : Id.Set.t) : Pp.t * Pp.t =
  let first_c_name =
    match (List.hd entry_funcs).entryfunc_type with
    | EntryTypeTopfunc (_, primary_cfunc) -> primary_cfunc
    | EntryTypeFixfunc fixfunc_id ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        (cfunc_of_fixfunc fixfunc)
    | EntryTypeClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        closure_func_name clo
  in
  let num_entry_funcs = List.length entry_funcs in
  let entry_funcs = (* make the first entry function, possibly EntryTypeTopfunc, at last *)
    match entry_funcs with
    | [] -> []
    | hd :: tl -> rcons tl hd
  in
  let func_index_enum_tag = func_index_enum_tag_name first_c_name in
  let body_function_name = body_function_name first_c_name in
  let pp_forward_decl =
    Pp.hv 0 (
      Pp.str "static void" +++
      Pp.str body_function_name ++
      Pp.str ("(enum " ^ func_index_enum_tag ^ " codegen_func_index, void *codegen_args, void *codegen_ret);"))
  in
  let entries =
      List.mapi
        (fun i entry_func ->
          let is_last = (i = num_entry_funcs - 1) in
          (match entry_func with
          | {entryfunc_type=(EntryTypeTopfunc (static, primary_cfunc)); entryfunc_body=bodyhead} ->
              assert is_last;
              let enumindex = topfunc_enum_index primary_cfunc in
              let defs = pr_multi_topfunc_defs bodyhead static primary_cfunc body_function_name in
              let case = pr_multi_topfunc_case bodyhead primary_cfunc in
              (enumindex, defs, case)
          | {entryfunc_type=(EntryTypeFixfunc fixfunc_id); entryfunc_body=bodyhead} ->
              let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
              let enumindex = fixfunc_enum_index fixfunc.fixfunc_c_name in
              let defs = pr_multi_fixfunc_defs bodyhead fixfunc body_function_name in
              let case = pr_multi_fixfunc_case is_last fixfunc in
              (enumindex, defs, case)
          | {entryfunc_type=(EntryTypeClosure closure_id); entryfunc_body=bodyhead} ->
              let clo = Hashtbl.find closure_tbl closure_id in
              let enumindex = closure_enum_index clo.closure_c_name in
              let defs = pr_multi_closure_defs bodyhead clo body_function_name in
              let case = pr_multi_closure_case clo in
              (enumindex, defs, case)))
        entry_funcs
  in
  let pp_enum =
    Pp.hov 0 (
      Pp.str "enum" +++
      Pp.str func_index_enum_tag +++
      hovbrace (
        pp_joinmap_list (Pp.str "," ++ Pp.spc ())
          (fun (enumindex, defs, case) -> Pp.str enumindex)
          entries) ++
      Pp.str ";")
  in
  let pp_entry_defs = pp_sjoin_list (List.map (fun (enumindex, defs, case) -> defs) entries) in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun genchunk ->
          let bodyhead = List.hd genchunk.genchunk_bodyhead_list in
          List.iter
            (fun (arg_name, arg_type) ->
              (*msg_debug_hov (Pp.str ("[codegen:gen_func_multi] add_local_var " ^ arg_name));*)
              add_local_var arg_type arg_name)
            (bodyhead_fargs bodyhead);
          List.iter
            (function
              | BodyVarFixfunc fixfunc_id ->
                  let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
                  List.iter
                    (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
                    fixfunc.fixfunc_extra_arguments
              | _ -> ())
            bodyhead.bodyhead_vars;
          let cont = { tail_cont_return_type = bodyhead.bodyhead_return_type; tail_cont_multifunc = true } in
          let label_opt = label_of_bodyhead ~fixfunc_tbl ~closure_tbl bodyhead in
          Pp.v 0 (
            (match label_opt with None -> Pp.mt () | Some l -> Pp.str (l ^ ":")) +++
            gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont genchunk.genchunk_env sigma genchunk.genchunk_exp))
        genchunks)
  in
  let pp_local_variables_decls =
    pp_sjoinmap_list
      (fun (c_ty, c_var) -> Pp.hov 0 (pr_c_decl c_ty (Pp.str c_var) ++ Pp.str ";"))
      local_vars
  in
  let pp_switch =
    Pp.hov 0 (Pp.str "switch" +++ Pp.str "(codegen_func_index)") +++
    vbrace (pp_sjoin_list (List.map (fun (enumindex, defs, case) -> case) entries))
  in
  let pp_body_function =
    (Pp.str "static void" +++
    Pp.str body_function_name ++
    Pp.str ("(enum " ^ func_index_enum_tag ^ " codegen_func_index, void *codegen_args, void *codegen_ret)")) +++
    vbrace (
      pp_local_variables_decls +++
      pp_switch +++
      pp_body)
  in
  (Pp.v 0 (
     pp_enum +++
     pp_forward_decl +++
     pp_entry_defs),
   Pp.v 0 (pp_body_function))

let is_static_function_icommand (icommand : instance_command) : bool =
  match icommand with
  | CodeGenFunc -> false
  | CodeGenStaticFunc -> true
  | CodeGenPrimitive -> user_err (Pp.str "[codegen] unexpected CodeGenPrimitive")
  | CodeGenConstant -> user_err (Pp.str "[codegen] unexpected CodeGenConstant")

let make_simplified_for_cfunc (cfunc_name : string) :
    (*static*)bool * Constr.types * Constr.t =
  let (sp_cfg, sp_inst) =
    match CString.Map.find_opt cfunc_name !cfunc_instance_map with
    | None ->
        user_err (Pp.str "[codegen] C function name not found:" +++
                  Pp.str cfunc_name)
    | Some (CodeGenCfuncGenerate (sp_cfg, sp_inst)) -> (sp_cfg, sp_inst)
    | Some (CodeGenCfuncPrimitive _) ->
        user_err (Pp.str "[codegen] C primitive function name found:" +++
                  Pp.str cfunc_name)
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
  (*msg_debug_hov (Pp.str "[codegen:make_simplified_for_cfunc] ctnt=" ++ Printer.pr_constant env ctnt);*)
  let cdef = Environ.lookup_constant ctnt env in
  let ty = cdef.Declarations.const_type in
  match Global.body_of_constant_body Library.indirect_accessor cdef with
  | None -> user_err (Pp.str "[codegen] couldn't obtain the body:" +++
                      Printer.pr_constant env ctnt)
  | Some (body,_, _) -> (static, ty, body)

let make_sibling_entfuncs (primary_term : Constr.t) (sibling_cfunc_static_ty_term_list : ((*cfunc*)string * (*static*)bool * Constr.types * Constr.t) list) : sibling_t list =
  let (args, body) = Term.decompose_lam primary_term in
  if Constr.isFix body then
    let primary_nary =
      let ((ks, j), (nary, tary, fary)) = Constr.destFix body in
      nary
    in
    List.map
      (fun (cfunc, static, ty, term) ->
        let (args, body) = Term.decompose_lam term in
        let ((ks, j), (nary, tary, fary)) = Constr.destFix body in
        let fixfunc_id = id_of_annotated_name primary_nary.(j) in
        { sibling_static=static; sibling_cfunc=cfunc; sibling_fixfunc_id=fixfunc_id })
      sibling_cfunc_static_ty_term_list
  else
    []

let gen_func_sub (cfunc_static_ty_term_list : (string * bool * Constr.types * Constr.t) list) : Pp.t =
  let (primary_cfunc, primary_static, primry_ty, primry_term) = List.hd cfunc_static_ty_term_list in
  let sibling_entfuncs = make_sibling_entfuncs primry_term (List.tl cfunc_static_ty_term_list) in
  let static_and_primary_cfunc = (primary_static, primary_cfunc) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let primry_term = EConstr.of_constr primry_term in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:1");*)
  let fixterm_tbl = make_fixterm_tbl env sigma primry_term in
  let fixfunc_fixterm_tbl = make_fixfunc_fixterm_tbl sigma ~fixterm_tbl in
  let higher_order_fixfunc_tbl = make_higher_order_fixfunc_tbl sigma ~fixterm_tbl in
  let inlinable_fixterm_tbl = make_inlinable_fixterm_tbl ~higher_order_fixfunc_tbl env sigma primry_term in
  let genchunks = obtain_function_genchunks ~higher_order_fixfunc_tbl ~inlinable_fixterm_tbl ~static_and_primary_cfunc env sigma primry_term in
  let used_for_call_set = make_used_for_call_set genchunks in
  let used_for_goto_set = make_used_for_goto_set genchunks in
  let fixfunc_bodyhead_tbl = make_fixfunc_bodyhead_tbl genchunks in
  let topfunc_tbl = make_topfunc_tbl sigma primry_term ~static_and_primary_cfunc in
  let sibling_tbl = make_sibling_tbl sibling_entfuncs in
  let extra_arguments_tbl = make_extra_arguments_tbl ~fixfunc_fixterm_tbl ~fixterm_tbl ~topfunc_tbl ~sibling_tbl env sigma primry_term genchunks in
  let c_names_tbl = make_c_names_tbl ~fixfunc_fixterm_tbl ~used_for_call_set ~topfunc_tbl ~sibling_tbl in
  let cfunc_tbl = make_cfunc_tbl ~used_for_call_set ~sibling_tbl sigma genchunks in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:2");*)
  let closure_terms = collect_closure_terms env sigma primry_term in
  let closure_c_name_tbl = make_closure_c_name_tbl sigma closure_terms in
  let genchunks_list = split_function_genchunks genchunks in
  List.iter (fun genchunks -> show_genchunks sigma genchunks) genchunks_list;
  let entry_funcs_list =
    List.map
      (fun genchunks ->
        let bodyhead_list = List.concat_map (fun genchunk -> genchunk.genchunk_bodyhead_list) genchunks in
        List.concat_map (entfuncs_of_bodyhead ~used_for_call_set ~sibling_tbl) bodyhead_list)
      genchunks_list
  in
  let label_tbl_pairs =
    List.map2
      (fun genchunks entry_funcs ->
        match entry_funcs with
        | [] -> (Id.Map.empty, Id.Map.empty)
        | first_entfunc :: _ ->
            make_labels_tbl genchunks ~used_for_call_set ~used_for_goto_set ~sibling_tbl ~cfunc_tbl ~closure_c_name_tbl ~first_entfunc)
      genchunks_list entry_funcs_list
  in
  let fixfunc_label_tbl = disjoint_id_map_union_list (List.map fst label_tbl_pairs) in
  let closure_label_tbl = disjoint_id_map_union_list (List.map snd label_tbl_pairs) in
  let fixfunc_tbl =
    collect_fixpoints
      ~fixterm_tbl
      ~higher_order_fixfunc_tbl
      ~inlinable_fixterm_tbl
      ~used_for_call_set
      ~used_for_goto_set
      ~fixfunc_bodyhead_tbl
      ~topfunc_tbl
      ~sibling_tbl
      ~extra_arguments_tbl
      ~c_names_tbl
      ~cfunc_tbl
      ~fixfunc_label_tbl
      sigma
  in
  let closure_bodyhead_tbl = make_closure_bodyhead_tbl genchunks in
  let closure_tbl =
    collect_closures
      ~closure_bodyhead_tbl
      ~extra_arguments_tbl
      ~closure_c_name_tbl
      ~closure_label_tbl
      sigma closure_terms
  in
  show_fixfunc_table env sigma fixfunc_tbl;
  let used_vars = used_variables env sigma primry_term in
  let code_pairs = List.map2
    (fun genchunks entry_funcs ->
      let (decl, impl) =
        match entry_funcs with
        | [] -> (Pp.mt (), Pp.mt ())
        | [entfunc] ->
            gen_func_single ~fixfunc_tbl ~closure_tbl ~entfunc ~genchunks sigma used_vars
        | _ ->
            gen_func_multi ~fixfunc_tbl ~closure_tbl ~entry_funcs ~genchunks env sigma used_vars
      in
      (decl, impl))
    genchunks_list entry_funcs_list
  in
  pp_sjoinmap_list (fun (decl, impl) -> decl ++ Pp.fnl ()) code_pairs +++
  pp_sjoinmap_list (fun (decl, impl) -> impl ++ Pp.fnl ()) code_pairs

let detect_stubs (cfunc_static_ty_term_list : ((*cfunc*)string * (*static*)bool * Constr.types * Constr.t) list) :
    (*cfunc_static_ty_term_list*) ((*cfunc*)string * (*static*)bool * Constr.types * Constr.t) list *
    (*stubs*) (bool * string * string * (string * c_typedata) list * c_typedata) list =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let m = ref ConstrMap.empty in
  let acc = ref [] in
  List.iter
    (fun (cfunc, static, ty, term) ->
      match ConstrMap.find_opt term !m with
      | None ->
          let s = ref [(cfunc, static, ty, term)] in
          acc := s :: !acc;
          m := ConstrMap.add term s !m
      | Some s ->
          s := (cfunc, static, ty, term) :: !s)
    cfunc_static_ty_term_list;
  let cfunc_static_ty_term_list_list = List.rev_map (fun l -> List.rev !l) !acc in
  let cfunc_static_ty_term_list = List.map List.hd cfunc_static_ty_term_list_list in
  let stubs =
    List.concat_map
      (fun cfunc_static_ty_term_list ->
        match cfunc_static_ty_term_list with
        | [] -> assert false
        | (first_cfunc, first_static, first_ty, first_term) :: rest_cfunc_static_ty_term_list ->
            let (formal_arguments_without_void, return_type) = c_args_without_void_and_ret_type env sigma (EConstr.of_constr first_ty) in
            List.map
              (fun (cfunc, static, ty, term) -> (static, cfunc, first_cfunc, formal_arguments_without_void, return_type))
              rest_cfunc_static_ty_term_list)
      cfunc_static_ty_term_list_list
  in
  (cfunc_static_ty_term_list, stubs)

let gen_stub_sibling_functions (stub_sibling_entries : (bool * string * string * (string * c_typedata) list * c_typedata) list) : Pp.t =
  pp_sjoinmap_list
    (fun (static, cfunc_name_to_define, cfunc_name_to_call, formal_arguments_without_void, return_type) ->
      Pp.v 0 (
        gen_function_header ~static return_type cfunc_name_to_define formal_arguments_without_void +++
        vbrace (
          Pp.hov 0 (
            (if c_type_is_void return_type then
              Pp.mt ()
            else
              Pp.str "return") +++
            Pp.str cfunc_name_to_call ++
            Pp.str "(" ++
            pp_joinmap_list (Pp.str "," ++ Pp.spc ())
              (fun (c_arg, c_ty) -> Pp.str c_arg)
              formal_arguments_without_void ++
            Pp.str ");"))))
    stub_sibling_entries

let gen_function (cfunc_names : string list) : Pp.t =
  match cfunc_names with
  | [] -> user_err (Pp.str "[codegen:bug] gen_function with empty cfunc_names")
  | cfuncs ->
      let cfunc_static_ty_term_list =
        List.map
          (fun cfunc ->
            let (static, ty, term) = make_simplified_for_cfunc cfunc in
            (cfunc, static, ty, term))
          cfuncs
      in
      let (cfunc_static_ty_term_list, stubs) = detect_stubs cfunc_static_ty_term_list in
      local_gensym_with (fun () -> gen_func_sub cfunc_static_ty_term_list) +++
      gen_stub_sibling_functions stubs

let gen_prototype (cfunc_name : string) : Pp.t =
  let (static, ty, whole_term) = make_simplified_for_cfunc cfunc_name in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments_without_void, return_type) = c_args_without_void_and_ret_type env sigma whole_ty in
  gen_function_header ~static return_type cfunc_name formal_arguments_without_void ++ Pp.str ";"

let common_key_for_siblings (term : Constr.t) : (int * Constr.t) option =
  let (args, body) = Term.decompose_lam term in
  match Constr.kind body with
  | Fix ((ks, j), (nary, tary, fary)) ->
      Some (j, Term.compose_lam args (Constr.mkFix ((ks, 0), (nary, tary, fary))))
  | _ -> None

let codegen_detect_siblings (gen_list : code_generation list) : code_generation list =
  let map = ref ConstrMap.empty in
  let gens = List.map
    (fun gen ->
      gen,
      (match gen with
      | GenFunc cfunc ->
          let (static, ty, term) = make_simplified_for_cfunc cfunc in
          (match common_key_for_siblings term with
          | Some (j, key) as jkey ->
              map := ConstrMap.update
                key
                (fun njs_opt ->
                  match njs_opt with
                  | None -> Some [(cfunc, j)]
                  | Some njs -> Some ((cfunc, j) :: njs))
                !map;
              jkey
          | None -> None)
      | _ -> None))
    gen_list
  in
  CList.map_filter (* assumes CList.map_filter invokes the function left-to-right order *)
    (fun (gen, jkey_opt) ->
      match jkey_opt with
      | None -> Some gen
      | Some (j, key) ->
          (match ConstrMap.find_opt key !map with
          | Some njs ->
              (match njs with
              | [] -> assert false
              | [(cfunc, j)] -> Some (GenFunc cfunc)
              | _ ->
                  map := ConstrMap.remove key !map;
                  let njs = List.sort (fun (_,j1) (_,j2) -> Int.compare j1 j2) njs in
                  let cfuncs = List.map fst njs in
                  msg_info_hov (Pp.str "[codegen] mutually recursive functions detected:" +++ pp_sjoinmap_list Pp.str cfuncs);
                  Some (GenMutual cfuncs))
          | None -> None))
    gens

let gen_pp_iter (f : Pp.t -> unit) (gen_list : code_generation list) : unit =
  List.iter
    (fun gen ->
      match gen with
      | GenFunc cfunc_name ->
          f (Pp.v 0 (gen_function [cfunc_name] ++ Pp.fnl ()))
      | GenMutual cfunc_names ->
          f (Pp.v 0 (gen_function cfunc_names ++ Pp.fnl ()))
      | GenPrototype cfunc_name ->
          f (Pp.v 0 (gen_prototype cfunc_name ++ Pp.fnl ()))
      | GenSnippet str ->
          f (Pp.v 0 (Pp.str str ++ Pp.fnl ())))
    gen_list

let complete_gen_map (gflist : genflag list) (gen_map : (code_generation list) CString.Map.t) : (code_generation list) CString.Map.t =
  let gen_map =
    if List.mem DisableDependencyResolver gflist then gen_map
    else CString.Map.map codegen_resolve_dependencies gen_map in
  let gen_map =
    if List.mem DisableMutualRecursionDetection gflist then gen_map
    else CString.Map.map codegen_detect_siblings gen_map in
  gen_map

(* Vernacular commands *)

let command_gen (cfunc_list : string_or_qualid list) : unit =
  let gen_list =
    List.map
      (fun arg ->
        match arg with
        | StrOrQid_Str cfunc_name ->
            GenFunc cfunc_name
        | StrOrQid_Qid qid ->
          let env = Global.env () in
          let sigma = Evd.from_env env in
          let func = func_of_qualid env qid in
          let sp_cfg = codegen_auto_arguments_internal env sigma func in
          (if List.mem SorD_S sp_cfg.sp_sd_list then
            user_err (Pp.str "[codegen] function has static arguments:" +++ Printer.pr_constr_env env sigma func));
          let (env, sp_inst) =
            match ConstrMap.find_opt func sp_cfg.sp_instance_map with
            | None -> codegen_define_instance env sigma CodeGenFunc func [] None
            | Some sp_inst -> (env, sp_inst)
          in
          GenFunc sp_inst.sp_cfunc_name)
      cfunc_list
  in
  (* Don't call codegen_resolve_dependencies.
     CodeGen Gen is used to test code generation of specified functions.
     Generating non-specified functions would make result longer with uninteresting functions. *)
  let gen_list = codegen_detect_siblings gen_list in
  gen_pp_iter Feedback.msg_info gen_list

let gen_file (fn : string) (gen_list : code_generation list) : unit =
  (* open in the standard permission, 0o666, which will be masked by umask. *)
  (let (temp_fn, ch) = Filename.open_temp_file
    ~perms:0o666 ~temp_dir:(Filename.dirname fn) (Filename.basename fn) ".c" in
  let fmt = Format.formatter_of_out_channel ch in
  gen_pp_iter (Pp.pp_with fmt) gen_list;
  Format.pp_print_flush fmt ();
  close_out ch;
  Sys.rename temp_fn fn;
  msg_info_hov (Pp.str ("[codegen] file generated: " ^ fn)))

let command_generate_file (gflist : genflag list) : unit =
  let gen_map = complete_gen_map gflist !generation_map in
  List.iter
    (fun (fn, gen_list) -> gen_file fn (List.rev gen_list))
    (CString.Map.bindings gen_map);
  generation_map := CString.Map.empty

let command_generate_test (gflist : genflag list) : unit =
  let gen_map = complete_gen_map gflist !generation_map in
  List.iter
    (fun (fn, gen_list) ->
      Feedback.msg_info (Pp.str fn);
      gen_pp_iter Feedback.msg_info (List.rev gen_list))
    (CString.Map.bindings gen_map)
