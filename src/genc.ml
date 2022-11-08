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

type fixterm_t = {
  fixterm_term_id: Id.t;
  fixterm_tail_position: bool;
  fixterm_term_env: Environ.env;
  fixterm_inlinable: bool;
}

type fixfunc_t = {
  fixfunc_fixterm: fixterm_t;
  fixfunc_func_id: Id.t;
  fixfunc_used_as_call: bool;
  fixfunc_used_as_goto: bool;
  fixfunc_formal_arguments: (string * c_typedata) list; (* [(varname1, vartype1); ...] *) (* vartype may be void *)
  fixfunc_return_type: c_typedata; (* may be void. *)
  fixfunc_is_higher_order: bool; (* means that arguments contain function *)

  fixfunc_topfunc: (bool * string) option; (* (static, cfunc_name) *) (* by fixfunc_initialize_topfunc *)
  fixfunc_sibling: (bool * string) option; (* (static, cfunc_name) *) (* by fixfunc_initialize_siblings *)
  fixfunc_c_name: string; (* by fixfunc_initialize_c_names *)

  fixfunc_cfunc : (bool * string) option; (* (static, cfunc_name) *) (* by fixfunc_initialize_c_call *)

  fixfunc_label : string option; (* by fixfunc_initialize_labels *)

  fixfunc_extra_arguments: (string * c_typedata) list; (* [(varname1, vartype1); ...] *) (* by fixfunc_initialize_extra_arguments *)
  (* extra arguments are mostly same for fix-bouded functions in a fix-term.
    However, they can be different for primary function and siblings.
    In such case, extra arguments are all bounded variables by lambda and let-in and not filtered. *)
}

type fixfunc_table = (Id.t, fixfunc_t) Hashtbl.t

let fixfunc_entry_label (c_name : string) : string = "entry_" ^ c_name
let fixfunc_exit_label (c_name : string) : string = "exit_" ^ c_name

let cfunc_of_fixfunc (fixfunc : fixfunc_t) : string =
  snd (Option.get fixfunc.fixfunc_cfunc)

type closure_t = {
  closure_id: Id.t;
  closure_c_name: string;
  closure_c_func_type: c_typedata;
  closure_c_return_type: c_typedata;
  closure_label : string option; (* by fixfunc_initialize_labels *)
  closure_args: (string * c_typedata) list;
  closure_vars: (string * c_typedata) list;
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

type body_root_t =
| BodyRootTopFunc of (bool * string) (* (static, primary_cfunc) *)
| BodyRootClosure of Id.t (* closure_id *)
| BodyRootFixfunc of Id.t (* fixfunc_id *)

type body_var_t =
| BodyVarFixfunc of Id.t (* fixfunc_id *)
| BodyVarArg of (string * c_typedata)
| BodyVarVoidArg of (string * c_typedata)

type bodyhead_t = body_root_t * body_var_t list (* 2nd component (body_vars) is outermost first (left to right) *)

type bodychunk_t = {
  bodychunk_return_type : c_typedata;
  bodychunk_fargs : (string * c_typedata) list; (* outermost first (left to right) *)
  bodychunk_bodyhead_list : bodyhead_t list;
  bodychunk_env : Environ.env;
  bodychunk_exp : EConstr.t;
  bodychunk_fixfunc_impls : Id.Set.t;
  bodychunk_fixfunc_gotos : Id.Set.t;
  bodychunk_fixfunc_calls : Id.Set.t;
  bodychunk_closure_impls : Id.Set.t;
}

type body_entry_t =
| BodyEntryTopFunc of (bool * string) (* (static, primary_cfunc) *)
| BodyEntryFixfunc of Id.t (* fixfunc_id *)
| BodyEntryClosure of Id.t (* closure_id *)

let show_fixfunc_table (env : Environ.env) (sigma : Evd.evar_map) (fixfunc_tbl : fixfunc_table) : unit =
  Hashtbl.iter
    (fun fixfunc_id fixfunc ->
      msg_debug_hov (Pp.str "[codegen:show_fixfunc_table]" +++
        Pp.str (Id.to_string fixfunc_id) ++ Pp.str ":" +++
        Pp.v 0 (
        Pp.str "inlinable=" ++ Pp.bool fixfunc.fixfunc_fixterm.fixterm_inlinable +++
        Pp.str "tail_position=" ++ Pp.bool fixfunc.fixfunc_fixterm.fixterm_tail_position +++
        Pp.str "used_as_call=" ++ Pp.bool fixfunc.fixfunc_used_as_call +++
        Pp.str "used_as_goto=" ++ Pp.bool fixfunc.fixfunc_used_as_goto +++
        Pp.str "formal_arguments=(" ++
          pp_joinmap_list (Pp.str ",")
            (fun (farg, c_ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str (compose_c_abstract_decl c_ty))
            fixfunc.fixfunc_formal_arguments ++ Pp.str ")" +++
        Pp.str "return_type=" ++ Pp.str (compose_c_abstract_decl fixfunc.fixfunc_return_type) +++
        Pp.str "topfunc=" ++ (match fixfunc.fixfunc_topfunc with None -> Pp.str "None" | Some (static,cfunc) -> Pp.str ("Some(" ^ (if static then "true" else "false") ^ "," ^ cfunc ^ ")")) +++
        Pp.str "sibling=" ++ (match fixfunc.fixfunc_sibling with None -> Pp.str "None" | Some (static,cfunc) -> Pp.str ("Some(" ^ (if static then "true" else "false") ^ "," ^ cfunc ^ ")")) +++
        Pp.str "c_name=" ++ Pp.str fixfunc.fixfunc_c_name +++
        Pp.str "fixfunc_cfunc=" ++ (match fixfunc.fixfunc_cfunc with None -> Pp.str "None" | Some (static,cfunc) -> Pp.str ("Some(" ^ (if static then "true" else "false") ^ "," ^ cfunc ^ ")")) +++
        Pp.str "fixfunc_label=" ++ Pp.str (match fixfunc.fixfunc_label with None -> "None" | Some s -> "(Some " ^ s ^ ")") +++
        Pp.str "extra_arguments=(" ++ pp_joinmap_list (Pp.str ",") (fun (farg, c_ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str (compose_c_abstract_decl c_ty)) fixfunc.fixfunc_extra_arguments ++ Pp.str ")" +++
        Pp.mt ())
      ))
    fixfunc_tbl

let _ = ignore show_fixfunc_table

let show_bodychunks (sigma : Evd.evar_map) (bodychunks : bodychunk_t list) : unit =
  msg_debug_hov (Pp.str "[codegen:show_bodychunks]" +++
    pp_sjoinmap_list
      (fun bodychunk ->
        Pp.hv 2 (
          Pp.hov 2 (Pp.str "bodyhead_list=[" ++
            Pp.hov 0 (
            pp_sjoinmap_list
              (fun (bodyroot, bodyvars) ->
                (match bodyroot with
                | BodyRootTopFunc (static,primary_cfunc) -> Pp.str ("TopFunc:" ^ primary_cfunc ^ if static then "(static)" else "")
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
                  bodyvars) ++
                  Pp.str "]")
              bodychunk.bodychunk_bodyhead_list)
            ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "fargs=[" ++
            pp_sjoinmap_list (fun (varname, vartype) -> Pp.str varname ++ Pp.str ":" ++ pr_c_abstract_decl vartype) bodychunk.bodychunk_fargs ++
            Pp.str "]") +++
          Pp.hov 2 (Pp.str "return_type=" ++ pr_c_abstract_decl bodychunk.bodychunk_return_type) +++
          Pp.hov 2 (Pp.str "fixfunc_impls=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements bodychunk.bodychunk_fixfunc_impls) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "fixfunc_gotos=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements bodychunk.bodychunk_fixfunc_gotos) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "fixfunc_calls=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements bodychunk.bodychunk_fixfunc_calls) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "closure_impls=[" ++ pp_sjoinmap_list Id.print (Id.Set.elements bodychunk.bodychunk_closure_impls) ++ Pp.str "]") +++
          Pp.hov 2 (Pp.str "bodychunk=" +++ Printer.pr_econstr_env bodychunk.bodychunk_env sigma bodychunk.bodychunk_exp)
          ))
      bodychunks)

let _ = ignore show_bodychunks

let rec c_args_and_ret_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((string * c_typedata) list) * c_typedata =
  match EConstr.kind sigma term with
  | Prod (x,t,b) ->
      let env2 = env_push_assum env x t in
      let (rest_args, ret_type) = c_args_and_ret_type env2 sigma b in
      (((str_of_annotated_name x, c_typename env sigma t) :: rest_args), ret_type)
  | _ ->
      ([], c_typename env sigma term)

let disjoint_id_map_union (m1 : 'a Id.Map.t) (m2 : 'a Id.Map.t) =
  Id.Map.union
    (fun id b1 b2 -> user_err (Pp.str "[codegen:bug] unexpected duplicated variable name:" +++ Id.print id))
    m1 m2

let disjoint_id_map_union_ary (ms : 'a Id.Map.t array) : 'a Id.Map.t =
  Array.fold_left
    (fun m0 m1 ->
      disjoint_id_map_union m0 m1)
    Id.Map.empty ms

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

let rec detect_higher_order_fixfunc (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool Id.Map.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:detect_higher_order_fixfunc] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:detect_higher_order_fixfunc] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i -> Id.Map.empty
  | Const _ | Construct _ -> Id.Map.empty
  | Proj _ -> Id.Map.empty
  | App (f, args) ->
      detect_higher_order_fixfunc env sigma f
  | LetIn (x,e,t,b) ->
      let env2 = env_push_def env x e t in
      let m1 = detect_higher_order_fixfunc env sigma e in
      let m2 = detect_higher_order_fixfunc env2 sigma b in
      disjoint_id_map_union m1 m2
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let ms = Array.map2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          detect_higher_order_fixfunc env2 sigma body)
        bl bl0
      in
      disjoint_id_map_union_ary ms
  | Lambda (x,t,b) ->
      let env2 = env_push_assum env x t in
      detect_higher_order_fixfunc env2 sigma b
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ms = Array.map (detect_higher_order_fixfunc env2 sigma) fary in
      let m = disjoint_id_map_union_ary ms in
      let m = CArray.fold_left2
        (fun m x t -> Id.Map.add (id_of_annotated_name x) (is_higher_order_function env sigma t) m)
        m nary tary
      in
      m

(*
  detect_inlinable_fixterm implementes TR[term]_numargs in doc/codegen.tex.
*)
(*
  detect_inlinable_fixterm_rec implements (R,N,T) = RNT[term] in doc/codegen.tex.
  R is a map from fix-bounded IDs to bool.
  R[n] = true if n is fix-bounded function which is inlinable (only used for goto so do not need to be a real function).
  R[n] = false if n is fix-bounded function not inlinable.
  R can also be usable to determine an ID is fix-bounded function or not.
*)
let detect_inlinable_fixterm ~(higher_order_fixfuncs : bool Id.Map.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool Id.Map.t =
  let rec detect_inlinable_fixterm_lamfix (env : Environ.env) (term : EConstr.t) :
      (* this lambda/fix is inlinable or not *) bool *
      (* fixterms inlinable or not *) bool Id.Map.t *
      (* variables at non-tail position *) IntSet.t *
      (* variables at tail position *) IntSet.t =
    (*msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_lamfix] start:" +++
      Printer.pr_econstr_env env sigma term); *)
    let result = detect_inlinable_fixterm_lamfix1 env term in
    (*
    let (tailrec_fixfuncs, nontailset, tailset) = result in
    msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_lamfix] end:" +++
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
  and detect_inlinable_fixterm_lamfix1 (env : Environ.env) (term : EConstr.t) :
      (* this lambda/fix is inlinable or not *) bool *
      (* fixterms inlinable or not *) bool Id.Map.t *
      (* variables at non-tail position *) IntSet.t *
      (* variables at tail position *) IntSet.t =
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:detect_inlinable_fixterm_lamfix] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ ->
        user_err (Pp.str "[codegen:detect_inlinable_fixterm_lamfix] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Lambda (x,t,b) ->
        let env2 = env_push_assum env x t in
        let (inlinable_here, inlinablemap_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_lamfix env2 b in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        (inlinable_here, inlinablemap_b, nontailset_b, tailset_b)
    | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
        let h = Array.length nary in
        let env2 = EConstr.push_rec_types prec env in
        let fixfuncs_result = Array.map (detect_inlinable_fixterm_lamfix env2) fary in
        let inlinable_here_fs = Array.for_all (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> inlinable_here) fixfuncs_result in
        let tailset_fs = intset_union_ary (Array.map (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> tailset_f) fixfuncs_result) in
        let nontailset_fs = intset_union_ary (Array.map (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> nontailset_f) fixfuncs_result) in
        let inlinablemap_fs = disjoint_id_map_union_ary (Array.map (fun (inlinable_here, inlinablemap_f, nontailset_f, tailset_f) -> inlinablemap_f) fixfuncs_result) in
        let fixfunc_referenced_at_nontail_position = IntSet.exists ((>=) h) nontailset_fs in
        let tailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) tailset_fs) in
        let nontailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) nontailset_fs) in
        let fixterm_is_higher_order = Array.exists (fun x -> Id.Map.find (id_of_annotated_name x) higher_order_fixfuncs) nary in
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
        let (inlinablemap, nontailset, tailset) = detect_inlinable_fixterm_exp env term in
        (true, inlinablemap, nontailset, tailset)
  and detect_inlinable_fixterm_exp (env : Environ.env) (term : EConstr.t) :
      (* fixterms inlinable or not *) bool Id.Map.t *
      (* variables at non-tail position *) IntSet.t *
      (* variables at tail position *) IntSet.t =
    (*msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_exp] start:" +++
      Printer.pr_econstr_env env sigma term); *)
    let result = detect_inlinable_fixterm_exp1 env term in
    (*
    let (tailrec_fixfuncs, nontailset, tailset) = result in
    msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_exp] end:" +++
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
  and detect_inlinable_fixterm_exp1 (env : Environ.env) (term : EConstr.t) :
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
        user_err (Pp.str "[codegen:detect_inlinable_fixterm_exp] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
        user_err (Pp.str "[codegen:detect_inlinable_fixterm_exp] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Rel i -> (Id.Map.empty, args_set, IntSet.singleton i)
    | Const _ | Construct _ -> (Id.Map.empty, args_set, IntSet.empty)
    | Proj (proj, e) ->
        (* e must be a Rel which type is inductive (non-function) type *)
        (Id.Map.empty, IntSet.empty, IntSet.empty)
    | LetIn (x,e,t,b) ->
        let env2 = env_push_def env x e t in
        let (inlinablemap_e, nontailset_e, tailset_e) = detect_inlinable_fixterm_exp env e in
        let (inlinablemap_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_exp env2 b in
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
            let (inlinablemap_br, nontailset_br, tailset_br) = detect_inlinable_fixterm_exp env2 body in
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
          let (inlinable_here, inlinablemap, nontailset, tailset) = detect_inlinable_fixterm_lamfix env term in
          let nontailset' = IntSet.union tailset nontailset in
          (inlinablemap, nontailset', IntSet.empty)
        else
          assert false
    | Fix _ ->
        if CArray.is_empty args then (* closure creation *)
          let (inlinable_here, inlinablemap, nontailset, tailset) = detect_inlinable_fixterm_lamfix env term in
          let nontailset' = IntSet.union tailset nontailset in
          (inlinablemap, nontailset', IntSet.empty)
        else
          let (inlinable_here, inlinablemap, nontailset, tailset) = detect_inlinable_fixterm_lamfix env term in
          (inlinablemap, IntSet.union nontailset args_set, tailset)
  in
  let (inlinable_here, inlinablemap, nontailset, tailset) = detect_inlinable_fixterm_lamfix env term in
  inlinablemap

(*
  collect_fix_usage collects information for each fix-terms and fix-bounded functions.

  collect_fix_usage tracks the term will be translated by gen_head or gen_tail.
  tail_position=false means that term will be translated by gen_head.
  tail_position=true means that term will be translated by gen_tail.
*)

type fixacc_t = {
  fixacc_used_as_call : bool ref;
  fixacc_used_as_goto : bool ref;
}

let make_fixfunc_table (fixfuncs : fixfunc_t list) : fixfunc_table =
  let fixfunc_tbl = Hashtbl.create 0 in
  List.iter (fun fixfunc -> Hashtbl.add fixfunc_tbl fixfunc.fixfunc_func_id fixfunc) fixfuncs;
  fixfunc_tbl

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

let collect_fix_usage
    ~(higher_order_fixfuncs : bool Id.Map.t)
    ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    fixfunc_table =
  let rec collect_fix_usage_rec
      ~(under_fix_or_lambda : bool)
      (env : Environ.env) (sigma : Evd.evar_map)
      (tail_position : bool) (term : EConstr.t)
      ~(fixaccs : fixacc_t list) :
      fixfunc_t Seq.t =
    let result = collect_fix_usage_rec1 ~under_fix_or_lambda env sigma tail_position term ~fixaccs in
    result
  and collect_fix_usage_rec1
      ~(under_fix_or_lambda : bool)
      (env : Environ.env) (sigma : Evd.evar_map)
      (tail_position : bool) (term : EConstr.t)
      ~(fixaccs : fixacc_t list) :
      fixfunc_t Seq.t =
    let (term, args) = decompose_appvect sigma term in
    let numargs = Array.length args in
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:collect_fix_usage_rec] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ ->
        user_err (Pp.str "[codegen:collect_fix_usage_rec] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Rel i ->
        ((if 0 < numargs then
          let id = id_of_name (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)) in
          match Id.Map.find_opt id inlinable_fixterms with
          | None -> () (* term is not fix-bounded function *)
          | Some fixterm_is_inlinable ->
              let fixacc = List.nth fixaccs (i-1) in
              let fixfunc_is_higher_order = Id.Map.find id higher_order_fixfuncs in
              determine_fixfunc_call_or_goto tail_position fixfunc_is_higher_order fixterm_is_inlinable
                ~call:(fun () -> fixacc.fixacc_used_as_call := true)
                ~goto:(fun () -> fixacc.fixacc_used_as_goto := true));
        Seq.empty)
    | Const _ | Construct _ -> Seq.empty
    | Proj (proj, e) ->
        (* e must be a Rel which type is inductive (non-function) type *)
        Seq.empty
    | App (f, args) ->
        collect_fix_usage_rec ~under_fix_or_lambda env sigma tail_position f ~fixaccs
    | LetIn (x,e,t,b) ->
        let env2 = env_push_def env x e t in
        let fixaccs2 = { fixacc_used_as_call = ref false;
                         fixacc_used_as_goto = ref false; } :: fixaccs in
        let fixfuncs1 = collect_fix_usage_rec ~under_fix_or_lambda:false env sigma false e ~fixaccs in
        let fixfuncs2 = collect_fix_usage_rec ~under_fix_or_lambda:false env2 sigma tail_position b ~fixaccs:fixaccs2 in
        Seq.append fixfuncs1 fixfuncs2
    | Case (ci,u,pms,p,iv,item,bl) ->
        let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
        (* item cannot contain fix-term because item must be a Rel which type is inductive (non-function) type *)
        let results = Array.map2
          (fun (nas,body) (ctx,_) ->
            let env2 = EConstr.push_rel_context ctx env in
            let n = Array.length nas in
            let fixaccs2 =
              List.append
                (List.init n (fun _ -> { fixacc_used_as_call = ref false;
                                         fixacc_used_as_goto = ref false; }))
                fixaccs
            in
            collect_fix_usage_rec ~under_fix_or_lambda:false env2 sigma
              tail_position body ~fixaccs:fixaccs2)
          bl bl0
        in
        concat_array_seq results
    | Lambda (x,t,b) ->
        let env2 = env_push_assum env x t in
        let fixaccs2 = { fixacc_used_as_call = ref false;
                         fixacc_used_as_goto = ref false; } :: fixaccs in
        if numargs = 0 && not under_fix_or_lambda then
          (* closure creation *)
          collect_fix_usage_rec ~under_fix_or_lambda:true env2 sigma true b ~fixaccs:fixaccs2
        else
          collect_fix_usage_rec ~under_fix_or_lambda:true env2 sigma tail_position b ~fixaccs:fixaccs2
    | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
        let fixterm_id = id_of_annotated_name nary.(j) in
        let inlinable = Id.Map.find (id_of_annotated_name nary.(j)) inlinable_fixterms in
        let h = Array.length nary in
        let env2 = EConstr.push_rec_types prec env in
        let fixfunc_is_higher_order_ary = Array.map (is_higher_order_function env sigma) tary in
        let fixaccs2 =
          list_rev_map_append
            (fun i ->
              { fixacc_used_as_call = ref (j = i && not tail_position && not inlinable);
                fixacc_used_as_goto = ref false; })
            (iota_list 0 h)
            fixaccs
        in
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
            (fun t f -> collect_fix_usage_rec ~under_fix_or_lambda:true env2 sigma
              tail_position2 f ~fixaccs:fixaccs2)
            tary fary
        in
        let fixterm = {
          fixterm_term_id = fixterm_id;
          fixterm_tail_position = tail_position;
          fixterm_term_env = env;
          fixterm_inlinable = inlinable;
        } in
        let fixfuncs =
          Array.to_seq
            (CArray.map2_i
              (fun i name ty ->
                let fixacc = List.nth fixaccs2 (h - i - 1) in
                let (formal_arguments, return_type) = c_args_and_ret_type env sigma ty in
                {
                  fixfunc_fixterm = fixterm;
                  fixfunc_func_id = id_of_annotated_name nary.(i);
                  fixfunc_used_as_call = !(fixacc.fixacc_used_as_call);
                  fixfunc_used_as_goto = !(fixacc.fixacc_used_as_goto);
                  fixfunc_formal_arguments = formal_arguments;
                  fixfunc_return_type = return_type;
                  fixfunc_is_higher_order = fixfunc_is_higher_order_ary.(i);
                  fixfunc_topfunc = None; (* dummy. updated by fixfunc_initialize_topfunc *)
                  fixfunc_sibling = None; (* dummy. updated by fixfunc_initialize_siblings *)
                  fixfunc_c_name = "dummy"; (* dummy. updated by fixfunc_initialize_c_names *)
                  fixfunc_cfunc = None; (* dummy. updated by fixfunc_initialize_c_call *)
                  fixfunc_label = None; (* dummy. updated by fixfunc_initialize_labels *)
                  fixfunc_extra_arguments = []; (* dummy. updated by fixfunc_initialize_extra_arguments *)
                })
              nary tary)
        in
        Seq.append fixfuncs (concat_array_seq results)
  in
  let fixfuncs = collect_fix_usage_rec ~under_fix_or_lambda:false env sigma true term ~fixaccs:[] in
  make_fixfunc_table (List.of_seq fixfuncs)

let fixfunc_initialize_topfunc (sigma : Evd.evar_map) (term : EConstr.t) ~(static_and_primary_cfunc : bool * string) ~(fixfunc_tbl : fixfunc_table) : unit =
  let (fargs, term') = decompose_lam sigma term in
  match EConstr.kind sigma term' with
  | Fix ((ks, j), (nary, tary, fary)) ->
      let fixfunc_id = id_of_annotated_name nary.(j) in
      let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
      Hashtbl.replace fixfunc_tbl fixfunc_id
        { fixfunc with
          fixfunc_topfunc = Some static_and_primary_cfunc }
  | _ -> ()

let fixfunc_initialize_siblings (sibling_entfuncs : (bool * string * int * Id.t) list) ~(fixfunc_tbl : fixfunc_table) : unit =
  List.iter
    (fun (static, sibling_cfunc_name, i, fixfunc_id) ->
      let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
      Hashtbl.replace fixfunc_tbl fixfunc_id
        { fixfunc with
          fixfunc_sibling = Some (static, sibling_cfunc_name) })
    sibling_entfuncs

let fixfunc_initialize_c_names (fixfunc_tbl : fixfunc_table) : unit =
  Hashtbl.filter_map_inplace
    (fun (fixfunc_id : Id.t) (fixfunc : fixfunc_t) ->
      let c_name =
        match fixfunc.fixfunc_topfunc, fixfunc.fixfunc_sibling with
        | Some (_,cfunc), _ -> cfunc
        | None, Some (_,cfunc) -> cfunc
        | None, None ->
            if fixfunc.fixfunc_used_as_call then
              global_gensym_with_id fixfunc_id
            else
              Id.to_string fixfunc_id
      in
      Some { fixfunc with fixfunc_c_name = c_name })
    fixfunc_tbl

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

let pr_extra_argument (exarg : (string * string) list) : Pp.t =
  Pp.str "[" ++
  pp_joinmap_list (Pp.str ",")
    (fun (x,t) -> Pp.str "(" ++ Pp.str x ++ Pp.str "," ++ Pp.str t ++ Pp.str ")")
    exarg ++
  Pp.str "]"

let check_eq_extra_arguments exarg1 exarg2 =
  if exarg1 <> exarg2 then
    user_err (Pp.str "[codegen:bug] exargs length differ:" +++ pr_extra_argument exarg1 +++ Pp.str "<>" +++ pr_extra_argument exarg2)

let _ = ignore check_eq_extra_arguments

(*
  compute_naive_extra_arguments computes extra arguments in "naive" way:
  It contains all variables in env except fix-bounded functions.
  Note that the result is ordered from outside to inside of the term.
*)
let compute_naive_extra_arguments ~(fixfunc_tbl : fixfunc_table) (env : Environ.env) (sigma : Evd.evar_map) : (string * c_typedata) list =
  let n = Environ.nb_rel env in
  let exargs = ref [] in
  for i = 1 to n do
    let decl = Environ.lookup_rel i env in
    let x = Context.Rel.Declaration.get_name decl in
    let t = Context.Rel.Declaration.get_type decl in
    let id = id_of_name x in
    if not (Hashtbl.mem fixfunc_tbl id) then (* Don't include fix-bounded functions *)
      let c_ty = c_typename env sigma (EConstr.of_constr t) in
      if not (c_type_is_void c_ty) then
        exargs := (str_of_name x, c_ty) :: !exargs
  done;
  !exargs

let compute_precise_extra_arguments
    ~(fixfunc_tbl : fixfunc_table)
    (env : Environ.env) (sigma : Evd.evar_map)
    (fixterm_free_variables : (Id.t, Id.Set.t) Hashtbl.t) :
    ((*fixterm_id*)Id.t, (*extra_arguments*)Id.Set.t) Hashtbl.t =
  let fixfunc_ids =
    Hashtbl.fold
      (fun fixfunc_id fixfunc set ->
        Id.Set.add fixfunc_id set)
      fixfunc_tbl
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
          match Hashtbl.find_opt fixfunc_tbl id with
          | None -> ()
          | Some fixfunc2 ->
            let fixterm2_id = fixfunc2.fixfunc_fixterm.fixterm_term_id in
            match Hashtbl.find_opt fixterm_free_variables fixterm2_id with
            | None -> ()
            | Some fv ->
                q := Id.Set.union !q fv)
      done;
      Hashtbl.add fixterm_extra_arguments fixterm_id
        (Id.Set.diff !extra_arguments fixfunc_ids))
    fixterm_free_variables;
  fixterm_extra_arguments

let fixfunc_initialize_extra_arguments
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t)
    (bodychunks : bodychunk_t list)
    ~(fixfunc_tbl : fixfunc_table) : unit =
  let fixterm_free_variables = fixterm_free_variables env sigma term in
  let precise_extra_arguments_sets = compute_precise_extra_arguments ~fixfunc_tbl env sigma fixterm_free_variables in
  let bodyhead_list = List.concat_map (fun bodychunk -> bodychunk.bodychunk_bodyhead_list) bodychunks in
  List.iter
    (fun (bodyroot, bodyvars) ->
      let fixfuncs =
        List.filter_map
          (function
            | BodyVarFixfunc fixfunc_id -> Some (Hashtbl.find fixfunc_tbl fixfunc_id)
            | _ -> None)
          bodyvars
      in
      match fixfuncs with
      | [] -> ()
      | fixfunc :: inner_fixfuncs ->
          let naive_extra_arguments = compute_naive_extra_arguments ~fixfunc_tbl fixfunc.fixfunc_fixterm.fixterm_term_env sigma in
          let extra_arguments =
            match fixfunc.fixfunc_topfunc, fixfunc.fixfunc_sibling with
            | None, None ->
                let precise_set = Hashtbl.find precise_extra_arguments_sets fixfunc.fixfunc_fixterm.fixterm_term_id in
                List.filter
                  (fun (varname, vartype) ->
                    Id.Set.mem (Id.of_string varname) precise_set)
                  naive_extra_arguments
            | _, _ ->
                naive_extra_arguments
          in
          Hashtbl.replace fixfunc_tbl fixfunc.fixfunc_func_id
            { fixfunc with
              fixfunc_extra_arguments = extra_arguments };
          let bodyvars1 = List.tl (list_find_suffix (function BodyVarFixfunc fixfunc_id -> Id.equal fixfunc_id fixfunc.fixfunc_func_id | _ -> false) bodyvars) in
          let rev_exargs = ref (List.rev extra_arguments) in
          List.iter
            (function
              | BodyVarArg (var, c_ty) ->
                  rev_exargs := (var, c_ty) :: !rev_exargs
              | BodyVarVoidArg _ -> ()
              | BodyVarFixfunc fixfunc_id ->
                  let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
                  Hashtbl.replace fixfunc_tbl fixfunc.fixfunc_func_id
                    { fixfunc with
                      fixfunc_extra_arguments = List.rev !rev_exargs })
            bodyvars1)
    bodyhead_list

let fixfunc_initialize_c_call
    (sigma : Evd.evar_map) (bodychunks : bodychunk_t list) ~(fixfunc_tbl : fixfunc_table) : unit =
  let bodyhead_list = List.concat_map (fun bodychunk -> bodychunk.bodychunk_bodyhead_list) bodychunks in
  List.iter
    (fun (bodyroot, bodyvars) ->
      let fixfuncs =
        List.filter_map
          (function
            | BodyVarFixfunc fixfunc_id -> Some (Hashtbl.find fixfunc_tbl fixfunc_id)
            | _ -> None)
          bodyvars
      in
      let static_and_cfunc_name =
        match bodyroot with
        | BodyRootTopFunc (static, primary_cfunc)  -> Some (static, primary_cfunc)
        | BodyRootClosure _
        | BodyRootFixfunc _ ->
            match fixfuncs with
            | [] -> None
            | first_fixfunc :: rest_fixfuncs ->
                match first_fixfunc.fixfunc_sibling with
                | Some (sibling_static, sibling_cfunc_name) -> Some (sibling_static, sibling_cfunc_name)
                | None ->
                    let used_as_call = List.exists (fun fixfunc -> fixfunc.fixfunc_used_as_call) fixfuncs in
                    if used_as_call then
                      Some (true, global_gensym_with_id first_fixfunc.fixfunc_func_id)
                    else
                      None
      in
      match static_and_cfunc_name with
      | Some (static, cfunc_name) ->
          List.iter
            (fun fixfunc ->
              Hashtbl.replace fixfunc_tbl fixfunc.fixfunc_func_id
                { fixfunc with
                  fixfunc_cfunc = Some (static, cfunc_name); })
            fixfuncs
      | None -> ())
    bodyhead_list

let fixfunc_initialize_labels (bodychunks : bodychunk_t list) ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) : unit =
  let bodyhead_list = List.concat_map (fun bodychunk -> bodychunk.bodychunk_bodyhead_list) bodychunks in
  List.iteri
    (fun i (bodyroot, bodyvars) ->
      msg_debug_hov (Pp.str "[codegen:fixfunc_initialize_labels]" +++
        Pp.str "i=" ++ Pp.int i +++
        Pp.str "bodyroot=" ++
          (match bodyroot with
          | BodyRootTopFunc (static,primary_cfunc) -> Pp.str ("TopFunc:" ^ primary_cfunc)
          | BodyRootFixfunc fixfunc_id -> Pp.str ("Fixfunc:" ^ Id.to_string fixfunc_id)
          | BodyRootClosure closure_id -> Pp.str ("Closure:" ^ Id.to_string closure_id)));
      let is_first = (i = 0) in
      let fixfuncs =
        List.filter_map
          (function
            | BodyVarFixfunc fixfunc_id -> Some (Hashtbl.find fixfunc_tbl fixfunc_id)
            | _ -> None)
          bodyvars
      in
      (match fixfuncs with
      | [] -> ()
      | first_fixfunc :: _ ->
          if ((first_fixfunc.fixfunc_cfunc <> None && not is_first) || (* gen_func_multi requires labels to jump for each entry functions except first one *)
              List.exists (fun fixfunc -> fixfunc.fixfunc_used_as_goto) fixfuncs) (* Anyway, labels are required if internal goto use them *)
          then
          let first_fixfunc_id = first_fixfunc.fixfunc_func_id in
          let label = fixfunc_entry_label (Id.to_string first_fixfunc_id) in (* xxx: use shorter name for primary function and siblings *)
          msg_debug_hov (Pp.str "[codegen:fixfunc_initialize_labels]" +++
            Pp.str "i=" ++ Pp.int i +++
            Pp.str "is_first=" ++ Pp.bool is_first +++
            Pp.str "exists_fixfunc_used_as_goto=" ++ Pp.bool (List.exists (fun fixfunc -> fixfunc.fixfunc_used_as_goto) fixfuncs));
          List.iter
            (fun fixfunc ->
              let fixfunc = Hashtbl.find fixfunc_tbl fixfunc.fixfunc_func_id in
              Hashtbl.replace fixfunc_tbl fixfunc.fixfunc_func_id
                { fixfunc with
                  fixfunc_label = Some label })
            fixfuncs);
      (match bodyroot with
      | BodyRootClosure closure_id ->
          let clo = Hashtbl.find closure_tbl closure_id in
          let needs_label =
            not is_first ||
            match fixfuncs with
            | [] -> false
            | first_fixfunc :: _ -> first_fixfunc.fixfunc_cfunc <> None (* "fall through" is not usable in the gen_func_multi switch. *)
          in
          if needs_label then
            Hashtbl.replace closure_tbl closure_id
              { clo with
                closure_label = Some (closure_entry_label clo.closure_c_name) }
      | _ -> ()))
    bodyhead_list

let unique_sibling_entfuncs (sibling_entfuncs : (bool * string * int * Id.t) list) : (bool * string * int * Id.t) list =
  let h = Hashtbl.create 0 in
  let rec aux s =
    match s with
    | [] -> []
    | (static, cfunc, j, fixfunc_id) as entfunc :: rest ->
        match Hashtbl.find_opt h j with
        | Some fixfunc_id1 ->
            aux rest
        | None ->
            (Hashtbl.add h j fixfunc_id;
             entfunc :: aux rest)
  in
  aux sibling_entfuncs

let collect_fix_info ~(higher_order_fixfuncs : bool Id.Map.t) ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t)
    ~(static_and_primary_cfunc : bool * string)
    ~(sibling_entfuncs : (bool * string * int * Id.t) list)
    ~(bodychunks : bodychunk_t list) : fixfunc_table =
  let fixfunc_tbl = collect_fix_usage ~higher_order_fixfuncs ~inlinable_fixterms env sigma term in
  let sibling_entfuncs = unique_sibling_entfuncs sibling_entfuncs in
  fixfunc_initialize_topfunc sigma term ~static_and_primary_cfunc ~fixfunc_tbl;
  fixfunc_initialize_siblings sibling_entfuncs ~fixfunc_tbl;
  fixfunc_initialize_c_names fixfunc_tbl;
  fixfunc_initialize_extra_arguments env sigma term bodychunks ~fixfunc_tbl;
  fixfunc_initialize_c_call sigma bodychunks ~fixfunc_tbl;
  (*show_fixfunc_table env sigma fixfunc_tbl;*)
  fixfunc_tbl

let collect_fix_info_splitted (env : Environ.env) (sigma : Evd.evar_map)
    ~(bodychunks : bodychunk_t list) ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) : unit =
  fixfunc_initialize_labels bodychunks ~fixfunc_tbl ~closure_tbl;
  show_fixfunc_table env sigma fixfunc_tbl;
  ()

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

let lam_fix_body_list (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) :
    ((*fargs of outermost lambdas*)(Names.Name.t Context.binder_annot * EConstr.types) list *
     (*environment under the outermost lambdas*)Environ.env *
     (((*env including fixfunc names but without lambdas of fixfunc*)Environ.env *
       (*env including fixfunc names and lambdas of fixfunc*)Environ.env *
       (*fixfunc name*)Names.Name.t Context.binder_annot *
       (*fixfunc type*)EConstr.types *
       (*fargs*)(Names.Name.t Context.binder_annot * EConstr.types) list) list *
      ((*env for body*)Environ.env *
       (*body*)EConstr.t)) list) =
  let (fargs, body) = EConstr.decompose_lam sigma term in
  let env2 = env_push_assums env fargs in
  (fargs, env2, fix_body_list env2 sigma body)

type head_cont = {
  head_cont_ret_var: string option; (* None for void type context *)
  head_cont_exit_label: string option;
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
  let cargs =
    Array.to_list
      (Array.map
        (fun arg ->
          let arg_ty = Retyping.get_type_of env sigma arg in
          if ind_is_void_type env sigma arg_ty then
            None
          else
            Some (carg_of_garg env (destRel sigma arg)))
        argsary)
  in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:gen_head] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
      user_err (Pp.str "[codegen:gen_head] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_head_cont ~omit_void_exp:true cont (Pp.str str)
      else
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        (match Hashtbl.find_opt fixfunc_tbl (id_of_name name) with
        | None -> (* closure invocation *)
            let closure_var = carg_of_garg env i in
            let pp = gen_funcall ("(*" ^ closure_var ^ ")") (Array.of_list (rcons (list_filter_none cargs) closure_var)) in
            gen_head_cont cont pp
        | Some fixfunc ->
            if fixfunc.fixfunc_fixterm.fixterm_inlinable then
              let assignments =
                list_filter_map2
                  (fun (lhs, c_ty) rhs_opt ->
                    match (c_type_is_void c_ty), rhs_opt with
                    | true, None -> None
                    | false, Some rhs -> Some (lhs, rhs, c_ty)
                    | _, _ -> assert false)
                  fixfunc.fixfunc_formal_arguments
                  cargs
              in
              let pp_assignments = gen_parallel_assignment (Array.of_list assignments) in
              let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str (Option.get fixfunc.fixfunc_label) ++ Pp.str ";") in
              pp_assignments +++ pp_goto_entry
            else
              gen_head_cont cont
                (gen_funcall (cfunc_of_fixfunc fixfunc)
                  (Array.append
                    (Array.of_list (List.map fst fixfunc.fixfunc_extra_arguments))
                    (Array.of_list (list_filter_none cargs)))))

  | Const (ctnt,_) ->
      gen_head_cont cont (gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list (list_filter_none cargs)))
  | Construct (cstr,_) ->
      gen_head_cont ~omit_void_exp:true cont (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list (list_filter_none cargs)))
  | Case (ci,u,pms,p,iv,item,bl) ->
      assert (cargs = []);
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      let gen_switch =
        match cont.head_cont_exit_label with
        | None -> gen_switch_with_break
        | Some _ -> gen_switch_without_break
      in
      gen_match used_vars gen_switch (gen_head ~fixfunc_tbl ~closure_tbl ~used_vars ~cont) env sigma ci item (bl,bl0)
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_proj env sigma pr item (gen_head_cont ~omit_void_exp:true cont))
  | LetIn (x,e,t,b) ->
      assert (cargs = []);
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
      let nj_formal_arguments = fixfunc_j.fixfunc_formal_arguments in
      if not fixfunc_j.fixfunc_fixterm.fixterm_inlinable then
        gen_head_cont cont
          (gen_funcall (cfunc_of_fixfunc fixfunc_j)
            (Array.append
              (Array.of_list (List.map fst fixfunc_j.fixfunc_extra_arguments))
              (Array.of_list (list_filter_none cargs))))
      else
        let assignments =
          list_filter_map2
            (fun (lhs, c_ty) rhs_opt ->
              match (c_type_is_void c_ty), rhs_opt with
              | true, None -> None
              | false, Some rhs -> Some (lhs, rhs, c_ty)
              | _, _ -> assert false)
            nj_formal_arguments
            cargs
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
  let cargs =
    Array.to_list
      (Array.map
        (fun arg ->
          let arg_ty = Retyping.get_type_of env sigma arg in
          if ind_is_void_type env sigma arg_ty then
            None
          else
            Some (carg_of_garg env (destRel sigma arg)))
        argsary)
  in
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:gen_tail] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
      user_err (Pp.str "[codegen:gen_tail] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_tail_cont ~omit_void_exp:true cont (Pp.str str)
      else
        let key = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
        let fixfunc_opt = Hashtbl.find_opt fixfunc_tbl (id_of_name key) in
        (match fixfunc_opt with
        | None -> (* closure invocation *)
            let closure_var = carg_of_garg env i in
            let pp = gen_funcall ("(*" ^ closure_var ^ ")") (Array.of_list (rcons (list_filter_none cargs) closure_var)) in
            gen_tail_cont cont pp
        | Some fixfunc ->
            let formal_arguments = fixfunc.fixfunc_formal_arguments in
            if List.length cargs < List.length formal_arguments then
              user_err (Pp.str "[codegen] gen_tail: partial application for fix-bounded-variable (higher-order term not supported yet):" +++
                Printer.pr_econstr_env env sigma term);
            if not fixfunc.fixfunc_is_higher_order then
              let assignments =
                list_filter_map2
                  (fun (lhs, c_ty) rhs_opt ->
                    match (c_type_is_void c_ty), rhs_opt with
                    | true, None -> None
                    | false, Some rhs -> Some (lhs, rhs, c_ty)
                    | _, _ -> assert false)
                  formal_arguments
                  cargs
              in
              let pp_assignments = gen_parallel_assignment (Array.of_list assignments) in
              let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str (Option.get fixfunc.fixfunc_label) ++ Pp.str ";") in
              pp_assignments +++ pp_goto_entry
            else
              gen_tail_cont cont
                (gen_funcall (cfunc_of_fixfunc fixfunc)
                  (Array.append
                    (Array.of_list (List.map fst fixfunc.fixfunc_extra_arguments))
                    (Array.of_list (list_filter_none cargs)))))
  | Const (ctnt,_) ->
      let pp = gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list (list_filter_none cargs)) in
      gen_tail_cont cont pp
  | Construct (cstr,univ) ->
      gen_tail_cont ~omit_void_exp:true cont (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list (list_filter_none cargs)))
  | Lambda (x,t,b) ->
      user_err (Pp.str "[codegen] gen_tail: lambda term without argument (higher-order term not supported yet):" +++
        Printer.pr_econstr_env env sigma term)
  | Case (ci,u,pms,p,iv,item,bl) ->
      assert (cargs = []);
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      gen_match used_vars gen_switch_without_break (gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont) env sigma ci item (bl,bl0)
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_proj env sigma pr item (gen_tail_cont ~omit_void_exp:true cont))
  | LetIn (x,e,t,b) ->
      assert (cargs = []);
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
      let nj_formal_arguments = fixfunc_j.fixfunc_formal_arguments in
      if List.length cargs < List.length nj_formal_arguments then
        user_err (Pp.str "[codegen] gen_tail: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assignments =
        list_filter_map2
          (fun (lhs, c_ty) rhs_opt ->
            match (c_type_is_void c_ty), rhs_opt with
            | true, None -> None
            | false, Some rhs -> Some (lhs, rhs, c_ty)
            | _, _ -> assert false)
          nj_formal_arguments
          cargs
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
              | None -> Pp.mt () (* Not reached.  Currently, fix-term in top-call are decomposed by obtain_function_bodychunks and gen_tail is not used for it. *)
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

let _ = fun x -> ignore x.bodychunk_fixfunc_calls
let _ = fun x -> ignore x.bodychunk_closure_impls

let labels_of_bodyhead ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) (bodyhead : bodyhead_t) : string list =
  let (bodyroot, bodyvars) = bodyhead in
  let fixfunc_ids =
    List.filter_map
      (function
        | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
        | _ -> None)
      bodyvars
  in
  let fixfunc_label =
    match fixfunc_ids with
    | [] -> []
    | fixfunc_id :: _ ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        (match fixfunc.fixfunc_label with
        | None -> []
        | Some label -> [label])
  in
  let closure_label =
    match bodyroot with
    | BodyRootClosure cloid ->
        let clo = Hashtbl.find closure_tbl cloid in
        (match clo.closure_label with
        | Some label -> [label]
        | None -> [])
    | _ -> []
  in
  closure_label @ fixfunc_label

let obtain_function_bodychunks
    ~(higher_order_fixfuncs : bool Id.Map.t) ~(inlinable_fixterms : bool Id.Map.t)
    ~(static_and_primary_cfunc : bool * string)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    bodychunk_t list =
  let rec aux_lamfix ~(tail_position : bool) ~(individual_body : bool) ~(bodyroot : body_root_t) ~(bodyvars : body_var_t list) (env : Environ.env) (term : EConstr.t) :
      (bodychunk_t Seq.t * (*bodychunk_bodyhead_list*)bodyhead_t list * (*fixfunc_impls*)Id.Set.t * (*fixfunc_gotos*)Id.Set.t * (*fixfunc_calls*)Id.Set.t * (*closurr_defs*)Id.Set.t) =
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:obtain_function_bodychunks:aux_lamfix] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ ->
        user_err (Pp.str "[codegen:obtain_function_bodychunks:aux_lamfix] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Lambda (x,t,b) ->
        let env2 = env_push_assum env x t in
        let bodyvars2 =
          let c_ty = c_typename env sigma t in
          if c_type_is_void c_ty then
            BodyVarVoidArg (str_of_annotated_name x, c_ty) :: bodyvars
          else
            BodyVarArg (str_of_annotated_name x, c_ty) :: bodyvars
        in
        aux_lamfix ~tail_position ~individual_body ~bodyroot ~bodyvars:bodyvars2 env2 b
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
                aux_lamfix ~tail_position ~individual_body ~bodyroot ~bodyvars:bodyvars2 env2 f
              else
                let bodyroot2 = BodyRootFixfunc fixfunc_id in
                let bodyvars2 = [BodyVarFixfunc fixfunc_id] in
                aux_lamfix ~tail_position ~individual_body ~bodyroot:bodyroot2 ~bodyvars:bodyvars2 env2 f)
            nary' fary')
        in
        let bodychunks = concat_array_seq (Array.map (fun (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> bodychunks) result_ary) in
        let bodychunk_bodyhead_list = List.concat (CArray.map_to_list (fun (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> bodychunk_bodyhead_list) result_ary) in
        let fixfunc_impls0 = idset_union_ary (Array.map (fun (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_impls) result_ary) in
        let fixfunc_gotos = idset_union_ary (Array.map (fun (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_gotos) result_ary) in
        let fixfunc_calls = idset_union_ary (Array.map (fun (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_calls) result_ary) in
        let closure_impls = idset_union_ary (Array.map (fun (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> closure_impls) result_ary) in
        let fixfunc_impls = Id.Set.union fixfunc_impls0 (idset_of_array (Array.map id_of_annotated_name nary)) in
        (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
    | _ ->
        let (bodychunks, bodychunk_bodyhead_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = aux_body ~tail_position env term in
        let bodychunk_bodyhead_list2 = (bodyroot, List.rev bodyvars) :: bodychunk_bodyhead_list in
        if individual_body then
          let fixfunc_ids =
            List.filter_map
              (fun bodyvar ->
                match bodyvar with
                | BodyVarFixfunc fixfunc_id -> Some fixfunc_id
                | _ -> None)
              bodyvars
          in
          let fargs = List.filter_map (function BodyVarArg (var, c_ty) -> Some (var, c_ty) | _ -> None) bodyvars in
          let bodychunk = {
            bodychunk_return_type = c_typename env sigma (Reductionops.nf_all env sigma (Retyping.get_type_of env sigma term));
            bodychunk_fargs = List.rev fargs;
            bodychunk_bodyhead_list = bodychunk_bodyhead_list2;
            bodychunk_env = env;
            bodychunk_exp = term;
            bodychunk_fixfunc_impls = Id.Set.union (Id.Set.of_list fixfunc_ids) fixfunc_impls;
            bodychunk_fixfunc_gotos = fixfunc_gotos;
            bodychunk_fixfunc_calls = fixfunc_calls;
            bodychunk_closure_impls = closure_impls;
          } in
          (Seq.cons bodychunk bodychunks, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
        else
          (bodychunks, bodychunk_bodyhead_list2, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
  and aux_body ~(tail_position : bool) (env : Environ.env) (term : EConstr.t) :
      (bodychunk_t Seq.t * (*bodychunk_bodyhead_list*)bodyhead_t list * (*fixfunc_impls*)Id.Set.t * (*fixfunc_gotos*)Id.Set.t * (*fixfunc_calls*)Id.Set.t * (*closurr_defs*)Id.Set.t) =
    let (term, args) = decompose_appvect sigma term in
    match EConstr.kind sigma term with
    | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
        user_err (Pp.str "[codegen:obtain_function_bodychunks:aux_body] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Cast _ | Sort _ | Prod _ | Ind _ | App _ ->
        user_err (Pp.str "[codegen:obtain_function_bodychunks:aux_body] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
    | Rel i ->
        if CArray.is_empty args then
          (Seq.empty, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
        else (* application *)
          let id = id_of_name (Context.Rel.Declaration.get_name (Environ.lookup_rel i env)) in
          let (fixfunc_gotos, fixfunc_calls) =
            match Id.Map.find_opt id higher_order_fixfuncs with
            | None -> (Id.Set.empty, Id.Set.empty) (* closure call *)
            | Some fixfunc_is_higher_order ->
                let fixterm_is_inlinable = Id.Map.find id inlinable_fixterms in
                determine_fixfunc_call_or_goto tail_position fixfunc_is_higher_order fixterm_is_inlinable
                  ~call:(fun () -> (Id.Set.empty, Id.Set.singleton id))
                  ~goto:(fun () -> (Id.Set.singleton id, Id.Set.empty))
          in
          (Seq.empty, [], Id.Set.empty, fixfunc_gotos, fixfunc_calls, Id.Set.empty)
    | Const _ | Construct _ -> (Seq.empty, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
    | Proj (proj, e) -> (Seq.empty, [], Id.Set.empty, Id.Set.empty, Id.Set.empty, Id.Set.empty)
    | LetIn (x,e,t,b) ->
        let env2 = env_push_def env x e t in
        let (bodychunks1, body_entries1, fixfunc_impls1, fixfunc_gotos1, fixfunc_calls1, closure_impls1) = aux_body ~tail_position:false env e in
        let (bodychunks2, body_entries2, fixfunc_impls2, fixfunc_gotos2, fixfunc_calls2, closure_impls2) = aux_body ~tail_position env2 b in
        (Seq.append bodychunks1 bodychunks2,
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
              aux_body ~tail_position env2 body)
            bl bl0)
        in
        let bodychunks = concat_array_seq (Array.map (fun (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> bodychunks) result_ary) in
        let bodychunk_body_list = List.concat (CArray.map_to_list (fun (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> bodychunk_body_list) result_ary) in
        let fixfunc_impls = idset_union_ary (Array.map (fun (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_impls) result_ary) in
        let fixfunc_gotos = idset_union_ary (Array.map (fun (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_gotos) result_ary) in
        let fixfunc_calls = idset_union_ary (Array.map (fun (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> fixfunc_calls) result_ary) in
        let closure_impls = idset_union_ary (Array.map (fun (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) -> closure_impls) result_ary) in
        (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
    | Lambda (x,t,b) ->
        if CArray.is_empty args then (* closure creation *)
          let cloid = get_closure_id env sigma term in
          let (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = aux_lamfix ~tail_position:true ~individual_body:true ~bodyroot:(BodyRootClosure cloid) ~bodyvars:[] env term in
          let closure_impls2 = Id.Set.add cloid closure_impls in
          (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls2)
        else
          assert false
    | Fix ((ks, j), ((nary, tary, fary))) ->
        if CArray.is_empty args then (* closure creation *)
          (let cloid = get_closure_id env sigma term in
          assert (not tail_position);
          let (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = aux_lamfix ~tail_position:true ~individual_body:true ~bodyroot:(BodyRootClosure cloid) ~bodyvars:[] env term in
          let closure_impls2 = Id.Set.add cloid closure_impls in
          (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls2))
        else
          let fixterm_id = id_of_annotated_name nary.(j) in
          let inlinable = Id.Map.find fixterm_id inlinable_fixterms in
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
          let (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = aux_lamfix ~tail_position:tail_position2 ~individual_body ~bodyroot:(BodyRootFixfunc fixterm_id) ~bodyvars:[] env term in
          if individual_body then
            (bodychunks, bodychunk_body_list, Id.Set.empty, Id.Set.empty, Id.Set.singleton fixterm_id, Id.Set.empty)
          else
            (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls)
  in
  let (bodychunks, bodychunk_body_list, fixfunc_impls, fixfunc_gotos, fixfunc_calls, closure_impls) = aux_lamfix ~tail_position:true ~individual_body:true ~bodyroot:(BodyRootTopFunc static_and_primary_cfunc) ~bodyvars:[] env term in
  let result = List.of_seq bodychunks in
  (*show_bodychunks sigma result;*)
  result

let split_function_bodychunks (bodychunks : bodychunk_t list) : bodychunk_t list list =
  let bodychunks = Array.of_list bodychunks in
  let n = Array.length bodychunks in
  (*msg_debug_hov (Pp.str "[codegen:split_function_bodychunks] num_bodychunks=" ++ Pp.int n);*)
  let id_int_map =
    CArray.fold_left_i
      (fun i id_int_map bodychunk ->
        Id.Set.fold
          (fun fixfunc_def_id id_int_map ->
            (*msg_debug_hov (Pp.str "[codegen:split_function_bodychunks]" +++
              Pp.str "i=" ++ Pp.int i +++
              Pp.str "body_fixfunc_impl=" ++ Id.print fixfunc_def_id);*)
            Id.Map.add fixfunc_def_id i id_int_map)
          bodychunk.bodychunk_fixfunc_impls id_int_map)
      Id.Map.empty bodychunks
  in
  let u = unionfind_make n in
  Array.iteri
    (fun i bodychunk ->
      Id.Set.iter
        (fun fixfunc_id -> unionfind_union u i (Id.Map.find fixfunc_id id_int_map))
        bodychunk.bodychunk_fixfunc_gotos)
    bodychunks;
  List.map
    (List.map (fun i -> bodychunks.(i)))
    (unionfind_sets u)

let rec find_closures ~(found : Environ.env -> EConstr.t -> unit)
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
  | _ -> find_closures_exp ~found env sigma term
and find_closures_exp ~(found : Environ.env -> EConstr.t -> unit)
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ ->
      user_err (Pp.str "[codegen:find_closures_exp] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ | Sort _ | Prod _ | Ind _ ->
      user_err (Pp.str "[codegen:find_closures_exp] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | LetIn (x,e,t,b) ->
      let env2 = env_push_def env x e t in
      find_closures_exp ~found env sigma e;
      find_closures_exp ~found env2 sigma b
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      (Array.iter2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          find_closures_exp ~found env2 sigma body)
        bl bl0)
  | Rel _ -> ()
  | Const _ -> ()
  | Construct _ -> ()
  | Proj _ -> ()
  | App (f,args) -> (* The function position can be a fixpoint.  The fixpoint itself is not a closure generation but its bodychunks may have closure generations. *)
      find_closures ~found env sigma f
  | Lambda _ -> (* closure generation found *)
      found env term;
      find_closures ~found env sigma term
  | Fix _ -> (* closure generation found *)
      found env term;
      find_closures ~found env sigma term

let c_fargs_of (env : Environ.env) (sigma : Evd.evar_map) (fargs : (Names.Name.t Context.binder_annot * EConstr.types) list) =
  let (_, c_fargs) =
    List.fold_left_map
      (fun env (annotated_name, ty) ->
        let env' = Environ.pop_rel_context 1 env in
        (env, (str_of_annotated_name annotated_name, c_typename env' sigma ty)))
      env fargs
  in
  c_fargs

let collect_closures ~(fixfunc_tbl : fixfunc_table)
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : closure_t list =
  let closures = ref [] in
  find_closures env sigma term
    ~found:(fun closure_env closure_exp ->
      (*msg_debug_hov (Pp.str "[codegen:collect_closures] closure_exp=" ++ Printer.pr_econstr_env closure_env sigma closure_exp);*)
      let closure_ty = Reductionops.nf_all closure_env sigma (Retyping.get_type_of closure_env sigma closure_exp) in
      (*msg_debug_hov (Pp.str "[codegen:collect_closures] closure_ty=" ++ Printer.pr_econstr_env closure_env sigma closure_ty);*)
      let c_closure_function_ty = c_closure_function_type closure_env sigma closure_ty in
      let c_return_ty = c_typename closure_env sigma (snd (decompose_prod sigma closure_ty)) in
      let cloid = get_closure_id closure_env sigma closure_exp in
      let cloname = global_gensym () in
      let (outermost_fargs, env1, fix_bodies) = lam_fix_body_list closure_env sigma closure_exp in
      let outermost_fargs = c_fargs_of env1 sigma outermost_fargs in
      let (fixes, (env4, body)) = List.hd fix_bodies in
      let fix_fargs_list = List.map
        (fun (env2, env3, fixfunc_name, fixfunc_type, fix_fargs) ->
          c_fargs_of env3 sigma fix_fargs)
        fixes
      in
      let c_fargs = List.concat (List.rev outermost_fargs :: List.map List.rev fix_fargs_list) in
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
          match Hashtbl.find_opt fixfunc_tbl id with
          | None ->
              [(Id.to_string id, c_ty)]
          | Some fixfunc -> fixfunc.fixfunc_extra_arguments)
        (IntSet.elements fv_index_set)
      in
      let vars = List.sort_uniq (fun (str1,c_ty1) (str2,c_ty2) -> String.compare str1 str2) vars in
      closures := {
          closure_id=cloid;
          closure_c_name=cloname;
          closure_c_func_type=c_closure_function_ty;
          closure_c_return_type=c_return_ty;
          closure_label = None; (* dummy. updated by fixfunc_initialize_labels *)
          closure_args=c_fargs;
          closure_vars=vars;
        } :: !closures);
  List.rev !closures

let closure_tbl_of_list (closure_list : closure_t list) : closure_table =
  let closure_tbl = Hashtbl.create 0 in
  List.iter
    (fun clo -> Hashtbl.add closure_tbl clo.closure_id clo)
    closure_list;
  closure_tbl

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

let gen_func_single
    ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table)
    ~(bodyent : body_entry_t)
    ~(bodychunks : bodychunk_t list)
    (sigma : Evd.evar_map)
    (used_vars : Id.Set.t) : Pp.t * Pp.t =
  let (static, primary_cfunc) =
    match bodyent with
    | BodyEntryTopFunc (static, primary_cfunc) -> (static, primary_cfunc)
    | BodyEntryFixfunc fixfunc_id ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        (Option.get fixfunc.fixfunc_cfunc)
    | BodyEntryClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        (true, closure_func_name clo)
  in
  let pp_struct_closure =
    match bodyent with
    | BodyEntryClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        gen_closure_struct clo
    | _ -> Pp.mt ()
  in
  let pp_closure_assigns =
    match bodyent with
    | BodyEntryClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        let casted_var = "((struct " ^ closure_struct_tag clo ^ " *)closure)" in
        pp_sjoinmap_list
          (fun (lhs, rhs) -> gen_assignment (Pp.str lhs) (Pp.str rhs))
          (gen_closure_load_vars_assignments clo casted_var)
    | _ -> Pp.mt ()
  in
  let closure_vars =
    match bodyent with
    | BodyEntryClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        clo.closure_vars
    | _ -> []
  in
  let c_fargs =
    match bodyent with
    | BodyEntryTopFunc _ -> (List.hd bodychunks).bodychunk_fargs
    | BodyEntryFixfunc fixfunc_id ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        fixfunc.fixfunc_extra_arguments @ fixfunc.fixfunc_formal_arguments
    | BodyEntryClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        let pointer_to_void = { c_type_left="void *"; c_type_right="" } in
        clo.closure_args @ [("closure", pointer_to_void)]
  in
  let return_type = (List.hd bodychunks).bodychunk_return_type in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun bodychunk ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            bodychunk.bodychunk_fargs;
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            closure_vars;
          let cont = { tail_cont_return_type = return_type; tail_cont_multifunc = false } in
          let labels = labels_of_bodyhead ~fixfunc_tbl ~closure_tbl (List.hd bodychunk.bodychunk_bodyhead_list) in
          pp_closure_assigns +++
          pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
          gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont bodychunk.bodychunk_env sigma bodychunk.bodychunk_exp)
        bodychunks)
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

let gen_func_multi
    ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table)
    ~(entry_funcs : body_entry_t list)
    ~(bodychunks : bodychunk_t list)
    (env : Environ.env) (sigma : Evd.evar_map)
    (used_vars : Id.Set.t) : Pp.t * Pp.t =
  let first_c_name =
    match List.hd entry_funcs with
    | BodyEntryTopFunc (_, primary_cfunc) -> primary_cfunc
    | BodyEntryFixfunc fixfunc_id ->
        let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
        (cfunc_of_fixfunc fixfunc)
    | BodyEntryClosure closure_id ->
        let clo = Hashtbl.find closure_tbl closure_id in
        closure_func_name clo
  in
  let func_index_enum_tag = func_index_enum_tag_name first_c_name in
  let body_function_name = body_function_name first_c_name in
  let pointer_to_void = { c_type_left="void *"; c_type_right="" } in
  let formal_arguments = (List.hd bodychunks).bodychunk_fargs in
  let return_type = (List.hd bodychunks).bodychunk_return_type in
  let pp_enum =
    Pp.hov 0 (
      Pp.str "enum" +++
      Pp.str func_index_enum_tag +++
      hovbrace (
        pp_joinmap_list (Pp.str "," ++ Pp.spc ()) Pp.str
          (List.map
            (function
              | BodyEntryTopFunc (_,primary_cfunc) -> topfunc_enum_index primary_cfunc
              | BodyEntryFixfunc fixfunc_id ->
                  let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
                  fixfunc_enum_index fixfunc.fixfunc_c_name
              | BodyEntryClosure closure_id ->
                  let clo = Hashtbl.find closure_tbl closure_id in
                  closure_enum_index clo.closure_c_name)
            entry_funcs)
          ) ++
      Pp.str ";")
  in
  let pp_struct_closures =
    pp_sjoinmap_list
      (function
        | BodyEntryClosure closure_id ->
            let clo = Hashtbl.find closure_tbl closure_id in
            gen_closure_struct clo
        | _ -> Pp.mt ())
      entry_funcs
  in
  let pp_struct_args =
    pp_sjoin_list
      (List.filter_map
        (function
          | BodyEntryTopFunc (_, primary_cfunc) ->
              if CList.is_empty formal_arguments then
                None
              else
                Some (
                  Pp.hv 0 (
                    Pp.str (topfunc_args_struct_type primary_cfunc) +++
                    hovbrace (pr_members formal_arguments) ++ Pp.str ";"))
          | BodyEntryFixfunc fixfunc_id ->
              let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
              if CList.is_empty fixfunc.fixfunc_extra_arguments &&
                 CList.is_empty fixfunc.fixfunc_formal_arguments then
                None
              else
                Some (
                  Pp.hv 0 (
                  Pp.str (fixfunc_args_struct_type fixfunc.fixfunc_c_name) +++
                  hovbrace (
                  pr_members fixfunc.fixfunc_extra_arguments +++
                  pr_members (List.filter_map
                               (fun (c_arg, c_ty) ->
                                 if c_type_is_void c_ty then None
                                 else Some (c_arg, c_ty))
                               fixfunc.fixfunc_formal_arguments)) ++ Pp.str ";"))
          | BodyEntryClosure closure_id ->
              let clo = Hashtbl.find closure_tbl closure_id in
              Some (
                Pp.hv 0 (
                Pp.str (closure_args_struct_type clo.closure_c_name) +++
                hovbrace (
                  pr_members clo.closure_args +++
                  pr_members [("closure", c_type_pointer_to (closure_struct_type clo))]
                ) ++ Pp.str ";")))
        entry_funcs)
  in
  let pp_forward_decl =
    Pp.hv 0 (
      Pp.str "static void" +++
      Pp.str body_function_name ++
      Pp.str ("(enum " ^ func_index_enum_tag ^ " codegen_func_index, void *codegen_args, void *codegen_ret);"))
  in
  let pp_entry_functions =
    pp_sjoin_list
      (List.map
        (function
          | BodyEntryTopFunc (static, primary_cfunc) ->
              pr_entry_function ~static primary_cfunc (topfunc_enum_index primary_cfunc)
                (topfunc_args_struct_type primary_cfunc)
                formal_arguments return_type
                body_function_name
          | BodyEntryFixfunc fixfunc_id ->
              let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
              let (static, cfunc) = Option.get fixfunc.fixfunc_cfunc in
              pr_entry_function ~static cfunc (fixfunc_enum_index fixfunc.fixfunc_c_name)
                (fixfunc_args_struct_type fixfunc.fixfunc_c_name)
                (List.append
                  fixfunc.fixfunc_extra_arguments
                  (List.filter_map
                    (fun (c_arg, c_ty) ->
                      if c_type_is_void c_ty then None
                      else Some (c_arg, c_ty))
                    fixfunc.fixfunc_formal_arguments))
                fixfunc.fixfunc_return_type
                body_function_name
          | BodyEntryClosure closure_id ->
              let clo = Hashtbl.find closure_tbl closure_id in
              pr_entry_function ~static:true (closure_func_name clo) (closure_enum_index clo.closure_c_name)
                (closure_args_struct_type clo.closure_c_name)
                (List.append clo.closure_args [("closure", pointer_to_void)])
                clo.closure_c_return_type
                body_function_name)
        entry_funcs)
  in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun bodychunk ->
          List.iter
            (fun (arg_name, arg_type) ->
              (*msg_debug_hov (Pp.str ("[codegen:gen_func_multi] add_local_var " ^ arg_name));*)
              add_local_var arg_type arg_name)
            bodychunk.bodychunk_fargs;
          let bodyhead = List.hd bodychunk.bodychunk_bodyhead_list in
          let (bodyroot, bodyvars) = bodyhead in
          List.iter
            (function
              | BodyVarFixfunc fixfunc_id ->
                  let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
                  List.iter
                    (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
                    fixfunc.fixfunc_extra_arguments
              | _ -> ())
            bodyvars;
          let cont = { tail_cont_return_type = bodychunk.bodychunk_return_type; tail_cont_multifunc = true } in
          let labels = labels_of_bodyhead ~fixfunc_tbl ~closure_tbl bodyhead in
          Pp.v 0 (
            pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
            gen_tail ~fixfunc_tbl ~closure_tbl ~used_vars ~cont bodychunk.bodychunk_env sigma bodychunk.bodychunk_exp))
        bodychunks)
  in
  let pp_local_variables_decls =
    pp_sjoinmap_list
      (fun (c_ty, c_var) -> Pp.hov 0 (pr_c_decl c_ty (Pp.str c_var) ++ Pp.str ";"))
      local_vars
  in
  let pr_case case_value assigns goto_label =
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
  in
  let pp_switch_cases =
    let num_entry_funcs = List.length entry_funcs in
    let entry_funcs' =
      match entry_funcs with
      | [] -> []
      | hd :: tl -> rcons tl hd
    in
    pp_sjoin_list
      (List.mapi
        (fun i entry_func ->
          let is_last = (i = num_entry_funcs - 1) in
          match entry_func with
          | BodyEntryTopFunc (static, primary_cfunc) ->
              assert is_last;
              pr_case None
                (List.map
                  (fun (c_arg, t) ->
                      (c_arg,
                       ("((" ^ topfunc_args_struct_type primary_cfunc ^ " *)codegen_args)->" ^ c_arg)))
                  formal_arguments)
                None (* no need to goto label because BodyEntryTopFunc is always at last *)
          | BodyEntryFixfunc fixfunc_id ->
              let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
              let case_value = if is_last then None else Some (fixfunc_enum_index fixfunc.fixfunc_c_name) in
              let goto = if is_last then None else Some (Option.get fixfunc.fixfunc_label) in
              pr_case case_value
                (List.append
                  (List.map
                    (fun (c_arg, t) ->
                      (c_arg,
                       ("((" ^ fixfunc_args_struct_type fixfunc.fixfunc_c_name ^ " *)codegen_args)->" ^ c_arg)))
                    fixfunc.fixfunc_extra_arguments)
                  (List.filter_map
                    (fun (c_arg, c_ty) ->
                      if c_type_is_void c_ty then None
                      else Some (c_arg,
                                 ("((" ^ fixfunc_args_struct_type fixfunc.fixfunc_c_name ^ " *)codegen_args)->" ^ c_arg)))
                    fixfunc.fixfunc_formal_arguments))
                goto
          | BodyEntryClosure closure_id ->
              let clo = Hashtbl.find closure_tbl closure_id in
              pr_case (Some (closure_enum_index clo.closure_c_name))
                (gen_closure_load_args_assignments clo "codegen_args")
                (Some (closure_entry_label clo.closure_c_name)))
        entry_funcs')
  in
  let pp_switch =
    Pp.hov 0 (Pp.str "switch" +++ Pp.str "(codegen_func_index)") +++
    vbrace pp_switch_cases
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
     pp_struct_closures +++
     pp_struct_args +++
     pp_forward_decl +++
     pp_entry_functions),
   Pp.v 0 (pp_body_function))

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

let gen_stub_sibling_functions ~(fixfunc_tbl : fixfunc_table) (stub_sibling_entries : (bool * string * string * Id.t) list) : Pp.t =
  pp_sjoinmap_list
    (fun (static, cfunc_name_to_define, cfunc_name_to_call, fixfunc_id) ->
      let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
      let args = List.append fixfunc.fixfunc_extra_arguments fixfunc.fixfunc_formal_arguments in
      let return_type = fixfunc.fixfunc_return_type in
      Pp.v 0 (
        gen_function_header ~static return_type cfunc_name_to_define args +++
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
              args ++
            Pp.str ");"))))
    stub_sibling_entries

let entfuncs_of_bodyhead ~(fixfunc_tbl : fixfunc_table) ~(closure_tbl : closure_table) (bodyhead : bodyhead_t) : body_entry_t list =
  let (bodyroot, bodyvars) = bodyhead in
  let normal_ent =
    match bodyroot with
    | BodyRootTopFunc (primary_static, primary_cfunc) ->
        Some (BodyEntryTopFunc (primary_static, primary_cfunc))
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
            let first_fixfunc = Hashtbl.find fixfunc_tbl first_fixfunc_id in
            match first_fixfunc.fixfunc_sibling with
            | Some _ ->
                Some (BodyEntryFixfunc first_fixfunc_id)
            | None ->
                List.find_map
                  (fun fixfunc_id ->
                    let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
                    if fixfunc.fixfunc_used_as_call then
                      Some (BodyEntryFixfunc fixfunc_id)
                    else
                      None)
                  fixfunc_ids)
  in
  let closure_ent =
    match bodyroot with
    | BodyRootClosure cloid -> Some (BodyEntryClosure (Hashtbl.find closure_tbl cloid).closure_id)
    | _ -> None
  in
  (match normal_ent with Some nent -> [nent] | None -> []) @
  (match closure_ent with Some cent -> [cent] | None -> [])

let gen_func_sub (primary_cfunc : string) (sibling_entfuncs : (bool * string * int * Id.t) list) (stubs : (bool * string * string * Id.t) list) : Pp.t =
  let (static, ty, whole_term) = make_simplified_for_cfunc primary_cfunc in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_term = EConstr.of_constr whole_term in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:1");*)
  let higher_order_fixfuncs = detect_higher_order_fixfunc env sigma whole_term in
  let inlinable_fixterms = detect_inlinable_fixterm ~higher_order_fixfuncs env sigma whole_term in
  let bodychunks = obtain_function_bodychunks ~higher_order_fixfuncs ~inlinable_fixterms ~static_and_primary_cfunc:(static, primary_cfunc) env sigma whole_term in
  let fixfunc_tbl = collect_fix_info ~higher_order_fixfuncs ~inlinable_fixterms ~static_and_primary_cfunc:(static, primary_cfunc) ~sibling_entfuncs ~bodychunks env sigma whole_term in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:2");*)
  let used_vars = used_variables env sigma whole_term in
  let closure_list = collect_closures ~fixfunc_tbl env sigma whole_term in
  let closure_tbl = closure_tbl_of_list closure_list in
  let bodychunks_list = split_function_bodychunks bodychunks in
  List.iter (fun bodychunks -> show_bodychunks sigma bodychunks) bodychunks_list;
  let code_pairs = List.map
    (fun bodychunks ->
      collect_fix_info_splitted env sigma ~bodychunks ~fixfunc_tbl ~closure_tbl;
      let bodyhead_list = List.concat_map (fun bodychunk -> bodychunk.bodychunk_bodyhead_list) bodychunks in
      let entry_funcs = List.concat_map (entfuncs_of_bodyhead ~fixfunc_tbl ~closure_tbl) bodyhead_list in
      let (decl, impl) =
        match entry_funcs with
        | [] -> (Pp.mt (), Pp.mt ())
        | [bodyent] ->
            gen_func_single ~fixfunc_tbl ~closure_tbl ~bodyent ~bodychunks sigma used_vars
        | _ ->
            gen_func_multi ~fixfunc_tbl ~closure_tbl ~entry_funcs ~bodychunks env sigma used_vars
      in
      let pp_stub_sibling_entfuncs = gen_stub_sibling_functions ~fixfunc_tbl stubs in
      (decl +++ pp_stub_sibling_entfuncs, impl))
    bodychunks_list
  in
  List.fold_left (fun c (decl, impl) -> c +++ decl ++ Pp.fnl ()) (Pp.mt ()) code_pairs +++
  List.fold_left (fun c (decl, impl) -> c +++ impl ++ Pp.fnl ()) (Pp.mt ()) code_pairs

let gen_function ?(sibling_entfuncs : (bool * string * int * Id.t) list = []) ?(stubs : (bool * string * string * Id.t) list = []) (primary_cfunc : string) : Pp.t =
  local_gensym_with (fun () -> gen_func_sub primary_cfunc sibling_entfuncs stubs)

let detect_stubs (cfuncs : string list) static_ty_term_list =
  let primary_nary =
    let (primary_static, primary_ty, primary_term) = List.hd static_ty_term_list in
    let (args, body) = Term.decompose_lam primary_term in
    let ((ks, j), (nary, tary, fary)) = Constr.destFix body in
    nary
  in
  let h = Hashtbl.create 0 in
  let result_impls = ref [] in
  List.iter2
    (fun cfunc (static, ty, term) ->
      let (args, body) = Term.decompose_lam term in
      let ((ks, j), (nary, tary, fary)) = Constr.destFix body in
      match Hashtbl.find_opt h j with
      | None ->
          let fixfunc_id = id_of_annotated_name primary_nary.(j) in
          let entfunc = (static, cfunc, j, fixfunc_id) in
          result_impls := entfunc :: !result_impls;
          Hashtbl.add h j (cfunc, fixfunc_id, [])
      | Some (orig_cfunc, orig_fixfunc_id, stubs) ->
          let stub = (static, cfunc, orig_cfunc, orig_fixfunc_id) in
          Hashtbl.replace h j (orig_cfunc, orig_fixfunc_id, stub :: stubs))
    cfuncs static_ty_term_list;
  let result_stubs =
    List.concat_map
      (fun (j, (orig_cfunc, orig_fixfunc_id, stubs)) -> stubs)
      (List.of_seq (Hashtbl.to_seq h))
  in
  (List.rev !result_impls, result_stubs)

let gen_mutual (cfunc_names : string list) : Pp.t =
  match cfunc_names with
  | [] -> user_err (Pp.str "[codegen:bug] gen_mutual with empty cfunc_names")
  | [_] -> user_err (Pp.str "[codegen:bug] gen_mutual with single cfunc_name")
  | cfuncs ->
      let static_ty_term_list = List.map make_simplified_for_cfunc cfuncs in
      let (primary_and_sibling_entfuncs, stubs) = detect_stubs cfuncs static_ty_term_list in
      let primary_entfunc = List.hd primary_and_sibling_entfuncs in
      let sibling_entfuncs = List.tl primary_and_sibling_entfuncs in
      let (_, primary_cfunc, _, _) = primary_entfunc in
      gen_function ~sibling_entfuncs ~stubs primary_cfunc

let gen_prototype (cfunc_name : string) : Pp.t =
  let (static, ty, whole_term) = make_simplified_for_cfunc cfunc_name in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments, return_type) = c_args_and_ret_type env sigma whole_ty in
  let formal_arguments' =
    List.filter_map
      (fun (c_arg, c_ty) ->
        if c_type_is_void c_ty then None
        else Some (c_arg, c_ty))
      formal_arguments
  in
  gen_function_header ~static return_type cfunc_name formal_arguments' ++ Pp.str ";"

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
          f (Pp.v 0 (gen_function cfunc_name ++ Pp.fnl ()))
      | GenMutual cfunc_names ->
          f (Pp.v 0 (gen_mutual cfunc_names ++ Pp.fnl ()))
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
