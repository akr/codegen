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
  fixterm_term: EConstr.t;
  fixterm_inlinable: bool;
}

type fixfunc_t = {
  fixfunc_func_id: Id.t;
  fixfunc_term_id: Id.t;
  fixfunc_term_env: Environ.env;
  fixfunc_inlinable: bool;
  fixfunc_used_as_call: bool;
  fixfunc_used_as_goto: bool;
  fixfunc_formal_arguments: (string * c_typedata) list; (* [(varname1, vartype1); ...] *) (* vartype may be void *)
  fixfunc_return_type: c_typedata; (* may be void. *)

  fixfunc_top_call: string option; (* by fixfunc_initialize_top_calls *)
  fixfunc_c_name: string; (* by fixfunc_initialize_c_names *)

  fixfunc_outer_variables: (string * c_typedata) list; (* [(varname1, vartype1); ...] *) (* by fixfunc_initialize_outer_variables *)
  (* outer variables are mostly same for fix-bouded functions in a fix-term.
    However, they can be different when some of them have Some X for fixfunc_top_call.
    In such case, outer variables are all bounded variables by lambda and let-in and not filtered. *)
}

type fixfunc_table = (Id.t, fixfunc_t) Hashtbl.t

let show_fixfunc_table (env : Environ.env) (sigma : Evd.evar_map) (fixfunc_tbl : fixfunc_table) : unit =
  Hashtbl.iter
    (fun fixfunc_id fixfunc ->
      msg_debug_hov (Pp.str (Id.to_string fixfunc_id) ++ Pp.str ":" +++
        Pp.str "inlinable=" ++ Pp.bool fixfunc.fixfunc_inlinable +++
        Pp.str "used_as_call=" ++ Pp.bool fixfunc.fixfunc_used_as_call +++
        Pp.str "used_as_goto=" ++ Pp.bool fixfunc.fixfunc_used_as_goto +++
        Pp.str "formal_arguments=(" ++
          pp_joinmap_list (Pp.str ",")
            (fun (farg, c_ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str (compose_c_abstract_decl c_ty))
            fixfunc.fixfunc_formal_arguments ++ Pp.str ")" +++
        Pp.str "return_type=" ++ Pp.str (compose_c_abstract_decl fixfunc.fixfunc_return_type) +++
        Pp.str "top_call=" ++ (match fixfunc.fixfunc_top_call with None -> Pp.str "None" | Some top -> Pp.str ("Some " ^ top)) +++
        Pp.str "c_name=" ++ Pp.str fixfunc.fixfunc_c_name +++
        Pp.str "outer_variables=(" ++ pp_joinmap_list (Pp.str ",") (fun (farg, c_ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str (compose_c_abstract_decl c_ty)) fixfunc.fixfunc_outer_variables ++ Pp.str ")" +++
        Pp.mt ()
      ))
    fixfunc_tbl

let _ = ignore show_fixfunc_table

let rec c_args_and_ret_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((string * c_typedata) list) * c_typedata =
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

let disjoint_id_map_union_ary (ms : 'a Id.Map.t array) : 'a Id.Map.t =
  Array.fold_left
    (fun m0 m1 ->
      disjoint_id_map_union m0 m1)
    Id.Map.empty ms

(*
  detect_inlinable_fixterm_rec implements (R,N,T) = RNT[term] in doc/codegen.tex.
  R is a map from fix-bounded IDs to bool.
  R[n] = true if n is fix-bounded function which is inlinable (only used for goto so do not need to be a real function).
  R[n] = false if n is fix-bounded function not inlinable.
  R can also be usable to determine an ID is fix-bounded function or not.
*)
let rec detect_inlinable_fixterm_rec (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) :
    (* fixterms inlinable or not *) bool Id.Map.t *
    (* variables at non-tail position *) IntSet.t *
    (* variables at tail position *) IntSet.t =
  (*msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_rec] start:" +++
    Printer.pr_econstr_env env sigma term);*)
  let result = detect_inlinable_fixterm_rec1 env sigma term in
  (*let (argmap, nontailset, tailset, argset) = result in
  msg_debug_hov (Pp.str "[codegen:detect_inlinable_fixterm_rec] end:" +++
    Printer.pr_econstr_env env sigma term +++
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
and detect_inlinable_fixterm_rec1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) :
    (* fixterms inlinable or not *) bool Id.Map.t *
    (* variables at non-tail position *) IntSet.t *
    (* variables at tail position *) IntSet.t =
  let (term, args) = decompose_appvect sigma term in
  let numargs = Array.length args in
  (if 0 < numargs then
    match EConstr.kind sigma term with
    | Rel _ | Const _ | Construct _ | Fix _ -> ()
    | _ -> user_err (Pp.str "[codegen] unexpected term in function position:" +++ Printer.pr_econstr_env env sigma term));
  let args_set = Array.fold_left (fun set arg -> IntSet.add (destRel sigma arg) set) IntSet.empty args in
  match EConstr.kind sigma term with
  | App _ -> user_err (Pp.str "[codegen] App unexpected here")
  | Cast _ -> user_err (Pp.str "[codegen] Cast is not supported for code generation")
  | Var _ -> user_err (Pp.str "[codegen] Var is not supported for code generation")
  | Meta _ -> user_err (Pp.str "[codegen] Meta is not supported for code generation")
  | Sort _ -> user_err (Pp.str "[codegen] Sort is not supported for code generation")
  | Ind _ -> user_err (Pp.str "[codegen] Ind is not supported for code generation")
  | Prod _ -> user_err (Pp.str "[codegen] Prod is not supported for code generation")
  | Evar _ -> user_err (Pp.str "[codegen] Evar is not supported for code generation")
  | CoFix _ -> user_err (Pp.str "[codegen] CoFix is not supported for code generation")
  | Array _ -> user_err (Pp.str "[codegen] Array is not supported for code generation")
  | Int _ | Float _ -> (Id.Map.empty, IntSet.empty, IntSet.empty)
  | Rel i -> (Id.Map.empty, args_set, IntSet.singleton i)
  | Const _ | Construct _ -> (Id.Map.empty, args_set, IntSet.empty)
  | Proj (proj, e) ->
      (* e must be a Rel which type is inductive (non-function) type *)
      (Id.Map.empty, IntSet.empty, IntSet.empty)
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let (inlinable_e, nontailset_e, tailset_e) = detect_inlinable_fixterm_rec env sigma e in
      let (inlinable_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_rec env2 sigma b in
      let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
      let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
      let nontailset = intset_union3 tailset_e nontailset_e nontailset_b in
      let inlinable = disjoint_id_map_union inlinable_e inlinable_b in
      (inlinable, nontailset, tailset_b)
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      (* item cannot contain fix-term because item must be a Rel which type is inductive (non-function) type *)
      let branches_result = Array.map2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          let n = Array.length nas in
          let (inlinable_br, nontailset_br, tailset_br) = detect_inlinable_fixterm_rec env2 sigma body in
          let tailset_br = IntSet.map (fun i -> i - n) (IntSet.filter ((<) n) tailset_br) in
          let nontailset_br = IntSet.map (fun i -> i - n) (IntSet.filter ((<) n) nontailset_br) in
          (inlinable_br, nontailset_br, tailset_br))
        bl bl0
      in
      let tailset = intset_union_ary (Array.map (fun (inlinable_br, nontailset_br, tailset_br) -> tailset_br) branches_result) in
      let nontailset = intset_union_ary (Array.map (fun (inlinable_br, nontailset_br, tailset_br) -> nontailset_br) branches_result) in
      let inlinable = disjoint_id_map_union_ary (Array.map (fun (inlinable_br, nontailset_br, tailset_br) -> inlinable_br) branches_result) in
      (inlinable, nontailset, tailset)
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      if numargs = 0 then
        (* closure creation *)
        let (inlinable_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_rec env2 sigma b in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        let nontailset = IntSet.union tailset_b nontailset_b in
        (inlinable_b, nontailset, IntSet.empty)
      else
        let (inlinable_b, nontailset_b, tailset_b) = detect_inlinable_fixterm_rec env2 sigma b in
        let tailset_b = IntSet.map pred (IntSet.filter ((<) 1) tailset_b) in
        let nontailset_b = IntSet.map pred (IntSet.filter ((<) 1) nontailset_b) in
        (inlinable_b, nontailset_b, tailset_b)
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let h = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let fixfuncs_result = Array.map (detect_inlinable_fixterm_rec env2 sigma) fary in
      let tailset_fs = intset_union_ary (Array.map (fun (inlinable_f, nontailset_f, tailset_f) -> tailset_f) fixfuncs_result) in
      let nontailset_fs = intset_union_ary (Array.map (fun (inlinable_f, nontailset_f, tailset_f) -> nontailset_f) fixfuncs_result) in
      let inlinable_fs = disjoint_id_map_union_ary (Array.map (fun (inlineable_f, nontailset_f, tailset_f) -> inlineable_f) fixfuncs_result) in
      let inlinable_fixterm = not (IntSet.exists ((>=) h) nontailset_fs) in
      let tailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) tailset_fs) in
      let nontailset_fs' = IntSet.map (fun k -> k - h) (IntSet.filter ((<) h) nontailset_fs) in
      if numargs < numargs_of_type env sigma tary.(j) || (* closure creation *)
         not inlinable_fixterm then
        (* At least one fix-bounded function is used at
          non-tail position or argument position.
          Assuming fix-bounded functions are strongly-connected,
          there is no tail position in this fix-term. *)
        let nontailset = IntSet.union tailset_fs' nontailset_fs' in
        let inlinable_fs' =
          Array.fold_left
            (fun fs name -> Id.Map.add (id_of_annotated_name name) false fs)
            inlinable_fs
            nary
        in
        (inlinable_fs', IntSet.union nontailset args_set, IntSet.empty)
      else
        let inlinable_fs' =
          Array.fold_left
            (fun fs name -> Id.Map.add (id_of_annotated_name name) true fs)
            inlinable_fs
            nary
        in
        (inlinable_fs', IntSet.union nontailset_fs' args_set, tailset_fs')

(*
  detect_inlinable_fixterm implementes TR[term]_numargs in doc/codegen.tex.
*)
let detect_inlinable_fixterm (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool Id.Map.t =
  let (inlinable, nontailset, tailset) = detect_inlinable_fixterm_rec env sigma term in
  inlinable

(*
  collect_fix_usage collects information for each fix-terms and fix-bounded functions.

  collect_fix_usage tracks the term will be translated by gen_head or gen_tail.
  tail_position=false means that term will be translated by gen_head.
  tail_position=true means that term will be translated by gen_tail.
*)

let rec collect_fix_usage_rec
    ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (tail_position : bool) (term : EConstr.t) (numargs : int)
    ~(used_as_call : bool ref list)
    ~(used_as_goto : bool ref list) :
    fixterm_t Seq.t * fixfunc_t Seq.t =
  let result = collect_fix_usage_rec1 ~inlinable_fixterms env sigma tail_position term numargs ~used_as_call ~used_as_goto in
  result
and collect_fix_usage_rec1 ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (tail_position : bool) (term : EConstr.t) (numargs : int)
    ~(used_as_call : bool ref list)
    ~(used_as_goto : bool ref list) :
    fixterm_t Seq.t * fixfunc_t Seq.t =
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
  | Case (ci,u,pms,p,iv,item,bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, p, iv, item, bl) in
      (* item cannot contain fix-term because item must be a Rel which type is inductive (non-function) type *)
      let results = Array.map2
        (fun (nas,body) (ctx,_) ->
          let env2 = EConstr.push_rel_context ctx env in
          let n = Array.length nas in
          let used_as_call2 = List.append (List.init n (fun _ -> ref false)) used_as_call in
          let used_as_goto2 = List.append (List.init n (fun _ -> ref false)) used_as_goto in
          collect_fix_usage_rec ~inlinable_fixterms env2 sigma
            tail_position body numargs ~used_as_call:used_as_call2 ~used_as_goto:used_as_goto2)
        bl bl0
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
        collect_fix_usage_rec ~inlinable_fixterms env2 sigma true b (numargs_of_exp env sigma b) ~used_as_call:used_as_call2 ~used_as_goto:used_as_goto2
      else
        collect_fix_usage_rec ~inlinable_fixterms env2 sigma tail_position b (numargs-1) ~used_as_call:used_as_call2 ~used_as_goto:used_as_goto2
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let fixterm_id = id_of_annotated_name nary.(j) in
      let inlinable = Id.Map.find (id_of_annotated_name nary.(j)) inlinable_fixterms in
      let h = Array.length nary in
      let env2 = EConstr.push_rec_types prec env in
      let used_as_call2 =
        list_rev_map_append
          (fun i -> ref (j = i && not tail_position && not inlinable))
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
        fixterm_tail_position = tail_position;
        fixterm_term_env = env;
        fixterm_term = term;
        fixterm_inlinable = inlinable;
      } in
      let fixfuncs =
        Array.to_seq
          (CArray.map2_i
            (fun i name ty ->
              let (formal_arguments, return_type) = c_args_and_ret_type env sigma ty in
              {
                fixfunc_func_id = id_of_annotated_name nary.(i);
                fixfunc_term_id = id_of_annotated_name nary.(j);
                fixfunc_term_env = env;
                fixfunc_inlinable = inlinable;
                fixfunc_used_as_call = !(List.nth used_as_call2 (h - i - 1));
                fixfunc_used_as_goto = !(List.nth used_as_goto2 (h - i - 1));
                fixfunc_formal_arguments = formal_arguments;
                fixfunc_return_type = return_type;
                fixfunc_top_call = None; (* dummy. updated by fixfunc_initialize_top_calls *)
                fixfunc_c_name = "dummy"; (* dummy. updated by fixfunc_initialize_c_names *)
                fixfunc_outer_variables = []; (* dummy. updated by fixfunc_initialize_outer_variables *)
              })
            nary tary)
      in
      (Seq.cons fixterm (concat_array_seq (Array.map fst results)),
       Seq.append fixfuncs (concat_array_seq (Array.map snd results)))

let make_fixfunc_table (fixfuncs : fixfunc_t list) : fixfunc_table =
  let fixfunc_tbl = Hashtbl.create 0 in
  List.iter (fun fixfunc -> Hashtbl.add fixfunc_tbl fixfunc.fixfunc_func_id fixfunc) fixfuncs;
  fixfunc_tbl

let collect_fix_usage
    ~(inlinable_fixterms : bool Id.Map.t)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    fixterm_t list * fixfunc_table =
  let (fixterms, fixfuncs) = collect_fix_usage_rec ~inlinable_fixterms env sigma true term (numargs_of_exp env sigma term) ~used_as_call:[] ~used_as_goto:[] in
  (List.of_seq fixterms, make_fixfunc_table (List.of_seq fixfuncs))

let rec fixfunc_initialize_top_calls (env : Environ.env) (sigma : Evd.evar_map)
    (top_c_func_name : string) (term : EConstr.t)
    (sibling_entfuncs : (bool * string * int * Id.t) list)
    ~(fixfunc_tbl : fixfunc_table) : unit =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      fixfunc_initialize_top_calls env2 sigma top_c_func_name e sibling_entfuncs ~fixfunc_tbl
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      fixfunc_initialize_top_calls env2 sigma top_c_func_name fary.(j) [] ~fixfunc_tbl;
      let key = id_of_annotated_name nary.(j) in
      let fixfunc = Hashtbl.find fixfunc_tbl key in
      Hashtbl.replace fixfunc_tbl key { fixfunc with fixfunc_top_call = Some top_c_func_name };
      (List.iter
        (fun (static, another_top_cfunc_name, i, fixfunc_id) ->
          fixfunc_initialize_top_calls env2 sigma another_top_cfunc_name fary.(i) [] ~fixfunc_tbl;
          let fixfunc = Hashtbl.find fixfunc_tbl fixfunc_id in
          Hashtbl.replace fixfunc_tbl fixfunc_id
            { fixfunc with
              fixfunc_top_call = Some another_top_cfunc_name;
              fixfunc_used_as_call = true })
        sibling_entfuncs)
  (* xxx: consider App *)
  | _ -> ()

let fixfunc_initialize_c_names (fixfunc_tbl : fixfunc_table) : unit =
  Hashtbl.filter_map_inplace
    (fun (fixfunc_id : Id.t) (fixfunc : fixfunc_t) ->
      let c_name =
        match fixfunc.fixfunc_top_call with
        | Some cfunc -> cfunc
        | None ->
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
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
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

let pr_outer_variable (outer : (string * string) list) : Pp.t =
  Pp.str "[" ++
  pp_joinmap_list (Pp.str ",")
    (fun (x,t) -> Pp.str "(" ++ Pp.str x ++ Pp.str "," ++ Pp.str t ++ Pp.str ")")
    outer ++
  Pp.str "]"

let check_eq_outer_variables outer1 outer2 =
  if outer1 <> outer2 then
    user_err (Pp.str "[codegen:bug] outer length differ:" +++ pr_outer_variable outer1 +++ Pp.str "<>" +++ pr_outer_variable outer2)

let _ = ignore check_eq_outer_variables

(*
  compute_naive_outer_variables computes outer variables in "naive" way:
  It contains all variables in env except fix-bounded functions.
  Note that the result is ordered from outside to inside of the term.
*)
let compute_naive_outer_variables ~(fixfunc_tbl : fixfunc_table) (env : Environ.env) (sigma : Evd.evar_map) : (string * c_typedata) list =
  let n = Environ.nb_rel env in
  let outer = ref [] in
  for i = 1 to n do
    let decl = Environ.lookup_rel i env in
    let x = Context.Rel.Declaration.get_name decl in
    let t = Context.Rel.Declaration.get_type decl in
    let id = id_of_name x in
    if not (Hashtbl.mem fixfunc_tbl id) then (* Don't include fix-bounded functions *)
      let c_ty = c_typename env sigma (EConstr.of_constr t) in
      if not (c_type_is_void c_ty) then
        outer := (str_of_name x, c_ty) :: !outer
  done;
  !outer

let compute_precise_outer_variables
    ~(fixfunc_tbl : fixfunc_table)
    (env : Environ.env) (sigma : Evd.evar_map)
    (fixterm_free_variables : (Id.t, Id.Set.t) Hashtbl.t) :
    ((*fixterm_id*)Id.t, (*outer_variables*)Id.Set.t) Hashtbl.t =
  let fixfunc_ids =
    Hashtbl.fold
      (fun fixfunc_id fixfunc set ->
        Id.Set.add fixfunc_id set)
      fixfunc_tbl
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
          match Hashtbl.find_opt fixfunc_tbl id with
          | None -> ()
          | Some fixfunc2 ->
            let fixterm2_id = fixfunc2.fixfunc_term_id in
            match Hashtbl.find_opt fixterm_free_variables fixterm2_id with
            | None -> ()
            | Some fv ->
                q := Id.Set.union !q fv)
      done;
      Hashtbl.add fixterm_outer_variables fixterm_id
        (Id.Set.diff !outer_variables fixfunc_ids))
    fixterm_free_variables;
  fixterm_outer_variables

let fixfunc_initialize_outer_variables
    (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t)
    ~(fixfunc_tbl : fixfunc_table) : unit =
  let fixterm_free_variables = fixterm_free_variables env sigma term in
  let outer_variables = compute_precise_outer_variables ~fixfunc_tbl env sigma fixterm_free_variables in
  Hashtbl.filter_map_inplace
    (fun (fixfunc_id : Id.t) (fixfunc : fixfunc_t) ->
      let fixterm_id = fixfunc.fixfunc_term_id in
      let ov = compute_naive_outer_variables ~fixfunc_tbl fixfunc.fixfunc_term_env sigma in
      let ov2 =
        if fixfunc.fixfunc_top_call <> None then
          ov
        else
          let precise_outer_variables = Hashtbl.find outer_variables fixterm_id in
          List.filter
            (fun (varname, vartype) ->
              Id.Set.mem (Id.of_string varname) precise_outer_variables)
            ov
      in
      Some { fixfunc with fixfunc_outer_variables = ov2 })
    fixfunc_tbl

let collect_fix_info (env : Environ.env) (sigma : Evd.evar_map) (name : string) (term : EConstr.t)
    (sibling_entfuncs : (bool * string * int * Id.t) list) : fixterm_t list * fixfunc_table =
  let inlinable_fixterms = detect_inlinable_fixterm env sigma term in
  let (fixterms, fixfunc_tbl) = collect_fix_usage ~inlinable_fixterms env sigma term in
  fixfunc_initialize_top_calls env sigma name term sibling_entfuncs ~fixfunc_tbl;
  fixfunc_initialize_c_names fixfunc_tbl;
  fixfunc_initialize_outer_variables env sigma term ~fixfunc_tbl;
  (*show_fixfunc_table env sigma fixfunc_tbl;*)
  (fixterms, fixfunc_tbl)

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

let decl_of_farg (x : Names.Name.t Context.binder_annot) (t : EConstr.types) : EConstr.rel_declaration =
  Context.Rel.Declaration.LocalAssum (x,t)

let ctx_of_fargs (fargs : (Names.Name.t Context.binder_annot * EConstr.types) list) : EConstr.rel_context =
  List.map (fun (x,t) -> decl_of_farg x t) fargs

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
      let ntf_j = ntfary.(j) in Array.blit ntfary 0 ntfary 1 j; ntfary.(0) <- ntf_j; (* move ntfary.(j) to the beginning *)
      List.concat_map
        (fun (n,t,f) ->
          let (f_fargs, f_body) = decompose_lam sigma f in
          let env3 = EConstr.push_rel_context (ctx_of_fargs f_fargs) env2 in
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
              env := EConstr.push_rel (decl_of_farg x t) !env)
            (List.rev fixfunc_fargs))
        context)
    fix_bodies

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

let rec gen_head ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(cont : head_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
  let pp = gen_head1 ~fixfunc_tbl ~used_vars ~cont env sigma term in
  (*msg_debug_hov (Pp.str "[codegen] gen_head:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_head1 ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(cont : head_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
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
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _ | Array _
  | Cast _ | CoFix _
  | App _ ->
      user_err (Pp.str "[codegen:gen_head] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
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
            let fname =
              match fixfunc.fixfunc_top_call with
              | Some top_func_name -> top_func_name
              | None -> fixfunc.fixfunc_c_name
            in
            if fixfunc.fixfunc_inlinable then
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
              let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str ("entry_" ^ fixfunc.fixfunc_c_name) ++ Pp.str ";") in
              pp_assignments +++ pp_goto_entry
            else
              gen_head_cont cont
                (gen_funcall fname
                  (Array.append
                    (Array.of_list (List.map fst fixfunc.fixfunc_outer_variables))
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
      gen_match used_vars gen_switch (gen_head ~fixfunc_tbl ~used_vars ~cont) env sigma ci item (bl,bl0)
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_proj env sigma pr item (gen_head_cont ~omit_void_exp:true cont))
  | LetIn (x,e,t,b) ->
      assert (cargs = []);
      let c_var = str_of_annotated_name x in
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
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
      gen_head ~fixfunc_tbl ~used_vars ~cont:cont1 env sigma e +++
      gen_head ~fixfunc_tbl ~used_vars ~cont env2 sigma b

  | Lambda (x,t,b) ->
      user_err (Pp.str "[codegen] gen_head: lambda term without argument (higher-order term not supported yet):" +++
        Printer.pr_econstr_env env sigma term)

  | Fix ((ks, j), ((nary, tary, fary))) ->
      let fixfunc_j = Hashtbl.find fixfunc_tbl (id_of_annotated_name nary.(j)) in
      let nj_formal_arguments = fixfunc_j.fixfunc_formal_arguments in
      if List.length cargs < List.length nj_formal_arguments then
        user_err (Pp.str "[codegen] gen_head: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let nj_funcname = fixfunc_j.fixfunc_c_name in
      if not fixfunc_j.fixfunc_inlinable then
        gen_head_cont cont
          (gen_funcall nj_funcname
            (Array.append
              (Array.of_list (List.map fst fixfunc_j.fixfunc_outer_variables))
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
              let exit_label = "exit_" ^ nj_funcname in
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
              let context_ary = Array.of_list context in
              let noninlinable_pred i (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) =
                let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name fixfunc_name) in
                not fixfunc_i.fixfunc_inlinable
              in
              let noninlinable_index = CArray.findi noninlinable_pred context_ary in
              let context_before_noninlinable =
                match noninlinable_index with
                | None -> context_ary
                | Some i -> Array.sub context_ary 0 i
              in
              let pp_labels =
                pp_sjoinmap_ary
                  (fun (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) ->
                    let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name fixfunc_name) in
                    let ni_funcname = fixfunc_i.fixfunc_c_name in
                    if fixfunc_i.fixfunc_used_as_goto ||
                       (fixfunc_i.fixfunc_used_as_call && fixfunc_i.fixfunc_top_call = None) then
                      Pp.str ("entry_" ^ ni_funcname) ++ Pp.str ":"
                    else
                      Pp.mt ())
                  context_before_noninlinable
              in
              match noninlinable_index with
              | None -> pp_labels +++ gen_head ~fixfunc_tbl ~used_vars ~cont:cont2 body_env sigma body
              | Some i ->
                  let (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) = context_ary.(i) in
                  let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name fixfunc_name) in
                  let ni_funcname = fixfunc_i.fixfunc_c_name in
                  let cargs = List.map (fun (c_arg, c_ty) -> if c_type_is_void c_ty then None
                                                                                    else Some c_arg)
                                       fixfunc_i.fixfunc_formal_arguments
                  in
                  pp_labels +++
                    gen_head_cont cont2
                      (gen_funcall ni_funcname
                        (Array.append
                          (Array.of_list (List.map fst fixfunc_i.fixfunc_outer_variables))
                          (Array.of_list (list_filter_none cargs)))))
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
      let retvar = "(*(" ^ compose_c_abstract_decl (compose_c_type cont.tail_cont_return_type "*" "") ^ ")codegen_ret)" in
      gen_assignment (Pp.str retvar) exp +++ Pp.str "return;"
    else
      Pp.hov 0 (Pp.str "return" +++ exp ++ Pp.str ";")

let rec gen_tail ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(cont : tail_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
  (*msg_debug_hov (Pp.str "[codegen] gen_tail start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "(" ++
    pp_sjoinmap_list Pp.str cargs ++
    Pp.str ")");*)
  let pp = gen_tail1 ~fixfunc_tbl ~used_vars ~cont env sigma term in
  (*msg_debug_hov (Pp.str "[codegen] gen_tail return:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_tail1 ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(cont : tail_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
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
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _ | Array _
  | Cast _ | CoFix _
  | App _ ->
      user_err (Pp.str "[codegen:gen_tail] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
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
            let funcname = fixfunc.fixfunc_c_name in
            let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str ("entry_" ^ funcname) ++ Pp.str ";") in
            pp_assignments +++ pp_goto_entry)
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
      gen_match used_vars gen_switch_without_break (gen_tail ~fixfunc_tbl ~used_vars ~cont) env sigma ci item (bl,bl0)
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_proj env sigma pr item (gen_tail_cont ~omit_void_exp:true cont))
  | LetIn (x,e,t,b) ->
      assert (cargs = []);
      let c_var = str_of_annotated_name x in
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
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
      gen_head ~fixfunc_tbl ~used_vars ~cont:cont1 env sigma e +++
      gen_tail ~fixfunc_tbl ~used_vars ~cont env2 sigma b

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
            let pp_labels =
              pp_sjoinmap_list
                (fun (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) ->
                  let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name fixfunc_name) in
                  let ni_funcname = fixfunc_i.fixfunc_c_name in
                  if fixfunc_i.fixfunc_used_as_goto || fixfunc_i.fixfunc_top_call = None then
                    Pp.str ("entry_" ^ ni_funcname) ++ Pp.str ":"
                  else
                    Pp.mt ()) (* Not reached.  Currently, fix-term in top-call are decomposed by obtain_function_bodies and gen_tail is not used for it. *)
                context
            in
            pp_labels +++ gen_tail ~fixfunc_tbl ~used_vars ~cont body_env sigma body)
          fix_bodies
      in
      pp_assignments +++ pp_sjoin_list pp_fixfuncs

let gen_function_header (static : bool) (return_type : c_typedata) (c_name : string)
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

(* internal entry functions *)
let fixfuncs_for_internal_entfuncs (fixfunc_tbl : fixfunc_table) : fixfunc_t list =
  Hashtbl.fold
    (fun fixfunc_id fixfunc fixfuncs ->
      if fixfunc.fixfunc_used_as_call &&
         fixfunc.fixfunc_top_call = None then
        fixfunc :: fixfuncs
      else
        fixfuncs)
    fixfunc_tbl
    []

(*
  detect_fixterms_for_bodies returns
  non-tail non-inlinable fixterms.

  gen_head generates code for non-tail position.
  However it's doesn't generate code for non-inlinable fixterms.
  They should be generated separatedly.
*)
let detect_fixterms_for_bodies
    ~(fixterms : fixterm_t list)
    ~(fixfunc_tbl : fixfunc_table) :
    ((*outer_variables*)((string * c_typedata) list) * Environ.env * EConstr.t) list =
  let non_inlinable_non_tail_position_fixterms =
    List.filter
      (fun fixterm ->
        not fixterm.fixterm_inlinable &&
        not fixterm.fixterm_tail_position)
    fixterms
  in
  List.map
    (fun fixterm ->
      let fixterm_id = fixterm.fixterm_term_id in
      let outer_variables = (Hashtbl.find fixfunc_tbl fixterm_id).fixfunc_outer_variables in
      (outer_variables, fixterm.fixterm_term_env, fixterm.fixterm_term))
    non_inlinable_non_tail_position_fixterms

let labels_for_stacked_fixfuncs
    ~(fixfunc_tbl : fixfunc_table)
    ~(primary_cfunc : string)
    (stacked_fixfuncs : string list) : string list =
  unique_string_list
    (CList.map_filter
      (fun fix_name ->
        let fixfunc = Hashtbl.find fixfunc_tbl (Id.of_string fix_name) in
        if fixfunc.fixfunc_used_as_goto || fixfunc.fixfunc_top_call <> Some primary_cfunc then
          Some ("entry_" ^ fixfunc.fixfunc_c_name)
        else
          None)
      stacked_fixfuncs)

let obtain_function_bodies1
    ~(fixfunc_tbl : fixfunc_table)
    ~(primary_cfunc : string)
    (env : Environ.env) (sigma : Evd.evar_map)
    (fargs : ((*varname*)string * (*vartype*)c_typedata) list) (stacked_fixfuncs : string list) (term : EConstr.t) :
    ((*return_type*)c_typedata * ((*varname*)string * (*vartype*)c_typedata) list * (*stacked_fixfuncs*)string list * Environ.env * EConstr.t) list =
  let fix_bodies = fix_body_list env sigma term in
  List.map
    (fun (context, (body_env, body)) ->
      let return_type =
        let ty = Reductionops.nf_all body_env sigma (Retyping.get_type_of body_env sigma body) in
        c_typename env sigma ty
      in
      let fargs =
        List.concat
          (List.append
            (List.rev_map
              (fun (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) ->
                List.filter_map
                  (fun (x,t) ->
                    let c_ty = c_typename env sigma t in
                    if c_type_is_void c_ty then
                      None
                    else
                      Some (str_of_annotated_name x, c_ty))
                  fixfunc_fargs)
              context)
            [fargs])
      in
      let stacked_fixfuncs =
        list_rev_map_append
          (fun (fixfunc_env2, fixfunc_env3, fixfunc_name, fixfunc_type, fixfunc_fargs) ->
            str_of_annotated_name fixfunc_name)
          context
          stacked_fixfuncs
      in
      (return_type, fargs, labels_for_stacked_fixfuncs ~fixfunc_tbl ~primary_cfunc stacked_fixfuncs, body_env, body))
    fix_bodies

let obtain_function_bodies
    ~(fixterms : fixterm_t list)
    ~(fixfunc_tbl : fixfunc_table)
    ~(primary_cfunc : string)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    ((*return_type*)c_typedata *
     ((*varname*)string * (*vartype*)c_typedata) list *
     (*labels*)string list *
     Environ.env *
     EConstr.t) list =
  let results =
    List.map
      (fun (outer_variables, env1, term1) ->
        let (term1_fargs, term1_body) = EConstr.decompose_lam sigma term1 in
        let env2 = EConstr.push_rel_context (ctx_of_fargs term1_fargs) env1 in
        let fargs =
          List.filter_map
            (fun (x,t) ->
              let c_ty = c_typename env sigma t in
              if c_type_is_void c_ty then
                None
              else
                Some (str_of_annotated_name x, c_ty))
            term1_fargs
        in
        obtain_function_bodies1 ~fixfunc_tbl ~primary_cfunc env2 sigma (List.append fargs outer_variables) [] term1_body)
      (([], env, term) ::
       detect_fixterms_for_bodies ~fixterms ~fixfunc_tbl)
  in
  List.concat results

let gen_func_single ~(fixterms : fixterm_t list) ~(fixfunc_tbl : fixfunc_table)
    ~(static : bool) ~(primary_cfunc : string) (env : Environ.env) (sigma : Evd.evar_map)
    (whole_term : EConstr.t) (return_type : c_typedata)
    (used_vars : Id.Set.t) : Pp.t =
  let bodies = obtain_function_bodies ~fixterms ~fixfunc_tbl ~primary_cfunc env sigma whole_term in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun (ret_type, args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          let cont = { tail_cont_return_type = return_type; tail_cont_multifunc = false } in
          pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
          gen_tail ~fixfunc_tbl ~used_vars ~cont env2 sigma body)
        bodies)
  in
  let c_fargs =
    let (ret_type, first_args, _, _, _) = List.hd bodies in
    List.rev first_args
  in
  let local_vars = List.filter
    (fun (c_ty, c_var) ->
      match List.find_opt (fun (c_var1, ty1) -> c_var = c_var1) c_fargs with
      | Some _ -> false (* xxx: check type mismach *)
      | None -> true)
    local_vars
  in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:6");*)
  Pp.v 0 (
  gen_function_header static return_type primary_cfunc c_fargs +++
  vbrace (
    pp_sjoinmap_list
      (fun (c_ty, c_var) -> Pp.hov 0 (pr_c_decl c_ty (Pp.str c_var) ++ Pp.str ";"))
      local_vars
    +++
    pp_body))

let gen_func_multi ~(fixterms : fixterm_t list) ~(fixfunc_tbl : fixfunc_table)
    ~(static : bool) ~(primary_cfunc : string) (env : Environ.env) (sigma : Evd.evar_map)
    (whole_term : EConstr.t) (formal_arguments : (string * c_typedata) list) (return_type : c_typedata)
    (used_vars : Id.Set.t) (internal_entfuncs : fixfunc_t list)
    (sibling_entfuncs : (bool * string * int * Id.t) list) : Pp.t =
  let func_index_type = "codegen_func_indextype_" ^ primary_cfunc in
  let func_index_prefix = "codegen_func_index_" in
  let sibling_and_internal_entfuncs =
    (List.map (fun (static1, another_top_cfunc_name, j, fixfunc_id) -> (static1, Hashtbl.find fixfunc_tbl fixfunc_id)) sibling_entfuncs) @
    List.map (fun fixfunc -> (true, fixfunc)) internal_entfuncs
  in
  let pp_enum =
    Pp.hov 0 (
      Pp.str "enum" +++
      Pp.str func_index_type +++
      hovbrace (
        pp_join_list (Pp.str "," ++ Pp.spc ())
          (Pp.str (func_index_prefix ^ primary_cfunc) ::
           List.map
             (fun (static1, fixfunc) -> Pp.str (func_index_prefix ^ fixfunc.fixfunc_c_name))
             sibling_and_internal_entfuncs)) ++
      Pp.str ";")
  in
  let pp_struct_args =
    let pr_members args =
      pp_sjoinmap_list
        (fun (c_arg, c_ty) -> Pp.hov 0 (pr_c_decl c_ty (Pp.str c_arg) ++ Pp.str ";"))
        args
    in
    (if CList.is_empty formal_arguments then
      Pp.mt ()
    else
      Pp.hv 0 (
      Pp.str ("struct codegen_args_" ^ primary_cfunc) +++
      hovbrace (pr_members formal_arguments) ++ Pp.str ";")) +++
    pp_sjoinmap_list
      (fun (static1, fixfunc) ->
        if CList.is_empty fixfunc.fixfunc_outer_variables &&
           CList.is_empty fixfunc.fixfunc_formal_arguments then
          Pp.mt ()
        else
          Pp.hv 0 (
          Pp.str ("struct codegen_args_" ^ fixfunc.fixfunc_c_name) +++
          hovbrace (
          pr_members fixfunc.fixfunc_outer_variables +++
          pr_members (List.filter_map
                       (fun (c_arg, c_ty) ->
                         if c_type_is_void c_ty then None
                         else Some (c_arg, c_ty))
                       fixfunc.fixfunc_formal_arguments)) ++ Pp.str ";"))
      sibling_and_internal_entfuncs
  in
  let pp_forward_decl =
    Pp.hv 0 (
      Pp.str "static void" +++
      Pp.str ("codegen_functions_" ^ primary_cfunc) ++
      Pp.str ("(enum " ^ func_index_type ^ " codegen_func_index, void *codegen_args, void *codegen_ret);"))
  in
  let pp_entry_functions =
    let pr_entry_function static c_name func_index formal_arguments return_type =
      let null = "((void*)0)" in (* We don't use NULL because it needs stddef.h *)
      let (pp_vardecl_args, pp_struct_arg) =
        if CList.is_empty formal_arguments then
          (Pp.mt (), null)
        else
          (Pp.hov 2
            (Pp.str ("struct codegen_args_" ^ c_name) +++
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
        Pp.hov 2 (Pp.str ("codegen_functions_" ^ primary_cfunc) ++
                  Pp.str "(" ++
                  Pp.str func_index ++ Pp.str "," +++
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
        gen_function_header static return_type c_name formal_arguments +++
        vbrace (
          pp_vardecl_args +++
          pp_vardecl_ret +++
          pp_call +++
          pp_return))
    in
    pr_entry_function static primary_cfunc (func_index_prefix ^ primary_cfunc)
      formal_arguments return_type +++
    pp_sjoinmap_list
      (fun (static1, fixfunc) ->
        pr_entry_function static1 fixfunc.fixfunc_c_name (func_index_prefix ^ fixfunc.fixfunc_c_name)
          (List.append
            fixfunc.fixfunc_outer_variables
            (List.filter_map
              (fun (c_arg, c_ty) ->
                if c_type_is_void c_ty then None
                else Some (c_arg, c_ty))
              fixfunc.fixfunc_formal_arguments))
          fixfunc.fixfunc_return_type)
      sibling_and_internal_entfuncs
  in
  let bodies = obtain_function_bodies ~fixterms ~fixfunc_tbl ~primary_cfunc env sigma whole_term in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun (ret_type, args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          let cont = { tail_cont_return_type = ret_type; tail_cont_multifunc = true } in
          Pp.v 0 (
            pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
            gen_tail ~fixfunc_tbl ~used_vars ~cont env2 sigma body))
        bodies)
  in
  let pp_local_variables_decls =
    pp_sjoinmap_list
      (fun (c_ty, c_var) -> Pp.hov 0 (pr_c_decl c_ty (Pp.str c_var) ++ Pp.str ";"))
      local_vars
  in
  let pp_switch_cases =
    pp_sjoinmap_list
      (fun (static1, fixfunc) ->
        let pp_case =
          Pp.str "case" +++ Pp.str (func_index_prefix ^ fixfunc.fixfunc_c_name) ++ Pp.str ":"
        in
        let pp_assign_outer =
          pp_sjoinmap_list
            (fun (c_arg, t) ->
              Pp.hov 0 (
                Pp.str c_arg +++
                Pp.str "=" +++
                Pp.str ("((struct codegen_args_" ^ fixfunc.fixfunc_c_name ^ " *)codegen_args)->" ^ c_arg) ++
                Pp.str ";"))
            fixfunc.fixfunc_outer_variables
        in
        let pp_assign_args =
          pp_sjoinmap_list
            (fun (c_arg, t) ->
              Pp.hov 0 (
                Pp.str c_arg +++
                Pp.str "=" +++
                Pp.str ("((struct codegen_args_" ^ fixfunc.fixfunc_c_name ^ " *)codegen_args)->" ^ c_arg) ++
                Pp.str ";"))
            (List.filter_map
              (fun (c_arg, c_ty) ->
                if c_type_is_void c_ty then None
                else Some (c_arg, c_ty))
              fixfunc.fixfunc_formal_arguments)
        in
        let pp_goto =
          Pp.str "goto" +++ Pp.str ("entry_" ^ fixfunc.fixfunc_c_name) ++ Pp.str ";"
        in
        let pp_result =
          Pp.hov 0 pp_case ++ Pp.brk (1,2) ++
          Pp.v 0 (
            pp_assign_outer +++
            pp_assign_args +++
            Pp.hov 0 pp_goto)
        in
        pp_result)
      sibling_and_internal_entfuncs
  in
  let pp_switch_default = Pp.str "default:" in
  let pp_assign_args_default =
    if formal_arguments = [] then
      Pp.str ";"
    else
      pp_sjoinmap_list
        (fun (c_arg, t) ->
          Pp.hov 0 (
            Pp.str c_arg +++
            Pp.str "=" +++
            Pp.str ("((struct codegen_args_" ^ primary_cfunc ^ " *)codegen_args)->" ^ c_arg) ++
            Pp.str ";"))
        formal_arguments
  in
  let pp_switch_body =
    pp_switch_cases +++
    Pp.hov 0 pp_switch_default ++ Pp.brk (1,2) ++
    Pp.v 0 pp_assign_args_default
  in
  let pp_switch =
    Pp.hov 0 (Pp.str "switch" +++ Pp.str "(codegen_func_index)") +++
    vbrace pp_switch_body
  in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:6");*)
  Pp.v 0 (
    pp_enum +++
    pp_struct_args +++
    pp_forward_decl +++
    pp_entry_functions +++
    Pp.str "static void" +++
    Pp.str ("codegen_functions_" ^ primary_cfunc) ++
    Pp.str ("(enum " ^ func_index_type ^ " codegen_func_index, void *codegen_args, void *codegen_ret)")) +++
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
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
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

let gen_func_sub (primary_cfunc : string) (sibling_entfuncs : (bool * string * int * Id.t) list) : Pp.t =
  let (static, ty, whole_term) = make_simplified_for_cfunc primary_cfunc in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_term = EConstr.of_constr whole_term in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments, return_type) = c_args_and_ret_type env sigma whole_ty in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:1");*)
  let (fixterms, fixfunc_tbl) = collect_fix_info env sigma primary_cfunc whole_term sibling_entfuncs in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:2");*)
  let used_vars = used_variables env sigma whole_term in
  let internal_entfuncs = fixfuncs_for_internal_entfuncs fixfunc_tbl in
  (if internal_entfuncs <> [] || sibling_entfuncs <> [] then
    let formal_arguments' =
      List.filter_map
        (fun (c_arg, c_ty) ->
          if c_type_is_void c_ty then None
          else Some (c_arg, c_ty))
        formal_arguments
    in
    gen_func_multi ~fixterms ~fixfunc_tbl ~static ~primary_cfunc env sigma whole_term formal_arguments' return_type used_vars internal_entfuncs sibling_entfuncs
  else
    gen_func_single ~fixterms ~fixfunc_tbl ~static ~primary_cfunc env sigma whole_term return_type used_vars) ++
  Pp.fnl ()

let gen_function ?(sibling_entfuncs : (bool * string * int * Id.t) list = []) (primary_cfunc : string) : Pp.t =
  local_gensym_with (fun () -> gen_func_sub primary_cfunc sibling_entfuncs)

let entfunc_of_sibling_cfunc (cfunc : string) : (bool * string * int * Id.t) option =
  let (static, ty, term) = make_simplified_for_cfunc cfunc in (* modify global env *)
  let (args, body) = Term.decompose_lam term in
  match Constr.kind body with
  | Fix ((ks, j), (nary, tary, fary)) -> Some (static, cfunc, j, id_of_annotated_name nary.(j))
  | _ -> None (* not reached *)

let gen_mutual (cfunc_names : string list) : Pp.t =
  match cfunc_names with
  | [] -> user_err (Pp.str "[codegen:bug] gen_mutual with empty cfunc_names")
  | primary_cfunc :: sibling_cfuncs ->
      let sibling_entfuncs =
        CList.map_filter entfunc_of_sibling_cfunc sibling_cfuncs
      in
      gen_function ~sibling_entfuncs primary_cfunc

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
  gen_function_header static return_type cfunc_name formal_arguments' ++ Pp.str ";"

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
          | Some (j, key) as v ->
              map := ConstrMap.update
                key
                (fun njs_opt ->
                  match njs_opt with
                  | None -> Some [(cfunc, j)]
                  | Some njs -> Some ((cfunc, j) :: njs))
                !map;
              v
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
          f (gen_function cfunc_name ++ Pp.fnl ())
      | GenMutual cfunc_names ->
          f (gen_mutual cfunc_names ++ Pp.fnl ())
      | GenPrototype cfunc_name ->
          f (gen_prototype cfunc_name ++ Pp.fnl ())
      | GenSnippet str ->
          f (Pp.str str ++ Pp.fnl ()))
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
