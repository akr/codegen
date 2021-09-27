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
  fixfunc_func: EConstr.t;
  fixfunc_inlinable: bool;
  fixfunc_used_as_call: bool;
  fixfunc_used_as_goto: bool;
  fixfunc_formal_arguments: (string * string) list; (* [(varname1, vartype1); ...] *)
  fixfunc_return_type: string;

  fixfunc_top_call: string option; (* by fixfunc_initialize_top_calls *)
  fixfunc_c_name: string; (* by fixfunc_initialize_c_names *)

  fixfunc_outer_variables: (string * string) list; (* [(varname1, vartype1); ...] *) (* by fixfunc_initialize_outer_variables *)
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
        Pp.str "formal_arguments=(" ++ pp_joinmap_list (Pp.str ",") (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str ty) fixfunc.fixfunc_formal_arguments ++ Pp.str ")" +++
        Pp.str "return_type=" ++ Pp.str fixfunc.fixfunc_return_type +++
        Pp.str "top_call=" ++ (match fixfunc.fixfunc_top_call with None -> Pp.str "None" | Some top -> Pp.str ("Some " ^ top)) +++
        Pp.str "c_name=" ++ Pp.str fixfunc.fixfunc_c_name +++
        Pp.str "outer_variables=(" ++ pp_joinmap_list (Pp.str ",") (fun (farg, ty) -> Pp.str farg ++ Pp.str ":" ++ Pp.str ty) fixfunc.fixfunc_outer_variables ++ Pp.str ")" +++
        Pp.mt ()
      ))
    fixfunc_tbl

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
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
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
      if numargs < numargs_of_type env sigma tary.(j) || (* closure creation *)
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
                fixfunc_func = fary.(i);
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
    (other_topfuncs : (bool * string * int * Id.t) list)
    ~(fixfunc_tbl : fixfunc_table) : unit =
  match EConstr.kind sigma term with
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      fixfunc_initialize_top_calls env2 sigma top_c_func_name e other_topfuncs ~fixfunc_tbl
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
        other_topfuncs)
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

(*
  compute_naive_outer_variables computes outer variables in "naive" way:
  It may contain unused variables.
  Note that the result is ordered from outside to inside of the term.
*)
let compute_naive_outer_variables ~(fixfunc_tbl : fixfunc_table) (env : Environ.env) (sigma : Evd.evar_map) : (string * string) list =
  let n = Environ.nb_rel env in
  let outer = ref [] in
  for i = 1 to n do
    let decl = Environ.lookup_rel i env in
    let x = Context.Rel.Declaration.get_name decl in
    let t = Context.Rel.Declaration.get_type decl in
    let id = id_of_name x in
    if not (Hashtbl.mem fixfunc_tbl id) then (* Don't include fix-bounded functions *)
      outer := (str_of_name x, c_typename env sigma (EConstr.of_constr t)) :: !outer;
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
    (other_topfuncs : (bool * string * int * Id.t) list) : fixterm_t list * fixfunc_table =
  let numargs = numargs_of_exp env sigma term in
  let inlinable_fixterms = detect_inlinable_fixterm env sigma term numargs in
  let (fixterms, fixfunc_tbl) = collect_fix_usage ~inlinable_fixterms env sigma term in
  fixfunc_initialize_top_calls env sigma name term other_topfuncs ~fixfunc_tbl;
  fixfunc_initialize_c_names fixfunc_tbl;
  fixfunc_initialize_outer_variables env sigma term ~fixfunc_tbl;
  (*show_fixfunc_table env sigma fixfunc_tbl;*)
  (fixterms, fixfunc_tbl)

let compute_called_fixfuncs (fixfunc_tbl : fixfunc_table) : fixfunc_t list =
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
  detect_fixterms_for_code_generation returns
  non-tail non-inlinable fixterms.

  gen_head generates code for non-tail position.
  However it's doesn't generate code for non-inlinable fixterms.
  They should be generated separatedly.
*)
let detect_fixterms_for_code_generation
    ~(fixterms : fixterm_t list)
    ~(fixfunc_tbl : fixfunc_table) :
    ((*outer_variables*)((string * string) list) * Environ.env * EConstr.t) list =
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

let rec obtain_function_bodies_rec
    ~(fixfunc_tbl : fixfunc_table)
    ~(primary_cfunc : string)
    (env : Environ.env) (sigma : Evd.evar_map)
    (fargs : ((*varname*)string * (*vartype*)string) list) (stacked_fixfuncs : string list) (term : EConstr.t) :
    (((*varname*)string * (*vartype*)string) list * (*stacked_fixfuncs*)string list * Environ.env * EConstr.t) Seq.t =
  match EConstr.kind sigma term with
  | Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let c_var = (str_of_annotated_name x, c_typename env sigma t) in
      obtain_function_bodies_rec ~fixfunc_tbl ~primary_cfunc env2 sigma (c_var :: fargs) stacked_fixfuncs b
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let bodies = Array.mapi
        (fun i ni ->
          let fixfunc_name = str_of_annotated_name ni in
          let fi = fary.(i) in
          if j = i then
            obtain_function_bodies_rec ~fixfunc_tbl ~primary_cfunc env2 sigma fargs (fixfunc_name :: stacked_fixfuncs) fi
          else
            obtain_function_bodies_rec ~fixfunc_tbl ~primary_cfunc env2 sigma fargs (fixfunc_name :: []) fi)
        nary
      in
      let reordered_bodies = Array.copy bodies in
      Array.blit bodies 0 reordered_bodies 1 j;
      reordered_bodies.(0) <- bodies.(j);
      concat_array_seq reordered_bodies
  | _ ->
      Seq.return (fargs, labels_for_stacked_fixfuncs ~fixfunc_tbl ~primary_cfunc stacked_fixfuncs, env, term)

let obtain_function_bodies
    ~(fixterms : fixterm_t list)
    ~(fixfunc_tbl : fixfunc_table)
    ~(primary_cfunc : string)
    (env : Environ.env) (sigma : Evd.evar_map)
    (term : EConstr.t) :
    (((*varname*)string * (*vartype*)string) list *
     (*labels*)string list *
     Environ.env *
     EConstr.t) list =
  let results =
    List.map
      (fun (outer_variables, env1, term1) ->
        obtain_function_bodies_rec ~fixfunc_tbl ~primary_cfunc env1 sigma outer_variables [] term1)
      (([], env, term) ::
       detect_fixterms_for_code_generation ~fixterms ~fixfunc_tbl)
  in
  List.of_seq (concat_list_seq results)

let local_gensym_id : (int ref) option ref = ref None

let local_gensym_with (f : unit -> 'a) : 'a =
  (if !local_gensym_id <> None then
    user_err (Pp.str "[codegen:bug] nested invocation of local_gensym_with"));
  local_gensym_id := Some (ref 0);
  let ret = f () in
  local_gensym_id := None;
  ret

let local_gensym () : string =
  match !local_gensym_id with
  | None -> user_err (Pp.str "[codegen:bug] local_gensym is called outside of local_gensym_with");
  | Some idref ->
      (let n = !idref in
      idref := n + 1;
      "tmp" ^ string_of_int n)

let local_vars : ((string * string) list ref) option ref = ref None

let local_vars_with (f : unit -> 'a) : (string * string) list * 'a =
  (if !local_vars <> None then
    user_err (Pp.str "[codegen:bug] nested invocation of local_vars_with"));
  let vars = ref [] in
  local_vars := Some vars;
  let ret = f () in
  local_vars := None;
  (List.rev !vars, ret)

let add_local_var (c_type : string) (c_var : string) : unit =
  match !local_vars with
  | None -> user_err (Pp.str "[codegen:bug] add_local_var is called outside of local_vars_with");
  | Some vars ->
      (match List.find_opt (fun (c_type1, c_var1) -> c_var1 = c_var) !vars with
      | Some (c_type1, c_var1) ->
          if c_type1 <> c_type then
            user_err (Pp.str "[codegen:bug] add_local_var : inconsistent typed variable")
          else
            ()
      | None -> vars := (c_type, c_var) :: !vars)

let carg_of_garg (env : Environ.env) (i : int) : string =
  let x = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
  str_of_name x

let gen_assignment (lhs : Pp.t) (rhs : Pp.t) : Pp.t =
  Pp.hov 0 (lhs +++ Pp.str "=" +++ rhs ++ Pp.str ";")

let gen_return (arg : Pp.t) : Pp.t =
  Pp.hov 0 (Pp.str "return" +++ arg ++ Pp.str ";")

let gen_void_return (retvar : string) (arg : Pp.t) : Pp.t =
  gen_assignment (Pp.str retvar) arg +++ Pp.str "return;"

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

let gen_match (used_vars : Id.Set.t) (gen_switch : Pp.t -> (string * Pp.t) array -> Pp.t)
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
      | None -> user_err (Pp.hov 2 (Pp.str "[codegen] cannot match linear variable without deallocator:" +++
          Pp.hov 0 (Printer.pr_econstr_env env sigma item +++ Pp.str ":" +++ Printer.pr_type_env env sigma item_type)))
      | Some dealloc_cfunc ->
          Pp.str dealloc_cfunc ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ");"
    else
      Pp.mt ()
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
        (if Id.Set.mem c_id used_vars then
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
            if Id.Set.mem (Id.of_string c_var) used_vars then
              gen_assignment (Pp.str c_var)
                (Pp.str access ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ")")
            else
              Pp.mt ())
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
    let swexpr = if swfunc = "" then
                   Pp.str item_cvar
                 else
                   Pp.str swfunc ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ")" in
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
  Pp.str accessor ++ Pp.str "(" ++ Pp.str item_cvar ++ Pp.str ")"

let gen_parallel_assignment (assignments : ((*lhs*)string * (*rhs*)string * (*type*)string) array) : Pp.t =
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

type head_cont = {
  head_cont_ret_var: string;
  head_cont_exit_label: string option;
}

let gen_head_cont (cont : head_cont) (rhs : Pp.t) : Pp.t =
  gen_assignment (Pp.str cont.head_cont_ret_var) rhs +++
  match cont.head_cont_exit_label with
  | None -> Pp.mt ()
  | Some label -> Pp.hov 0 (Pp.str "goto" +++ Pp.str label ++ Pp.str ";")

let rec gen_head ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(cont : head_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  let pp = gen_head1 ~fixfunc_tbl ~used_vars ~cont env sigma term cargs in
  (*msg_debug_hov (Pp.str "[codegen] gen_head:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_head1 ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(cont : head_cont) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _ | Array _
  | Cast _ | CoFix _ ->
      user_err (Pp.str "[codegen:gen_head] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_head_cont cont (Pp.str str)
      else
        let decl = Environ.lookup_rel i env in
        let name = Context.Rel.Declaration.get_name decl in
        (match Hashtbl.find_opt fixfunc_tbl (id_of_name name) with
        | Some fixfunc ->
            let fname =
              match fixfunc.fixfunc_top_call with
              | Some top_func_name -> top_func_name
              | None -> fixfunc.fixfunc_c_name
            in
            if fixfunc.fixfunc_inlinable then
              let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) fixfunc.fixfunc_formal_arguments cargs in
              let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
              let pp_goto_entry = Pp.hov 0 (Pp.str "goto" +++ Pp.str ("entry_" ^ fixfunc.fixfunc_c_name) ++ Pp.str ";") in
              pp_assignments +++ pp_goto_entry
            else
              gen_head_cont cont
                (gen_funcall fname
                  (Array.append
                    (Array.of_list (List.map fst fixfunc.fixfunc_outer_variables))
                    (Array.of_list cargs)))
        | None ->
          user_err (Pp.str "[codegen:gen_head] fix/closure call not supported yet"))
  | Const (ctnt,_) ->
      gen_head_cont cont (gen_app_const_construct env sigma (mkConst ctnt) (Array.of_list cargs))
  | Construct (cstr,_) ->
      gen_head_cont cont (gen_app_const_construct env sigma (mkConstruct cstr) (Array.of_list cargs))
  | App (f,args) ->
      let cargs2 =
        List.append
          (Array.to_list (Array.map (fun arg -> carg_of_garg env (destRel sigma arg)) args))
          cargs
      in
      gen_head ~fixfunc_tbl ~used_vars ~cont env sigma f cargs2
  | Case (ci,predicate,iv,item,branches) ->
      let gen_switch =
        match cont.head_cont_exit_label with
        | None -> gen_switch_with_break
        | Some _ -> gen_switch_without_break
      in
      gen_match used_vars gen_switch (gen_head ~fixfunc_tbl ~used_vars ~cont) env sigma ci predicate item branches cargs
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_head_cont cont (gen_proj env sigma pr item))
  | LetIn (x,e,t,b) ->
      let c_var = str_of_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      let cont1 = { head_cont_ret_var = c_var;
                    head_cont_exit_label = None; } in
      gen_head ~fixfunc_tbl ~used_vars ~cont:cont1 env sigma e [] +++
      gen_head ~fixfunc_tbl ~used_vars ~cont env2 sigma b cargs

  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
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
              (Array.of_list cargs)))
      else
        let env2 = EConstr.push_rec_types prec env in
        let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) nj_formal_arguments cargs in
        let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
        let exit_label = "exit_" ^ nj_funcname in
        let cont2 = match cont.head_cont_exit_label with
                    | None -> { cont with head_cont_exit_label = Some exit_label }
                    | Some _ -> cont
        in
        let pp_exit =
          match cont.head_cont_exit_label with
          | None -> Pp.hov 0 (Pp.str exit_label ++ Pp.str ":")
          | Some _ -> Pp.mt ()
        in
        let pp_bodies =
          Array.mapi
            (fun i ni ->
              let fi = fary.(i) in
              let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name ni) in
              let ni_formal_arguments = fixfunc_i.fixfunc_formal_arguments in
              List.iter
                (fun (c_arg, t) -> add_local_var t c_arg)
                ni_formal_arguments;
              let ni_formal_argvars = List.map fst ni_formal_arguments in
              let ni_funcname = fixfunc_i.fixfunc_c_name in
              let pp_label =
                if fixfunc_i.fixfunc_used_as_goto ||
                   (fixfunc_i.fixfunc_used_as_call && fixfunc_i.fixfunc_top_call = None) then
                  Pp.str ("entry_" ^ ni_funcname)  ++ Pp.str ":"
                else
                  Pp.mt ()
              in
              pp_label +++ gen_head ~fixfunc_tbl ~used_vars ~cont:cont2 env2 sigma fi ni_formal_argvars)
            nary in
        let reordered_pp_bodies = Array.copy pp_bodies in
        Array.blit pp_bodies 0 reordered_pp_bodies 1 j;
        reordered_pp_bodies.(0) <- pp_bodies.(j);
        pp_assignments +++ pp_sjoin_ary reordered_pp_bodies +++ pp_exit

  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "[codegen] gen_head: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_head] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_head ~fixfunc_tbl ~used_vars ~cont env2 sigma b rest)

let rec gen_tail ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  (*msg_debug_hov (Pp.str "[codegen] gen_tail start:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "(" ++
    pp_sjoinmap_list Pp.str cargs ++
    Pp.str ")");*)
  let pp = gen_tail1 ~fixfunc_tbl ~used_vars ~gen_ret env sigma term cargs in
  (*msg_debug_hov (Pp.str "[codegen] gen_tail return:" +++
    Printer.pr_econstr_env env sigma term +++
    Pp.str "->" +++
    pp);*)
  pp
and gen_tail1 ~(fixfunc_tbl : fixfunc_table) ~(used_vars : Id.Set.t) ~(gen_ret : Pp.t -> Pp.t) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (cargs : string list) : Pp.t =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _
  | Evar _ | Prod _
  | Int _ | Float _ | Array _
  | Cast _ | CoFix _ ->
      user_err (Pp.str "[codegen:gen_tail] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.length cargs = 0 then
        let str = carg_of_garg env i in
        gen_ret (Pp.str str)
      else
        let key = Context.Rel.Declaration.get_name (Environ.lookup_rel i env) in
        let fixfunc_opt = Hashtbl.find_opt fixfunc_tbl (id_of_name key) in
        (match fixfunc_opt with
        | None -> user_err (Pp.str "[codegen] gen_tail doesn't support partial application to (non-fixpoint) Rel, yet:" +++ Printer.pr_econstr_env env sigma term)
        | Some fixfunc ->
            let formal_arguments = fixfunc.fixfunc_formal_arguments in
            if List.length cargs < List.length formal_arguments then
              user_err (Pp.str "[codegen] gen_tail: partial application for fix-bounded-variable (higher-order term not supported yet):" +++
                Printer.pr_econstr_env env sigma term);
            let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) formal_arguments cargs in
            let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
            let funcname = fixfunc.fixfunc_c_name in
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
      gen_tail ~fixfunc_tbl ~used_vars ~gen_ret env sigma f cargs2
  | Lambda (x,t,b) ->
      (match cargs with
      | [] -> user_err (Pp.str "[codegen] gen_tail: lambda term without argument (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term)
      | arg :: rest ->
          (if Context.binder_name x <> Name.Name (Id.of_string arg) then
            Feedback.msg_warning (Pp.str "[codegen:gen_tail] lambda argument doesn't match to outer application argument"));
          let decl = Context.Rel.Declaration.LocalAssum (Context.nameR (Id.of_string arg), t) in
          let env2 = EConstr.push_rel decl env in
          gen_tail ~fixfunc_tbl ~used_vars ~gen_ret env2 sigma b rest)
  | Case (ci,predicate,iv,item,branches) ->
      gen_match used_vars gen_switch_without_break (gen_tail ~fixfunc_tbl ~used_vars ~gen_ret) env sigma ci predicate item branches cargs
  | Proj (pr, item) ->
      ((if cargs <> [] then
        user_err (Pp.str "[codegen:gen_head] projection cannot return a function, yet:" +++ Printer.pr_econstr_env env sigma term));
      gen_ret (gen_proj env sigma pr item))
  | LetIn (x,e,t,b) ->
      let c_var = str_of_annotated_name x in
      add_local_var (c_typename env sigma t) c_var;
      let decl = Context.Rel.Declaration.LocalDef (Context.nameR (Id.of_string c_var), e, t) in
      let env2 = EConstr.push_rel decl env in
      let cont1 = { head_cont_ret_var = c_var;
                    head_cont_exit_label = None; } in
      gen_head ~fixfunc_tbl ~used_vars ~cont:cont1 env sigma e [] +++
      gen_tail ~fixfunc_tbl ~used_vars ~gen_ret env2 sigma b cargs

  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let fixfunc_j = Hashtbl.find fixfunc_tbl (id_of_annotated_name nary.(j)) in
      let nj_formal_arguments = fixfunc_j.fixfunc_formal_arguments in
      if List.length cargs < List.length nj_formal_arguments then
        user_err (Pp.str "[codegen] gen_tail: partial application for fix-term (higher-order term not supported yet):" +++
          Printer.pr_econstr_env env sigma term);
      let assginments = List.map2 (fun (lhs, t) rhs -> (lhs, rhs, t)) nj_formal_arguments cargs in
      let pp_assignments = gen_parallel_assignment (Array.of_list assginments) in
      let pp_bodies =
        Array.mapi
          (fun i ni ->
            let fi = fary.(i) in
            let fixfunc_i = Hashtbl.find fixfunc_tbl (id_of_annotated_name ni) in
            let ni_formal_arguments = fixfunc_i.fixfunc_formal_arguments in
            List.iter
              (fun (c_arg, t) -> add_local_var t c_arg)
              ni_formal_arguments;
            let ni_formal_argvars = List.map fst ni_formal_arguments in
            let ni_funcname = fixfunc_i.fixfunc_c_name in
            let pp_label =
              if fixfunc_i.fixfunc_used_as_goto || fixfunc_i.fixfunc_top_call = None then
                Pp.str ("entry_" ^ ni_funcname) ++ Pp.str ":"
              else
                Pp.mt () (* Not reached.  Currently, fix-term in top-call are decomposed by obtain_function_bodies and gen_tail is not used for it. *)
            in
            pp_label +++ gen_tail ~fixfunc_tbl ~used_vars ~gen_ret env2 sigma fi ni_formal_argvars)
          nary in
      let reordered_pp_bodies = Array.copy pp_bodies in
      Array.blit pp_bodies 0 reordered_pp_bodies 1 j;
      reordered_pp_bodies.(0) <- pp_bodies.(j);
      pp_assignments +++ pp_sjoin_ary reordered_pp_bodies

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
        Pp.hov 0 (Pp.str t +++ Pp.str c_arg))
      formal_arguments) ++
    Pp.str ")"
  in
  Pp.hov 0 pp_return_type +++
  Pp.str c_name ++
  Pp.hov 0 (pp_parameters)

let gen_func_single ~(fixterms : fixterm_t list) ~(fixfunc_tbl : fixfunc_table)
    ~(static : bool) ~(primary_cfunc : string) (env : Environ.env) (sigma : Evd.evar_map)
    (whole_body : EConstr.t) (return_type : string)
    (used_vars : Id.Set.t) : Pp.t =
  let bodies = obtain_function_bodies ~fixterms ~fixfunc_tbl ~primary_cfunc env sigma whole_body in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun (args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
          gen_tail ~fixfunc_tbl ~used_vars ~gen_ret:gen_return env2 sigma body [])
        bodies)
  in
  let c_fargs =
    let (first_args, _, _, _) = List.hd bodies in
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
  Pp.v 0 (
  gen_function_header static return_type primary_cfunc c_fargs +++
  vbrace (
    pp_sjoinmap_list
      (fun (c_type, c_var) -> Pp.hov 0 (Pp.str c_type +++ Pp.str c_var ++ Pp.str ";"))
      local_vars
    +++
    pp_body))

let gen_func_multi ~(fixterms : fixterm_t list) ~(fixfunc_tbl : fixfunc_table)
    ~(static : bool) ~(primary_cfunc : string) (env : Environ.env) (sigma : Evd.evar_map)
    (whole_body : EConstr.t) (formal_arguments : (string * string) list) (return_type : string)
    (used_vars : Id.Set.t) (called_fixfuncs : fixfunc_t list)
    (other_topfuncs : (bool * string * int * Id.t) list) : Pp.t =
  let func_index_type = "codegen_func_indextype_" ^ primary_cfunc in
  let func_index_prefix = "codegen_func_index_" in
  let other_topfuncs_and_called_fixfuncs =
    (List.map (fun (static1, another_top_cfunc_name, j, fixfunc_id) -> (static1, Hashtbl.find fixfunc_tbl fixfunc_id)) other_topfuncs) @
    List.map (fun fixfunc -> (true, fixfunc)) called_fixfuncs
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
             other_topfuncs_and_called_fixfuncs)) ++
      Pp.str ";")
  in
  let pp_struct_args =
    let pr_members args =
      pp_sjoinmap_list
        (fun (c_arg, t) -> Pp.hov 0 (Pp.str t +++ Pp.str c_arg ++ Pp.str ";"))
        args
    in
    Pp.hv 0 (
    Pp.str ("struct codegen_args_" ^ primary_cfunc) +++
    hovbrace (
    pr_members formal_arguments +++
    (if CList.is_empty formal_arguments then
      (* empty struct is undefined behavior *)
      Pp.str "int" +++ Pp.str "dummy;" (* Not reached because fixfunc_formal_arguments cannot be empty. *)
    else
      Pp.mt ())) ++ Pp.str ";") +++
    pp_sjoinmap_list
      (fun (static1, fixfunc) ->
        Pp.hv 0 (
        Pp.str ("struct codegen_args_" ^ fixfunc.fixfunc_c_name) +++
        hovbrace (
        pr_members fixfunc.fixfunc_outer_variables +++
        pr_members fixfunc.fixfunc_formal_arguments +++
        (if CList.is_empty fixfunc.fixfunc_outer_variables &&
            CList.is_empty fixfunc.fixfunc_formal_arguments then
          (* empty struct is undefined behavior *)
          Pp.str "int" +++ Pp.str "dummy;" (* Not reached because fixfunc_formal_arguments cannot be empty. *)
        else
          Pp.mt ())) ++ Pp.str ";"))
      other_topfuncs_and_called_fixfuncs
  in
  let pp_forward_decl =
    Pp.hv 0 (
      Pp.str "static void" +++
      Pp.str ("codegen_functions_" ^ primary_cfunc) ++
      Pp.str ("(enum " ^ func_index_type ^ " codegen_func_index, void *codegen_args, void *codegen_ret);"))
  in
  let pp_entry_functions =
    let pr_entry_function static c_name func_index formal_arguments return_type =
      let pp_vardecl_args =
        Pp.str ("struct codegen_args_" ^ c_name) +++
        Pp.str "codegen_args" +++
        Pp.str "=" +++
        hovbrace (
          (pp_joinmap_list (Pp.str "," ++ Pp.spc ())
            (fun (c_arg, t) -> Pp.str c_arg)
            formal_arguments)) ++
        Pp.str ";"
      in
      let pp_vardecl_ret =
        Pp.str return_type +++
        Pp.str "codegen_ret;"
      in
      let pp_call =
        Pp.str ("codegen_functions_" ^ primary_cfunc) ++
        Pp.str "(" ++
        Pp.str func_index ++ Pp.str "," +++
        Pp.str "&codegen_args," +++
        Pp.str "&codegen_ret);"
      in
      let pp_return =
        Pp.str "return codegen_ret;"
      in
      Pp.v 0 (
        gen_function_header static return_type c_name formal_arguments +++
        vbrace (
          Pp.hov 0 (pp_vardecl_args) +++
          Pp.hov 0 (pp_vardecl_ret) +++
          Pp.hov 0 pp_call +++
          Pp.hov 0 pp_return))
    in
    pr_entry_function static primary_cfunc (func_index_prefix ^ primary_cfunc)
      formal_arguments return_type +++
    pp_sjoinmap_list
      (fun (static1, fixfunc) ->
        pr_entry_function static1 fixfunc.fixfunc_c_name (func_index_prefix ^ fixfunc.fixfunc_c_name)
          (List.append
            fixfunc.fixfunc_outer_variables
            fixfunc.fixfunc_formal_arguments)
          fixfunc.fixfunc_return_type)
      other_topfuncs_and_called_fixfuncs
  in
  let bodies = obtain_function_bodies ~fixterms ~fixfunc_tbl ~primary_cfunc env sigma whole_body in
  let gen_ret = (gen_void_return ("(*(" ^ return_type ^ " *)codegen_ret)")) in
  let (local_vars, pp_body) = local_vars_with
    (fun () ->
      pp_sjoinmap_list
        (fun (args, labels, env2, body) ->
          List.iter
            (fun (arg_name, arg_type) -> add_local_var arg_type arg_name)
            (List.rev args);
          Pp.v 0 (
            pp_sjoinmap_list (fun l -> Pp.str (l ^ ":")) labels +++
            gen_tail ~fixfunc_tbl ~used_vars ~gen_ret env2 sigma body []))
        bodies)
  in
  let pp_local_variables_decls =
    pp_sjoinmap_list
      (fun (c_type, c_var) -> Pp.hov 0 (Pp.str c_type +++ Pp.str c_var ++ Pp.str ";"))
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
            fixfunc.fixfunc_formal_arguments
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
      other_topfuncs_and_called_fixfuncs
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

let is_static_function_icommand (icommand : instance_command) : bool =
  match icommand with
  | CodeGenFunction -> false
  | CodeGenStaticFunction -> true
  | CodeGenPrimitive -> user_err (Pp.str "[codegen] unexpected CodeGenPrimitive")
  | CodeGenConstant -> user_err (Pp.str "[codegen] unexpected CodeGenConstant")

let get_ctnt_type_body_from_cfunc (cfunc_name : string) :
    (*static*)bool * Constant.t * Constr.types * Constr.t =
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

let gen_func_sub (primary_cfunc : string) (other_topfuncs : (bool * string * int * Id.t) list) : Pp.t =
  let (static, ctnt, ty, whole_body) = get_ctnt_type_body_from_cfunc primary_cfunc in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_body = EConstr.of_constr whole_body in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments, return_type) = c_args_and_ret_type env sigma whole_ty in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:1");*)
  let (fixterms, fixfunc_tbl) = collect_fix_info env sigma primary_cfunc whole_body other_topfuncs in
  (*msg_debug_hov (Pp.str "[codegen] gen_func_sub:2");*)
  let used_vars = used_variables env sigma whole_body in
  let called_fixfuncs = compute_called_fixfuncs fixfunc_tbl in
  (if called_fixfuncs <> [] || other_topfuncs <> [] then
    gen_func_multi ~fixterms ~fixfunc_tbl ~static ~primary_cfunc env sigma whole_body formal_arguments return_type used_vars called_fixfuncs other_topfuncs
  else
    gen_func_single ~fixterms ~fixfunc_tbl ~static ~primary_cfunc env sigma whole_body return_type used_vars) ++
  Pp.fnl ()

let gen_function ?(other_topfuncs : (bool * string * int * Id.t) list = []) (primary_cfunc : string) : Pp.t =
  local_gensym_with (fun () -> gen_func_sub primary_cfunc other_topfuncs)

let another_topfunc_for_mutual_recursion (cfunc : string) : (bool * string * int * Id.t) option =
  let (static, ctnt, ty, term) = get_ctnt_type_body_from_cfunc cfunc in (* modify global env *)
  let (args, body) = Term.decompose_lam term in
  match Constr.kind body with
  | Fix ((ks, j), (nary, tary, fary)) -> Some (static, cfunc, j, id_of_annotated_name nary.(j))
  | _ -> None (* not reached *)

let gen_mutual (cfunc_names : string list) : Pp.t =
  match cfunc_names with
  | [] -> user_err (Pp.str "[codegen:bug] gen_mutual with empty cfunc_names")
  | cfunc :: other_cfuncs ->
      let other_topfuncs =
        CList.map_filter another_topfunc_for_mutual_recursion other_cfuncs
      in
      gen_function ~other_topfuncs cfunc

let gen_prototype (cfunc_name : string) : Pp.t =
  let (static, ctnt, ty, whole_body) = get_ctnt_type_body_from_cfunc cfunc_name in (* modify global env *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let whole_ty = Reductionops.nf_all env sigma (EConstr.of_constr ty) in
  let (formal_arguments, return_type) = c_args_and_ret_type env sigma whole_ty in
  gen_function_header static return_type cfunc_name formal_arguments ++ Pp.str ";"

let common_key_for_mutual_recursion (term : Constr.t) : (int * Constr.t) option =
  let (args, body) = Term.decompose_lam term in
  match Constr.kind body with
  | Fix ((ks, j), (nary, tary, fary)) ->
      Some (j, Term.compose_lam args (Constr.mkFix ((ks, 0), (nary, tary, fary))))
  | _ -> None

let codegen_detect_mutual_recursion (gen_list : code_generation list) : code_generation list =
  let map = ref ConstrMap.empty in
  let gens = List.map
    (fun gen ->
      gen,
      (match gen with
      | GenFunc cfunc ->
          let (static, ctnt, ty, body) = get_ctnt_type_body_from_cfunc cfunc in
          (match common_key_for_mutual_recursion body with
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
    else CString.Map.map codegen_detect_mutual_recursion gen_map in
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
            | None -> codegen_define_instance env sigma CodeGenFunction func [] None
            | Some sp_inst -> (env, sp_inst)
          in
          GenFunc sp_inst.sp_cfunc_name)
      cfunc_list
  in
  (* Don't call codegen_resolve_dependencies.
     CodeGen Gen is used to test code generation of specified functions.
     Generating non-specified functions would make result longer with uninteresting functions. *)
  let gen_list = codegen_detect_mutual_recursion gen_list in
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
