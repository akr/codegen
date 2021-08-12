open Names
open GlobRef
open Pp
open CErrors
open Term
open Constr
open EConstr

open Cgenutil
open State

module IntMap = HMap.Make(Int)

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = Reductionops.nf_all env sigma term

let prod_appvect (sigma : Evd.evar_map) (c : EConstr.t) (v : EConstr.t array) : EConstr.t = EConstr.of_constr (prod_appvect (EConstr.to_constr sigma c) (Array.map (EConstr.to_constr sigma) v))

let rec is_concrete_inductive_type (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool =
  let termty = Retyping.get_type_of env sigma term in
  (if isSort sigma termty then
    match EConstr.kind sigma term with
    | Ind _ -> true
    | App (f, argsary) ->
        isInd sigma f &&
        Array.for_all (is_concrete_inductive_type env sigma) argsary
    | _ -> false
  else
    false) (* "list" is not "concrete" inductive type because it has concrete parameter *)

let command_linear (ty : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, ty2) = Constrintern.interp_constr_evars env sigma ty in
  let ty4 = nf_all env sigma ty2 in
  (if not (is_concrete_inductive_type env sigma ty4) then
    user_err (str "[codegen] linear: concrete inductive type expected:" +++ Printer.pr_econstr_env env sigma ty4));
  type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty4) Linear !type_linearity_map;
  Feedback.msg_info (str "[codegen] linear type registered:" +++ Printer.pr_econstr_env env sigma ty2)

let type_of_inductive_arity (mind_arity : (Declarations.regular_inductive_arity, Declarations.template_arity) Declarations.declaration_arity) : Constr.t =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Constr.mkType (temp_arity : Declarations.template_arity).Declarations.template_level

let valid_type_param (env : Environ.env) (sigma : Evd.evar_map) (decl : Constr.rel_declaration) : bool =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> isSort sigma (whd_all env sigma (EConstr.of_constr ty))
  | Context.Rel.Declaration.LocalDef _ -> false

let rec hasRel (sigma : Evd.evar_map) (term : EConstr.t) : bool =
  match EConstr.kind sigma term with
  | Rel i -> true
  | Var name -> false
  | Meta i -> false
  | Evar (ekey, terms) -> List.exists (hasRel sigma) terms
  | Sort s -> false
  | Cast (expr, kind, ty) -> hasRel sigma expr || hasRel sigma ty
  | Prod (name, ty, body) -> hasRel sigma ty || hasRel sigma body
  | Lambda (name, ty, body) -> hasRel sigma ty || hasRel sigma body
  | LetIn (name, expr, ty, body) -> hasRel sigma expr || hasRel sigma ty || hasRel sigma body
  | App (f, argsary) -> hasRel sigma f || Array.exists (hasRel sigma) argsary
  | Const ctntu -> false
  | Ind iu -> false
  | Construct cstru -> false
  | Case (ci, tyf, iv, expr, brs) -> hasRel sigma tyf || hasRel sigma expr || Array.exists (hasRel sigma) brs
  | Fix ((ia, i), (nameary, tyary, funary)) -> Array.exists (hasRel sigma) tyary || Array.exists (hasRel sigma) funary
  | CoFix (i, (nameary, tyary, funary)) -> Array.exists (hasRel sigma) tyary || Array.exists (hasRel sigma) funary
  | Proj (proj, expr) -> hasRel sigma expr
  | Int n -> false
  | Float n -> false
  | Array (u,t,def,ty) -> Array.exists (hasRel sigma) t || hasRel sigma def || hasRel sigma ty

let rec destProdX_rec (sigma : Evd.evar_map) (term : EConstr.t) : Names.Name.t Context.binder_annot list * EConstr.t list * EConstr.t =
  match EConstr.kind sigma term with
  | Prod (name, ty, body) ->
      let (names, tys, body) = destProdX_rec sigma body in
      (name :: names, ty :: tys, body)
  | _ -> ([], [], term)

let destProdX (sigma : Evd.evar_map) (term : EConstr.t) : Names.Name.t Context.binder_annot array * EConstr.t array * EConstr.t =
  let (names, tys, body) = destProdX_rec sigma term in
  (Array.of_list names, Array.of_list tys, body)

let rec is_linear_type (env : Environ.env) (sigma :Evd.evar_map) (ty : EConstr.t) : bool =
  (*Feedback.msg_debug (str "[codegen] is_linear_type:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match EConstr.kind sigma ty with
  | Sort _ ->
      (* types cannot be linear. *)
      false
  | Prod (name, namety, body) ->
      ignore (is_linear_type env sigma namety);
      ignore (is_linear_type env sigma body);
      false (* function (closure) must not reference outside linear variables *)
  | Ind iu -> is_linear_app env sigma ty
  | App (f, argsary) -> is_linear_app env sigma ty
  | _ -> user_err (str "[codegen] is_linear_type: unexpected term:" +++ Printer.pr_econstr_env env sigma ty)
and is_linear_app (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (str "[codegen] is_linear_app:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  match ConstrMap.find_opt (EConstr.to_constr sigma ty) !type_linearity_map with
  | Some Linear -> true
  | Some Unrestricted -> false
  | Some Investigating -> false
  | None ->
      (type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty) Investigating !type_linearity_map;
      if is_linear_ind env sigma ty then
        (Feedback.msg_info (str "[codegen] Linear type registered:" +++ Printer.pr_econstr_env env sigma ty);
        type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty) Linear !type_linearity_map;
        true)
      else
        (Feedback.msg_info (str "[codegen] Unrestricted type registered:" +++ Printer.pr_econstr_env env sigma ty);
        type_linearity_map := ConstrMap.add (EConstr.to_constr sigma ty) Unrestricted !type_linearity_map;
        false))
and is_linear_ind (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (str "[codegen] is_linear_ind:ty=" ++ Printer.pr_econstr_env env sigma ty);*)
  let (ind_f, argsary) =
    match EConstr.kind sigma ty with
    | App (f, argsary) -> (f, argsary)
    | _ -> (ty, [| |])
  in
  if not (isInd sigma ind_f) then
    user_err (str "[codegen] is_linear_ind: inductive type application expected:" +++ Printer.pr_econstr_env env sigma ty);
  let ((mutind, i), _) = destInd sigma ind_f in
  let mind_body = Environ.lookup_mind mutind env in
  if mind_body.Declarations.mind_nparams <> mind_body.Declarations.mind_nparams_rec then
    user_err (str "[codegen] is_linear_ind: non-uniform inductive type:" +++ Printer.pr_econstr_env env sigma ind_f);
  if not (List.for_all (valid_type_param env sigma) mind_body.Declarations.mind_params_ctxt) then
    user_err (str "[codegen] is_linear_ind: non-type parameter:" +++ Printer.pr_econstr_env env sigma ind_f);
  let ind_ary = Array.map (fun j -> Constr.mkInd (mutind, j))
      (iota_ary 0 (Array.length mind_body.Declarations.mind_packets)) in
  let params = Array.sub argsary 0 mind_body.Declarations.mind_nparams in
  let env = Environ.push_rel_context (
      List.map (fun ii0 ->
        let oind_body = mind_body.Declarations.mind_packets.(Array.length mind_body.Declarations.mind_packets - ii0 - 1) in
        Context.Rel.Declaration.LocalDef
          (Context.annotR (Names.Name.Name oind_body.Declarations.mind_typename),
           ind_ary.(Array.length mind_body.Declarations.mind_packets - ii0 - 1),
           type_of_inductive_arity oind_body.Declarations.mind_arity))
        (iota_list 0 (Array.length mind_body.Declarations.mind_packets))
    ) env in
  let oind_body = mind_body.Declarations.mind_packets.(i) in
  let cons_is_linear = Array.map
    (fun nf_lc ->
      let user_lc =
        let ((ctx : Constr.rel_context), (t : Constr.t)) = nf_lc in
        Context.Rel.fold_inside
          (fun (t : Constr.t) (decl : Constr.rel_declaration) ->
            match decl with
            | Context.Rel.Declaration.LocalAssum (name, ty) -> Constr.mkProd (name, ty, t)
            | Context.Rel.Declaration.LocalDef (name, expr, ty) -> Constr.mkLetIn (name, expr, ty, t))
          ~init:t ctx
      in
      let user_lc = EConstr.of_constr user_lc in
      (*Feedback.msg_debug (str "[codegen] user_lc:" ++ str (constr_name sigma user_lc) ++ str ":" ++ Printer.pr_econstr_env env sigma user_lc);
      Feedback.msg_debug (str "[codegen] params:" +++ pp_sjoinmap_ary (Printer.pr_econstr_env env sigma) params);*)
      let user_lc1 = prod_appvect sigma user_lc params in (* apply type parameters *)
      let user_lc = nf_all env sigma user_lc1 in (* apply type parameters *)
      (*Feedback.msg_debug (str "[codegen] user_lc2:" ++ str (constr_name sigma user_lc) ++ str ":" ++ Printer.pr_econstr_env env sigma user_lc);*)
      (if hasRel sigma user_lc then
        user_err (str "[codegen] is_linear_ind: constructor type has has local reference:" +++ Printer.pr_econstr_env env sigma user_lc));
      (* cparam_tys and body can be interpreted under env because they have no Rel *)
      let (cparam_names, cparam_tys, body) = destProdX sigma user_lc in
      (if not (eq_constr sigma body ty) then
        user_err (str "[codegen] unexpected constructor body type:" +++ Printer.pr_econstr_env env sigma body +++ str "(expected:" +++ Printer.pr_econstr_env env sigma ty ++ str ")"));
      (if Array.exists (isSort sigma) cparam_tys then
        user_err (str "[codegen] is_linear_ind: constructor has type argument"));
      let consarg_is_linear = Array.map (is_linear_type env sigma) cparam_tys in
      Array.mem true consarg_is_linear)
    oind_body.Declarations.mind_nf_lc in
  Array.mem true cons_is_linear

let is_linear (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : bool =
  (*Feedback.msg_debug (str "[codegen] is_linear:argument:" ++ Printer.pr_econstr_env env sigma ty);*)
  let sort = Retyping.get_type_of env sigma ty in
  if not (isSort sigma sort) then
    user_err (str "[codegen] not a type:" +++ Printer.pr_econstr_env env sigma ty +++ str ":" +++ Printer.pr_econstr_env env sigma sort);
  let ty2 = nf_all env sigma ty in
  is_linear_type env sigma ty2

let check_type_linearity (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.types) : unit =
  ignore (is_linear env sigma ty)

let rec ntimes n f v =
  if n = 0 then
    v
  else
    ntimes (n-1) f (f v)

let string_of_name (name : Names.Name.t) : string =
  match name with
  | Names.Name.Name id -> Names.Id.to_string id
  | Names.Name.Anonymous -> "_"

let with_local_var (env : Environ.env) (sigma : Evd.evar_map)
    (decl : EConstr.rel_declaration) (linear_vars : bool list)
    (numvars_innermost_function : int)
    (f : Environ.env -> bool list -> int -> int IntMap.t) : int IntMap.t =
  let env2 = EConstr.push_rel decl env in
  let name = Context.Rel.Declaration.get_name decl in
  let ty = Context.Rel.Declaration.get_type decl in
  let numvars_innermost_function2 = numvars_innermost_function+1 in
  if not (is_linear env sigma ty) then
    f env2 (false :: linear_vars) numvars_innermost_function2
  else
    (let count = f env2 (true :: linear_vars) numvars_innermost_function2 in
    let opt_n = IntMap.find_opt (Environ.nb_rel env) count in
    if opt_n <> Some 1 then
      user_err (Pp.str "[codegen] linear variable not lineary used:" +++ Names.Name.print name +++ Pp.str "(" ++ Pp.int (Stdlib.Option.value opt_n ~default:0) +++ Pp.str "times used)")
    else
      IntMap.remove (Environ.nb_rel env) count)

let merge_count (c1 : int IntMap.t) (c2 : int IntMap.t) : int IntMap.t =
  IntMap.merge
    (fun j n1 n2 -> Some (Stdlib.Option.value n1 ~default:0 + Stdlib.Option.value n2 ~default:0))
    c1 c2

let rec linearcheck_function (env : Environ.env) (sigma : Evd.evar_map) (linear_vars : bool list) (term : EConstr.t) : unit =
  let count = linearcheck_function_rec env sigma linear_vars 0 term in
  if IntMap.is_empty count then
    ()
  else
    user_err (Pp.str "[codegen] linear variable is referened by an inner function:" +++
      pp_sjoinmap_list
        (fun (j, _) -> Names.Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel (Environ.nb_rel env - j) env)))
        (IntMap.bindings count))
and linearcheck_function_rec (env : Environ.env) (sigma : Evd.evar_map) (linear_vars : bool list) (numvars_innermost_function : int) (term : EConstr.t) : int IntMap.t =
  ((*Feedback.msg_debug (str "[codegen] linearcheck_function:" +++ Printer.pr_econstr_env env sigma term);*)
  match EConstr.kind sigma term with
  | Lambda (name, ty, body) ->
      (check_type_linearity env sigma ty;
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      with_local_var env sigma decl linear_vars numvars_innermost_function
        (fun env2 linear_vars2 numvars_innermost_function2 -> linearcheck_function_rec env2 sigma linear_vars2 numvars_innermost_function2 body))
  | _ -> linearcheck_exp env sigma linear_vars numvars_innermost_function term 0)
and linearcheck_exp (env : Environ.env) (sigma : Evd.evar_map) (linear_vars : bool list) (numvars_innermost_function : int) (term : EConstr.t) (numargs : int) : int IntMap.t =
  ((*Feedback.msg_debug (str "[codegen] linearcheck_exp:" +++ Printer.pr_econstr_env env sigma term);*)
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _
  | Sort _ | Prod _ | Ind _
  | CoFix _ | Array _ ->
      user_err (Pp.str "[codegen:linearcheck_exp] unexpected " ++ Pp.str (constr_name sigma term) ++ Pp.str ":" +++ Printer.pr_econstr_env env sigma term)
  | Rel i ->
      if List.nth linear_vars (i-1) then
        IntMap.singleton (Environ.nb_rel env - i) 1
      else
        IntMap.empty
  | Cast (expr, kind, ty) ->
      (check_type_linearity env sigma ty;
      linearcheck_exp env sigma linear_vars numvars_innermost_function expr numargs)
  | Lambda (name, ty, body) ->
      if numargs <= 0 then
        (* closure creation found *)
        (linearcheck_function env sigma linear_vars term;
        IntMap.empty)
      else
	let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
	with_local_var env sigma decl linear_vars numvars_innermost_function
          (fun env2 linear_vars2 numvars_innermost_function2 -> linearcheck_exp env2 sigma linear_vars2 numvars_innermost_function2 body (numargs-1))
  | LetIn (name, expr, ty, body) ->
      (check_type_linearity env sigma ty;
      let count1 = linearcheck_exp env sigma linear_vars numvars_innermost_function expr 0 in
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let count2 = with_local_var env sigma decl linear_vars numvars_innermost_function
        (fun env2 linear_vars2 numvars_innermost_function2 -> linearcheck_exp env2 sigma linear_vars2 numvars_innermost_function2 body numargs) in
      merge_count count1 count2)
  | App (f, argsary) ->
      let count = linearcheck_exp env sigma linear_vars numvars_innermost_function f (Array.length argsary + numargs) in
      let counts = Array.map (fun arg -> linearcheck_exp env sigma linear_vars numvars_innermost_function arg 0) argsary in
      (* no partial application after argument completion? *)
      if Array.exists (fun arg -> let ty = Retyping.get_type_of env sigma arg in
                       is_linear env sigma ty) argsary &&
         isProd sigma (Retyping.get_type_of env sigma term) then
           user_err (str "[codegen] application with linear argument cannot return function value:" +++ Printer.pr_econstr_env env sigma term);
      Array.fold_left merge_count count counts
  | Const ctntu -> IntMap.empty
  | Construct cstru -> IntMap.empty
  | Case (ci, tyf, iv, expr, brs) ->
      ((* tyf is not checked because it is not a target of code generation.
          check tyf is (fun _ -> termty) ? *)
      let count0 = linearcheck_exp env sigma linear_vars numvars_innermost_function expr 0 in
      let chk_br cstr_nargs br = linearcheck_exp env sigma linear_vars numvars_innermost_function br (cstr_nargs + numargs) in
      let counts = Array.map2 chk_br ci.ci_cstr_nargs brs in
      Array.iter
        (fun c ->
          if not (IntMap.equal Int.equal c counts.(0)) then
            let pp_vars =
              List.filter_map
                (fun (j, b) ->
                  if b then
                    Some (Names.Name.print (Context.Rel.Declaration.get_name (Environ.lookup_rel (Environ.nb_rel env - j) env)))
                  else
                    None)
                (IntMap.bindings
                  (Array.fold_left
                    (fun bmap1 bmap2 ->
                      IntMap.merge
                        (fun j opt_b0 opt_b1 -> Some (Stdlib.Option.value opt_b0 ~default:false || Stdlib.Option.value opt_b1 ~default:false))
                        bmap1 bmap2)
                    IntMap.empty
                    (Array.map
                      (fun c ->
                        IntMap.merge
                          (fun j opt_n0 opt_n1 -> Some (Stdlib.Option.value opt_n0 ~default:0 <> Stdlib.Option.value opt_n1 ~default:0))
                          counts.(0) c)
                      counts)))
            in
            user_err (Pp.str "[codegen] inconsistent linear variable use in match branches:" +++ pp_sjoin_list pp_vars))
        counts;
      merge_count count0 counts.(0))
  | Fix ((ia, i), ((nameary, tyary, funary) as prec)) ->
      (let n = Array.length funary in
      let env2 = push_rec_types prec env in
      let linear_vars2 = ntimes n (List.cons false) linear_vars in
      Array.iter (check_type_linearity env sigma) tyary;
      (* Since fix-bounded funcitons can be evaluated 0 or more times,
        they cannot reference linear variables declared outside of the fix-expression. *)
      Array.iter (fun f -> linearcheck_function env2 sigma linear_vars2 f) funary;
      IntMap.empty)
  | Proj (proj, expr) ->
      linearcheck_exp env sigma linear_vars numvars_innermost_function expr 0
  | Int n -> IntMap.empty
  | Float n -> IntMap.empty)

let linear_type_check_term (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : unit =
  if not (ConstrMap.is_empty !type_linearity_map) then
    linearcheck_function env sigma [] term

let linear_type_check_single (libref : Libnames.qualid) : unit =
  let gref = Smartlocate.global_with_alias libref in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match gref with
  | ConstRef ctnt ->
      (let fctntu = Univ.in_punivs ctnt in
      let value_and_type = Environ.constant_value_and_type env fctntu in
      (match value_and_type with
      | (Some term, termty, uconstraints) ->
        let eterm = EConstr.of_constr term in
        linearcheck_function env sigma [] eterm;
        Feedback.msg_info (str "[codegen] linearity check passed:" +++ Printer.pr_constant env ctnt);
        ()
      | _ -> user_err (str "[codegen] constant value couldn't obtained:" ++ Printer.pr_constant env ctnt)))
      | _ -> user_err (str "[codegen] not constant")

let command_linear_check (libref_list : Libnames.qualid list) : unit =
  List.iter linear_type_check_single libref_list

let command_test_linear (t : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_constr_evars env sigma t in
  if is_linear env sigma t then
    Feedback.msg_info (str "linear type:" +++ Printer.pr_econstr_env env sigma t)
  else
    user_err (str "[codegen] unrestricted type:" +++ Printer.pr_econstr_env env sigma t)

let command_test_unrestricted (t : Constrexpr.constr_expr) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t) = Constrintern.interp_constr_evars env sigma t in
  if is_linear env sigma t then
    user_err (str "[codegen] linear type:" +++ Printer.pr_econstr_env env sigma t)
  else
    Feedback.msg_info (str "unrestricted type:" +++ Printer.pr_econstr_env env sigma t)

(* xxx test *)

let command_linear_test t1 t2 =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, t1a) = Constrintern.interp_constr_evars env sigma t1 in
  let (sigma, t2a) = Constrintern.interp_constr_evars env sigma t2 in
  Feedback.msg_debug (str "[codegen] linear_type_check_test t1:" +++ Printer.pr_econstr_env env sigma t1a);
  Feedback.msg_debug (str "[codegen] linear_type_check_test t2:" +++ Printer.pr_econstr_env env sigma t2a);
  Feedback.msg_debug (str "[codegen] linear_type_check_test is_conv:" +++ bool (Reductionops.is_conv env sigma t1a t2a));
  Feedback.msg_debug (str "[codegen] linear_type_check_test is_conv_leq:" +++ bool (Reductionops.is_conv_leq env sigma t1a t2a));
  (match Reductionops.infer_conv env sigma t1a t2a with
  | Some _ -> Feedback.msg_debug (str "[codegen] linear_type_check_test infer_conv succeed")
  | None -> Feedback.msg_debug (str "[codegen] linear_type_check_test infer_conv failed"));
  (match Reductionops.infer_conv ~pb:Reduction.CONV env sigma t1a t2a with
  | Some _ -> Feedback.msg_debug (str "[codegen] linear_type_check_test infer_conv(CONV) succeed")
  | None -> Feedback.msg_debug (str "[codegen] linear_type_check_test infer_conv(CONV) failed"))


