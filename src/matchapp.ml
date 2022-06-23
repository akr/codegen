(*
Copyright (C) 2022- National Institute of Advanced Industrial Science and Technology (AIST)

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

(*open Names*)
(*open GlobRef*)
open CErrors
open Constr
open EConstr

open Cgenutil
open State

open Proofview.Notations

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = Reductionops.nf_all env sigma term

(* term is S-normalized *)
let rec mkapp_simplify (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (args : EConstr.t array) : EConstr.t =
  match EConstr.kind sigma term with
  | Var _| Meta _ | Evar _ | Sort _ | Cast _ | Prod _ | Ind _
  | CoFix _ | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:mkapp_simplify] unsupported term:" +++ Printer.pr_econstr_env env sigma term)
  | Rel _ | Const _ | Construct _ | Proj _
  | App _ (* We cannot move args because term is S-normalized (beta-var and zeta-app cannot applied anymore.) *)
  | Fix _ | Case _ ->
      mkApp (term, args)
  | Lambda _ ->
      (* beta-var *)
      let na = Array.length args in
      let (fargs, body) = decompose_lam_upto_n env sigma na term in
      let nf = List.length fargs in
      if nf < na then
        let args1 = array_firstn nf args in
        let args2 = array_skipn nf args in
        let body' = Vars.substl (CArray.rev_to_list args1) body in
        mkapp_simplify env sigma body' args2
      else (* nf = na *)
        Vars.substl (CArray.rev_to_list args) body
  | LetIn (x,e,t,b) ->
      (* zeta-app *)
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let args' = Array.map (Vars.lift 1) args in
      let b' = mkapp_simplify env2 sigma b args' in
      mkLetIn (x,e,t,b')

(*
  term : V-normal form
*)
let rec find_match_app (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((EConstr.t -> EConstr.t) * Environ.env * EConstr.case * EConstr.t array) option =
  match EConstr.kind sigma term with
  | Var _| Meta _ | Evar _ | Sort _ | Cast _ | Prod _ | Ind _
  | CoFix _ | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:find_match_app] unsupported term:" +++ Printer.pr_econstr_env env sigma term)
  | Rel _ | Const _ | Construct _ | Proj _ -> None
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      (match int_find_i_map (fun i -> find_match_app env2 sigma fary.(i)) (Array.length fary) with
      | None -> None
      | Some (i, (q, ma_env, ma_match, ma_args)) ->
          let q' ma_term =
            let fary' = Array.copy fary in
            fary'.(i) <- q ma_term;
            mkFix ((ks, j), (nary, tary, fary'))
          in
          Some (q', ma_env, ma_match, ma_args))
  | App (f, rels) ->
      (match EConstr.kind sigma f with
      | Case (ci, u, pms, mpred, iv, item, bl) ->
          let ma_match = (ci, u, pms, mpred, iv, item, bl) in
          Some ((fun ma_term -> ma_term), env, ma_match, rels)
      | _ ->
          match find_match_app env sigma f with
          | None -> None
          | Some (q, ma_env, ma_match, ma_args) ->
              let q' ma_term = mkApp (q ma_term, rels) in
              Some (q', ma_env, ma_match, ma_args))
  | Lambda (x,t,e) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      (match find_match_app env2 sigma e with
      | None -> None
      | Some (q, ma_env, ma_match, ma_args) ->
          let q' ma_term = mkLambda (x, t, q ma_term) in
          Some (q', ma_env, ma_match, ma_args))
  | LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      (match find_match_app env sigma e with
      | Some (q, ma_env, ma_match, ma_args) ->
          let q' ma_term = mkLetIn (x, q ma_term, t, b) in
          Some (q', ma_env, ma_match, ma_args)
      | None ->
          match find_match_app env2 sigma b with
          | Some (q, ma_env, ma_match, ma_args) ->
              let q' ma_term = mkLetIn (x, e, t, q ma_term) in
              Some (q', ma_env, ma_match, ma_args)
          | None -> None)
  | Case (ci, u, pms, mpred, iv, item, bl) ->
      let (_, _, _, _, _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, mpred, iv, item, bl) in
      (match int_find_i_map
              (fun i ->
                let (nas, body) = bl.(i) in
                let (ctx, _) = bl0.(i) in
                let env2 = EConstr.push_rel_context ctx env in
                find_match_app env2 sigma body)
              (Array.length bl) with
      | None -> None
      | Some (i, (q, ma_env, ma_match, ma_args)) ->
          let q' ma_term =
            let bl' = Array.copy bl in
            let (nas, _) = bl'.(i) in
            bl'.(i) <- (nas, q ma_term);
            mkCase (ci, u, pms, mpred, iv, item, bl')
          in
          Some (q', ma_env, ma_match, ma_args))

(*
let rec nf_delta (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  match EConstr.kind sigma term with
  | Rel i ->
      (match EConstr.lookup_rel i env with
      | Context.Rel.Declaration.LocalAssum (x, t) ->
          term
      | Context.Rel.Declaration.LocalDef (x, e, t) ->
          nf_delta env sigma (Vars.lift i e))
  | _ ->
      Termops.map_constr_with_full_binders env sigma push_rel
        (fun env2 term2 -> nf_delta env2 sigma term2)
        env term
*)

let expand_local_definitions (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:expand_local_definitions] env rel=[" ++
    pp_sjoinmap_ary
      (fun i -> Pp.str "(" ++ Printer.pr_rel_decl (Environ.pop_rel_context i env) sigma (Environ.lookup_rel i env) ++ Pp.str ")")
      (iota_ary 1 (Environ.nb_rel env)) ++
    Pp.str "]"));*)
  let rec aux n t =
    (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:expand_local_definitions]" +++
      Pp.str "n=" ++ Pp.int n +++
      Pp.str "term=" ++ pr_raw_econstr sigma t));*)
    let res =
    match EConstr.kind sigma t with
    | Rel i ->
        if i <= n then
          t
        else
          (match EConstr.lookup_rel (i-n) env with
          | Context.Rel.Declaration.LocalAssum (x, ty) ->
              t
          | Context.Rel.Declaration.LocalDef (x, e, ty) ->
              aux n (Vars.lift (n+i) e))
    | _ ->
        Termops.map_constr_with_full_binders env sigma
          (fun _ -> succ) aux n t
    in
    (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:expand_local_definitions]" +++
      Pp.str "result=" ++ pr_raw_econstr sigma res));*)
    res
  in
  let result = aux 0 term in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:expand_local_definitions]" +++ Pp.str "result=" ++ pr_raw_econstr sigma result));*)
  result

(*
  iary : An array of de Bruijn's indexes for free variables of the term
         This array must be sorted in descending order.
*)
let abstract_free_variables (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (iary : int array) : EConstr.t =
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:abstract_free_variables] env rel=[" ++
    pp_sjoinmap_ary
      (fun i -> Pp.hov 2 (Pp.int i ++ Pp.str ":(" ++ Printer.pr_rel_decl (Environ.pop_rel_context i env) sigma (Environ.lookup_rel i env) ++ Pp.str ")"))
      (array_rev (iota_ary 1 (Environ.nb_rel env))) ++
    Pp.str "]"));
  Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:abstract_free_variables]" +++ Pp.str "term=" ++ pr_raw_econstr sigma term));
  Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:abstract_free_variables]" +++ Pp.str "iary=[" ++ pp_sjoinmap_ary Pp.int iary ++ Pp.str "]"));*)
  if CArray.is_empty iary then
    term
  else
    let nvars = Array.length iary in
    (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:abstract_free_variables]" +++ Pp.str "nvars=" ++ Pp.int nvars));*)
    let imax = iary.(0) in (* iary.(0) is the maximum of iary because it is sorted in descending order. *)
    (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:abstract_free_variables]" +++ Pp.str "imax=" ++ Pp.int imax));*)
    let sub = Array.make imax (nvars+1) in (* nvars+1 is a dummy value which can be distinguished with 1..nvars. *)
    Array.iteri
      (fun j i ->
        (*
          - j=0 and i=imax means the outermost variable in iary.
            It should be translated to (Rel nvars).
          - j=nvars-1 and i=imin means the innermost variable in iary.
            It should be translated to (Rel 1).
            (imin is the minimum value of iary)
        *)
        sub.(i-1) <- nvars-j)
      iary;
    (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:abstract_free_variables]" +++ Pp.str "sub=[" ++ pp_sjoinmap_ary Pp.int sub ++ Pp.str "]"));*)
    let sub = CArray.map_to_list mkRel sub in
    let body = Vars.substl sub term in
    (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:abstract_free_variables]" +++ Pp.str "body=" ++ pr_raw_econstr sigma body));*)
    Array.fold_right
      (fun i body2 ->
        match EConstr.lookup_rel i env with
        | Context.Rel.Declaration.LocalAssum (x, t) ->
            if Vars.closed0 sigma t then
              mkLambda (x, t, body2)
            else
              user_err (Pp.str "[codegen] dependent type not supported:" +++
                        Printer.pr_econstr_env env sigma (mkRel i) +++
                        Pp.str ":" +++
                        Printer.pr_econstr_env (Environ.pop_rel_context i env) sigma t)
        | Context.Rel.Declaration.LocalDef (x, e, t) ->
            user_err (Pp.str "[codegen] local definition found:" +++
                      Printer.pr_econstr_env env sigma (mkRel i) +++
                      Pp.str ":" +++
                      Printer.pr_econstr_env (Environ.pop_rel_context i env) sigma t))
      iary body

(*
  env: environment for item, lhs_appmatch, and rhs_matchapp. (not for (q _))
*)
let replace_appmatch (env : Environ.env) (sigma : Evd.evar_map) (ty0 : EConstr.types) (q : EConstr.t -> EConstr.t) (lhs_fun : EConstr.t) (rhs_fun : EConstr.t) (fv_args : EConstr.t array) : unit Proofview.tactic =
  let eq_ind = mkConst (Globnames.destConstRef (Coqlib.lib_ref "core.eq.ind")) in
  let eq = mkInd (Globnames.destIndRef (Coqlib.lib_ref "core.eq.type")) in
  (* eq_ind : forall [A : Type] (x : A) (P : A -> Prop), P x -> forall y : A, x = y -> P y *)
  (* eq_ind fun_ty lhs_fun (fun z => q (lhs_fun fv_args) = q (z fv_args)) _ rhs_fun _ *)
  (* x = lhs_fun *)
  (* y = rhs_fun *)
  let fun_ty = Retyping.get_type_of env sigma lhs_fun in
  let p = mkLambda (Context.anonR, fun_ty, mkApp (eq, [| ty0; q (mkApp (lhs_fun, fv_args)); q (mkApp (mkRel (Environ.nb_rel env + 1), fv_args)) |])) in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    Refine.refine ~typecheck:true begin fun sigma ->
      let sigma, px = Evarutil.new_evar env sigma (mkApp (p, [| lhs_fun |])) in
      let sigma, g = Evarutil.new_evar env sigma (mkApp (eq, [| fun_ty; lhs_fun; rhs_fun |])) in
      let r = mkApp (eq_ind, [| fun_ty; lhs_fun; p; px; rhs_fun; g |]) in
      (sigma, r)
    end
  end

(*
  env: environment for item, lhs_appmatch, and rhs_matchapp. (not for (q _))

  q : context around lhs_appmatch and rhs_matchapp.
  lhs_appmatch : match item with ... end args
  rhs_matchapp : match item with ... | C vars => (...) args | ... end

  This function verifies
  (q lhs_appmatch) = (q rhs_matchapp).
*)
let verify_case_transform (env : Environ.env) (sigma : Evd.evar_map) (q : EConstr.t -> EConstr.t) (lhs_appmatch : EConstr.t) (rhs_matchapp : EConstr.t) : Evd.evar_map * EConstr.t =
  let c_eq = mkInd (Globnames.destIndRef (Coqlib.lib_ref "core.eq.type")) in
  let c_functional_extensionality = mkConst (Globnames.destConstRef (Coqlib.lib_ref "codegen.functional_extensionality")) in
  let lhs_term = q lhs_appmatch in
  let rhs_term = q rhs_matchapp in
  let eq_ty = Retyping.get_type_of env sigma lhs_term in
  let eq0 = mkApp (c_eq, [| eq_ty; lhs_term; rhs_term |]) in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] lhs_appmatch:" +++ Printer.pr_econstr_env env sigma lhs_appmatch));*)
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] rhs_matchapp:" +++ Printer.pr_econstr_env env sigma rhs_matchapp));*)
  let lhs_appmatch' = expand_local_definitions env sigma lhs_appmatch in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] lhs_appmatch':" +++ Printer.pr_econstr_env env sigma lhs_appmatch'));*)
  let rhs_matchapp' = expand_local_definitions env sigma rhs_matchapp in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] rhs_matchapp':" +++ Printer.pr_econstr_env env sigma rhs_matchapp'));*)
  let lhs_fv = free_variables_index_set env sigma lhs_appmatch' in
  let rhs_fv = free_variables_index_set env sigma rhs_matchapp' in
  let fv = IntSet.union lhs_fv rhs_fv in
  let fv_ary = CArray.rev_of_list (IntSet.elements fv) in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform]" +++ Pp.str "fv=[" ++ pp_sjoinmap_ary Pp.int fv_ary ++ Pp.str "]"));*)
  let lhs_fun = abstract_free_variables env sigma lhs_appmatch' fv_ary in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] lhs_fun:" +++ Printer.pr_econstr_env env sigma lhs_fun));*)
  if not (Vars.closed0 sigma lhs_fun) then user_err (Pp.hov 2 (Pp.str "[codegen:bug] lhs_fun couldn't closed:" +++
     Pp.str "lhs_appmatch2=" ++ pr_raw_econstr sigma lhs_appmatch' +++
     Pp.str "lhs_fun=" ++ pr_raw_econstr sigma lhs_fun));
  let rhs_fun = abstract_free_variables env sigma rhs_matchapp' fv_ary in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] rhs_fun:" +++ Printer.pr_econstr_env env sigma rhs_fun));*)
  if not (Vars.closed0 sigma rhs_fun) then user_err (Pp.str "[codegen:bug] rhs_fun couldn't closed");
  let fv_args = Array.map mkRel fv_ary in
  let lhs_app = mkApp (lhs_fun, fv_args) in
  let rhs_app = mkApp (rhs_fun, fv_args) in
  check_convertible "case_transform_lhs" env sigma lhs_appmatch lhs_app;
  check_convertible "case_transform_rhs" env sigma rhs_matchapp rhs_app;
  let lhs_term' = q lhs_app in
  let rhs_term' = q rhs_app in
  let eq1 = mkApp (c_eq, [| eq_ty; lhs_term'; rhs_term' |]) in
  let genv = Global.env () in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] eq0:" +++ Printer.pr_econstr_env genv sigma eq0));
  Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] eq1:" +++ Printer.pr_econstr_env genv sigma eq1));*)
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] eq_term1_term2_type:" +++ Printer.pr_econstr_env genv sigma (Retyping.get_type_of genv sigma eq_term1_term2)));
  Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:verify_case_transform] eq_term1_term2_type:" +++ Printer.pr_econstr_env genv sigma (snd (Typing.type_of genv sigma eq_term1_term2))));*)
  let (entry, pv) = Proofview.init sigma [(genv, eq0)] in
  let ((), pv, unsafe, tree) =
    Proofview.apply
      ~name:(Names.Id.of_string "codegen")
      ~poly:false
      env
      (
        Tactics.change_concl eq1 <*>
        replace_appmatch env sigma eq_ty q lhs_fun rhs_fun fv_args <*>
        (*Equality.replace rhs_fun lhs_fun <*>*)
        Proofview.tclDISPATCH [Tactics.reflexivity; Proofview.tclUNIT ()] <*>
        Tacticals.tclDO (Array.length fv_ary)
          (Tactics.apply c_functional_extensionality <*>
           Tactics.intro) <*>
        Proofview.Goal.enter begin fun g ->
          let sigma = Proofview.Goal.sigma g in
          let eq_matchapp = Proofview.Goal.concl g in
          (*Feedback.msg_info (Pp.hov 2 (Pp.str "[codegen]" +++ Pp.str "goal=" ++ (Printer.pr_econstr_env env sigma eq_matchapp)));*)
          let (ci, u, pms, mpred, iv, item, bl) =
            destCase sigma (snd (destApp sigma eq_matchapp)).(2)
          in
          Tactics.simplest_case item <*>
          Tactics.reflexivity
        end
      )
      pv
  in
  let sigma = Proofview.return pv in
  let proofs = Proofview.partial_proof entry pv in
  assert (List.length proofs = 1);
  (*List.iter
    (fun c ->
      Feedback.msg_info (Pp.hov 2 (Pp.str "[codegen]" +++ Pp.str "proofterm=" ++ (Printer.pr_econstr_env env sigma c))))
    proofs;*)
  (sigma, List.hd proofs)

let simplify_matchapp_once (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (Evd.evar_map * EConstr.t * EConstr.t) option =
  match find_match_app env sigma term with
  | None -> None
  | Some (q, env, ma_match, ma_args) ->
      let (ci, u, pms, ((mpred_nas, mpred_body) as mpred), iv, item, bl) = ma_match in
      let (_, _, _, (mpred_ctx, _), _, _, bl0) = EConstr.annotate_case env sigma ma_match in
      let rec decompose_prod_n_acc env fargs n term =
        let term = whd_all env sigma term in
        if n <= 0 then
          (fargs, term)
        else
          match EConstr.kind sigma term with
          | Prod (x,t,e) ->
              let t' = nf_all env sigma t in
              let decl = Context.Rel.Declaration.LocalAssum (x, t) in
              let env2 = EConstr.push_rel decl env in
              decompose_prod_n_acc env2 ((x,t')::fargs) (n-1) e
          | _ ->
              user_err (Pp.str "[codegen] could not move arg of (match ... end arg) because dependent-match (prod not exposed):" +++
                        Printer.pr_econstr_env env sigma term)
      in
      let na = Array.length ma_args in
      let (mpred_fargs, mpred_body) = decompose_prod_n_acc env [] na mpred_body in
      if List.exists (fun (x,t) -> not (Vars.closed0 sigma t)) mpred_fargs then
        user_err (Pp.str "[codegen] could not move arg of (match ... end arg) because dependent-match (dependent argument):" +++
                  Printer.pr_econstr_env env sigma term)
      else
        let mpred_body =
          let n = List.length mpred_ctx in
          let ma_args = Array.map (Vars.lift n) ma_args in
          Vars.substl (CArray.rev_to_list ma_args) mpred_body
        in
        let bl' =
          Array.map2
            (fun (nas,body) (ctx,_) ->
              let env2 = EConstr.push_rel_context ctx env in
              let nctx = List.length ctx in
              let args = Array.map (Vars.lift nctx) ma_args in
              let body = mkapp_simplify env2 sigma body args in
              (nas, body))
            bl bl0
        in
        let lhs_appmatch = mkApp (mkCase ma_match, ma_args) in
        let rhs_matchapp = mkCase (ci, u, pms, (mpred_nas, mpred_body), iv, item, bl') in
        let (sigma, proof) = verify_case_transform env sigma q lhs_appmatch rhs_matchapp in
        Some (sigma, q rhs_matchapp, proof)

let simplify_matchapp (env : Environ.env) (sigma : Evd.evar_map) (term0 : EConstr.t) : Evd.evar_map * EConstr.t * EConstr.t =
  let ty_term0 = Retyping.get_type_of env sigma term0 in
  let eq = mkInd (Globnames.destIndRef (Coqlib.lib_ref "core.eq.type")) in
  let eq_refl = mkConstruct (Globnames.destConstructRef (Coqlib.lib_ref "core.eq.refl")) in
  let rec aux sigma term proof0 =
    (if !opt_debug_matchapp then
      msg_debug_hov (Pp.str "[codegen] simplify_matchapp:" +++ Printer.pr_econstr_env env sigma term));
    match simplify_matchapp_once env sigma term with
    | None ->
        ((if !opt_debug_matchapp then
          msg_debug_hov (Pp.str "[codegen] simplify_matchapp: no matchapp redex"));
        (sigma, term, proof0))
    | Some (sigma, term', proof_eq_term_term') ->
        let (entry, pv) = Proofview.init sigma [(env, mkApp (eq, [|ty_term0; term0; term'|]))] in
        let ((), pv, unsafe, tree) =
          Proofview.apply
            ~name:(Names.Id.of_string "codegen")
            ~poly:false
            env
            (
              Equality.rewriteRL proof_eq_term_term' <*>
              Tactics.exact_no_check proof0 <*>
              Tactics.reflexivity
            )
            pv
        in
        let sigma = Proofview.return pv in
        let proofs = Proofview.partial_proof entry pv in
        assert (List.length proofs = 1);
        aux sigma term' (List.hd proofs)
  in
  let proof0 = mkApp (eq_refl, [| ty_term0; term0 |]) in
  aux sigma term0 proof0

