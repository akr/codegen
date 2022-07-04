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

open Names
(*open GlobRef*)
open CErrors
open Constr
open EConstr

open Cgenutil
open State

open Proofview.Notations

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = Reductionops.nf_all env sigma term

(*
  term : V-normal form
*)
let rec find_match_app (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((EConstr.t -> EConstr.t) * Environ.env * EConstr.case * EConstr.t array) option =
  match EConstr.kind sigma term with
  | Var _| Meta _ | Evar _ | Cast _
  | CoFix _ | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:find_match_app] unsupported term:" +++ Printer.pr_econstr_env env sigma term)
  | Sort _ | Prod _ | Ind _
  | Rel _ | Const _ | Construct _ | Proj _ ->
      None
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
  namemap : map from de Bruijn's level to id
*)
let term_rel_to_named (env : Environ.env) (sigma : Evd.evar_map) (namemap : Id.t Int.Map.t) (term : EConstr.t) : EConstr.t =
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:term_rel_to_named] term:" +++ pr_raw_econstr sigma term));*)
  let rec aux n t =
    match EConstr.kind sigma t with
    | Rel i ->
        if i <= n then
          t
        else
          mkVar (Int.Map.find (Environ.nb_rel env - (i - n)) namemap)
    | _ ->
        Termops.map_constr_with_full_binders env sigma
            (fun _ -> succ) aux n t
  in
  let result = aux 0 term in
  (*Feedback.msg_debug (Pp.hov 2 (Pp.str "[codegen:term_rel_to_named] result:" +++ pr_raw_econstr sigma result));*)
  result

let env_rel_to_named (env : Environ.env) (sigma : Evd.evar_map) : (Environ.env * Id.t Int.Map.t) =
  let avoid = ref (Environ.ids_of_named_context_val (Environ.named_context_val env)) in
  let namemap = ref Int.Map.empty in (* map from de Bruijn's level to id *)
  let n = Environ.nb_rel env in
  let env2 = ref (Environ.pop_rel_context n env) in
  for i = Environ.nb_rel env downto 1 do
    let rel_decl = EConstr.lookup_rel i env in
    let id = Namegen.next_name_away (Context.Rel.Declaration.get_name rel_decl) !avoid in
    avoid := Id.Set.add id !avoid;
    let env1 = Environ.pop_rel_context i env in
    let named_decl =
      (match rel_decl with
      | Context.Rel.Declaration.LocalAssum (x,t) ->
          Context.Named.Declaration.LocalAssum ((Context.map_annot (fun _ -> id) x),
                                                term_rel_to_named env1 sigma !namemap t)
      | Context.Rel.Declaration.LocalDef (x,e,t) ->
          Context.Named.Declaration.LocalDef ((Context.map_annot (fun _ -> id) x),
                                              term_rel_to_named env1 sigma !namemap e,
                                              term_rel_to_named env1 sigma !namemap t))
    in
    env2 := EConstr.push_named named_decl !env2;
    namemap := Int.Map.add (n - i) id !namemap
  done;
  (!env2, !namemap)

(*
  env: environment for lhs_appmatch and rhs_matchapp.
  lhs_appmatch : match item with ... end args
  rhs_matchapp : match item with ... | C vars => (...) args | ... end

  This function verifies: lhs_appmatch = rhs_matchapp
*)
let verify_case_transform (env : Environ.env) (sigma : Evd.evar_map) (lhs_appmatch : EConstr.t) (rhs_matchapp : EConstr.t) : Evd.evar_map =
  let eq = lib_ref "core.eq.type" in
  let eq_ty = Retyping.get_type_of env sigma lhs_appmatch in
  let eq_goal = mkApp (eq, [| eq_ty; lhs_appmatch; rhs_matchapp |]) in
  let (proof_env, namemap) = env_rel_to_named env sigma in
  let proof_goal = term_rel_to_named env sigma namemap eq_goal in
  let (entry, pv) = Proofview.init sigma [(proof_env, proof_goal)] in
  let ((), pv, unsafe, tree) =
    Proofview.apply
      ~name:(Names.Id.of_string "codegen")
      ~poly:false
      proof_env
      (
        (*show_goals () <*>*)
        Proofview.Goal.enter begin fun g ->
          let sigma = Proofview.Goal.sigma g in
          let eq_matchapp = Proofview.Goal.concl g in
          let (ci, u, pms, mpred, iv, item, bl) =
            destCase sigma (snd (destApp sigma eq_matchapp)).(2)
          in
          (*show_goals () <*>*)
          Tactics.simplest_case item <*>
          (*show_goals () <*>*)
          Tactics.intros <*>
          (*show_goals () <*>*)
          Tactics.reflexivity
        end
      )
      pv
  in
  if not (Proofview.finished pv) then
    user_err (Pp.str "[codegen] could not prove matchapp equality:" +++
      Printer.pr_econstr_env env sigma eq_goal);
  let sigma = Proofview.return pv in
  let proofs = Proofview.partial_proof entry pv in
  assert (List.length proofs = 1);
  let proof = List.hd proofs in
  (* Feedback.msg_info (Pp.hov 2 (Pp.str "[codegen]" +++ Pp.str "proofterm=" ++ (Printer.pr_econstr_env env sigma proof))); *)
  if Evarutil.has_undefined_evars sigma proof then
    user_err (Pp.str "[codegen] could not prove matchapp equality (evar remains):" +++
      Printer.pr_econstr_env env sigma eq_goal);
  let (sigma, ty) = Typing.type_of proof_env sigma proof in (* verify proof term *)
  sigma

let simplify_matchapp_once (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (Evd.evar_map * EConstr.t) option =
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
              let nctx = List.length ctx in
              let args = Array.map (Vars.lift nctx) ma_args in
              let body = mkApp (body,args) in
              (nas, body))
            bl bl0
        in
        let lhs_appmatch = mkApp (mkCase ma_match, ma_args) in
        let rhs_matchapp = mkCase (ci, u, pms, (mpred_nas, mpred_body), iv, item, bl') in
        let sigma = verify_case_transform env sigma lhs_appmatch rhs_matchapp in
        Some (sigma, q rhs_matchapp)

(*
  (sigma, term') = simplify_matchapp env sigma term

  - proofs is a list of equality proofs from term to term'
    If term is repeatedly rewritten to term' as
    term=term1 -> term2 -> ... -> termN=term',
    the first element of proofs is the tuple of (term{N-1}, termN, the proof of term{N-1} = termN), and
    the last element of proofs is the tuple of (term1, term2, the proof of term1 = term2).
*)
let simplify_matchapp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Evd.evar_map * EConstr.t =
  let rec aux sigma term =
    (if !opt_debug_matchapp then
      msg_debug_hov (Pp.str "[codegen] simplify_matchapp:" +++ Printer.pr_econstr_env env sigma term));
    match simplify_matchapp_once env sigma term with
    | None ->
        ((if !opt_debug_matchapp then
          msg_debug_hov (Pp.str "[codegen] simplify_matchapp: no matchapp redex"));
        (sigma, term))
    | Some (sigma, term') ->
        aux sigma term'
  in
  aux sigma term

