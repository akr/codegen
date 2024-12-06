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

open Ltac2_plugin
open Tac2expr
open Tac2interp
open Tac2val
open Tac2core

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = Reductionops.nf_all env sigma term

let codegen_solve () : unit Proofview.tactic =
  let gr = Coqlib.lib_ref "codegen.verification_anchor" in
  let cnst =
    match gr with
    | ConstRef cnst -> cnst
    | _ -> user_err (Pp.str "[codegen:matchapp] codegen.verification_anchor not found")
  in
  let modpath = KerName.modpath (Constant.canonical cnst) in
  let kn = KerName.make modpath (Label.make "codegen_solve0") in
  (*msg_debug_hov (Pp.str "[codegen] kn=" ++ KerName.debug_print kn);*)
  let glb_tacexpr = GTacRef kn in
  let valexpr = interp_value empty_environment glb_tacexpr in
  let clo = to_closure valexpr in
  let tac = apply clo [Core.v_unit] in
  Proofview.tclIGNORE tac

type verification_step = {
  vstep_lhs_fun : EConstr.t;
  vstep_rhs_fun : EConstr.t;
  vstep_goal : EConstr.types;
  vstep_proof : EConstr.t;
}

let verify_transformation (env : Environ.env) (sigma : Evd.evar_map) (lhs_fun : EConstr.t) (rhs_fun : EConstr.t) : (Evd.evar_map * verification_step) =
  let sigma, eq = lib_ref env sigma "core.eq.type" in
  let ty = nf_all env sigma (Retyping.get_type_of env sigma lhs_fun) in
  let (ctx, ret_ty) = decompose_prod sigma ty in
  let nargs = List.length ctx in
  let args = mkRels_dec nargs nargs in
  let lhs' = mkApp_beta sigma lhs_fun args in
  let rhs' = mkApp_beta sigma rhs_fun args in
  let equal = mkApp (eq, [| ret_ty; lhs'; rhs' |]) in
  let goal = compose_prod ctx equal in
  let (entry, pv) = Proofview.init sigma [(env, goal)] in
  let ((), pv, unsafe, tree) =
    Proofview.apply
      ~name:(Names.Id.of_string "codegen")
      ~poly:false
      env
      (
        (* show_goals () <*> *)
        codegen_solve ()
      )
      pv
  in
  if not (Proofview.finished pv) then
    user_err (Pp.str "[codegen] could not prove matchapp equality:" +++
      Printer.pr_econstr_env env sigma goal);
  let sigma = Proofview.return pv in
  let proofs = Proofview.partial_proof entry pv in
  assert (List.length proofs = 1);
  let proof = List.hd proofs in
  (* Feedback.msg_info (Pp.hov 2 (Pp.str "[codegen]" +++ Pp.str "proofterm=" ++ (Printer.pr_econstr_env env sigma proof))); *)
  if Evarutil.has_undefined_evars sigma proof then
    user_err (Pp.str "[codegen] could not prove matchapp equality (evar remains):" +++
      Printer.pr_econstr_env env sigma goal);
  let (sigma, ty) = Typing.type_of env sigma (mkCast (proof, DEFAULTcast, goal)) in (* verify proof term *)
  (sigma, { vstep_lhs_fun=lhs_fun; vstep_rhs_fun=rhs_fun; vstep_goal=ty; vstep_proof=proof })

let combine_verification_steps (env : Environ.env) (sigma: Evd.evar_map) (first_term : EConstr.t) (rev_steps : verification_step list) (last_term : EConstr.t) : Evd.evar_map * EConstr.types * EConstr.t =
  (*
  List.iteri
    (fun i (lhs_fun, rhs_fun, prop, proof) ->
      msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] [" ++ Pp.int i ++ Pp.str "] lhs_fun=" +++ Printer.pr_econstr_env env sigma lhs_fun);
      msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] [" ++ Pp.int i ++ Pp.str "] rhs_fun=" +++ Printer.pr_econstr_env env sigma rhs_fun);
      msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] [" ++ Pp.int i ++ Pp.str "] prop=" +++ Printer.pr_econstr_env env sigma prop);
      msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] [" ++ Pp.int i ++ Pp.str "] proof=" +++ Printer.pr_econstr_env env sigma proof))
    rev_steps;
  *)
  let (sigma, eq) = lib_ref env sigma "core.eq.type" in (* forall {A : Type}, A -> A -> Prop *)
  let (sigma, eq_refl) = lib_ref env sigma "core.eq.refl" in (* forall {A : Type} {x : A}, x = x *)
  let (sigma, eq_trans) = lib_ref env sigma "core.eq.trans" in (* forall [A : Type] [x y z : A], x = y -> y = z -> x = z *)
  let whole_type = nf_all env sigma (Retyping.get_type_of env sigma first_term) in
  let (prod_ctx, val_type) = decompose_prod sigma whole_type in
  let nargs = List.length prod_ctx in
  let args = mkRels_dec nargs nargs in
  let eq_prop = compose_prod prod_ctx (mkApp (eq, [| val_type; mkApp (first_term, args); mkApp (last_term, args) |])) in
  let eq_proof =
    match rev_steps with
    | [] ->
        let eq_proof = it_mkLambda (mkApp (eq_refl, [| val_type; mkApp (last_term, args) |])) prod_ctx in
        eq_proof
    | { vstep_proof=step_proof } :: [] ->
        step_proof
    | { vstep_lhs_fun=last_step_lhs_fun; vstep_rhs_fun=last_step_rhs_fun; vstep_goal=last_step_prop; vstep_proof=last_step_proof } :: rest ->
        let proof = List.fold_left
          (fun acc_proof { vstep_lhs_fun=prev_lhs_fun; vstep_rhs_fun=prev_rhs_fun; vstep_goal=prev_prop; vstep_proof=prev_proof } ->
            mkApp (eq_trans, [| val_type; mkApp (prev_lhs_fun, args); mkApp (prev_rhs_fun, args); mkApp (last_term, args); mkApp (prev_proof, args); acc_proof |]))
          (mkApp (last_step_proof, args))
          rest
        in
        it_mkLambda proof prod_ctx
  in
  (*msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] eq_prop=" ++ Printer.pr_econstr_env env sigma eq_prop);
  msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] eq_proof=" ++ Printer.pr_econstr_env env sigma eq_proof);*)
  (sigma, eq_prop, eq_proof)


(*
  term : V-normal form
*)
let rec find_match_app (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : ((EConstr.t -> EConstr.t) * Environ.env * EConstr.case * EConstr.t array) option =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Evar _ | CoFix _ | Array _ | Int _ | Float _ | String _ ->
       user_err (Pp.str "[codegen:find_match_app] unsupported term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
  | Cast _ ->
      user_err (Pp.str "[codegen:find_match_app] unexpected term (" ++ Pp.str (constr_name sigma term) ++ Pp.str "):" +++ Printer.pr_econstr_env env sigma term)
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
      let env2 = env_push_assum env x t in
      (match find_match_app env2 sigma e with
      | None -> None
      | Some (q, ma_env, ma_match, ma_args) ->
          let q' ma_term = mkLambda (x, t, q ma_term) in
          Some (q', ma_env, ma_match, ma_args))
  | LetIn (x,e,t,b) ->
      let env2 = env_push_assum env x t in
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

let simplify_matchapp_once (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (Evd.evar_map * verification_step) option =
  match find_match_app env sigma term with
  | None -> None
  | Some (q, env, ma_match, ma_args) ->
      let (ci, u, pms, ((mpred_nas, mpred_body) as mpred, sr), iv, item, bl) = ma_match in
      let (_, _, _, ((mpred_ctx, _), _), _, _, bl0) = EConstr.annotate_case env sigma ma_match in
      let rec decompose_prod_n_acc env fargs n term =
        let term = whd_all env sigma term in
        if n <= 0 then
          (fargs, term)
        else
          match EConstr.kind sigma term with
          | Prod (x,t,e) ->
              let t' = nf_all env sigma t in
              let env2 = env_push_assum env x t in
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
        let mpred_sr = EConstr.ERelevance.relevant in
        let rhs_matchapp = mkCase (ci, u, pms, ((mpred_nas, mpred_body), mpred_sr), iv, item, bl') in
        let transformed_term = q rhs_matchapp in
        let (sigma, step) = verify_transformation env sigma term transformed_term in
        Some (sigma, step)

(*
  (sigma, term') = simplify_matchapp env sigma term

  - proofs is a list of equality proofs from term to term'
    If term is repeatedly rewritten to term' as
    term=term1 -> term2 -> ... -> termN=term',
    the first element of proofs is the tuple of (term{N-1}, termN, the proof of term{N-1} = termN), and
    the last element of proofs is the tuple of (term1, term2, the proof of term1 = term2).
*)
let simplify_matchapp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : Evd.evar_map * EConstr.t * verification_step list =
  let rec aux sigma term rev_steps =
    (if !opt_debug_matchapp then
      msg_debug_hov (Pp.str "[codegen] simplify_matchapp:" +++ Printer.pr_econstr_env env sigma term));
    match simplify_matchapp_once env sigma term with
    | None ->
        ((if !opt_debug_matchapp then
          msg_debug_hov (Pp.str "[codegen] simplify_matchapp: no matchapp redex"));
        (sigma, term, rev_steps))
    | Some (sigma, ({vstep_rhs_fun=term'} as step)) ->
        aux sigma term' (step :: rev_steps)
  in
  aux sigma term []
