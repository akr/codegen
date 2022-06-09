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

let simplify_matchapp_once (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t option =
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
        Some (q (mkCase (ci, u, pms, (mpred_nas, mpred_body), iv, item, bl')))

let rec simplify_matchapp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  (if !opt_debug_matchapp then
    msg_debug_hov (Pp.str "[codegen] simplify_matchapp:" +++ Printer.pr_econstr_env env sigma term));
  match simplify_matchapp_once env sigma term with
  | None ->
      ((if !opt_debug_matchapp then
        msg_debug_hov (Pp.str "[codegen] simplify_matchapp: no matchapp redex"));
      term)
  | Some term' ->
      simplify_matchapp env sigma term'



