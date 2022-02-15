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

let whd_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = EConstr.of_constr (Reduction.whd_all env (EConstr.to_constr sigma term))
let nf_all (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t = Reductionops.nf_all env sigma term

let rels_of_levels (env : Environ.env) (args : int list) =
  List.map
    (fun l -> mkRel (Environ.nb_rel env - l))
    args

(*
  term : V-normal form
  args : arguments represented as list of de de Bruijn levels
*)
let rec simplify_matchapp_rec (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (args : int list) : EConstr.t =
  (*Feedback.msg_debug (Pp.hv 2 (Pp.str "[codegen:simplify_matchapp_rec] start" +++
    Pp.hv 2 (Pp.str "term=" ++ Printer.pr_econstr_env env sigma term) +++
    Pp.hv 2 (Pp.str "args=[" ++ pp_sjoinmap_list (fun l -> Pp.str (str_of_name_permissive (Context.Rel.Declaration.get_name (Environ.lookup_rel (Environ.nb_rel env - l) env)))) args ++ Pp.str "]")));*)
  let ret = simplify_matchapp_rec1 env sigma term args in
  (*Feedback.msg_debug (Pp.hv 2 (Pp.str "[codegen:simplify_matchapp_rec] return" +++
    Pp.hv 2 (Pp.str "term=" ++ Printer.pr_econstr_env env sigma term) +++
    Pp.hv 2 (Pp.str "args=[" ++ pp_sjoinmap_list (fun l -> Pp.str (str_of_name_permissive (Context.Rel.Declaration.get_name (Environ.lookup_rel (Environ.nb_rel env - l) env)))) args ++ Pp.str "]") +++
    Pp.hv 2 (Pp.str "result=" ++ Printer.pr_econstr_env env sigma ret)));*)
  ret
and simplify_matchapp_rec1 (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) (args : int list) : EConstr.t =
  match EConstr.kind sigma term with
  | Var _| Meta _ | Evar _ | Sort _ | Cast _ | Prod _ | Ind _
  | CoFix _ | Int _ | Float _ | Array _ ->
      user_err (Pp.str "[codegen:simplify_matchapp_rec] unsupported term:" +++ Printer.pr_econstr_env env sigma term)
  | Rel _ | Const _ | Construct _ | Proj _ ->
      mkApp (term, Array.of_list (rels_of_levels env args))
  | Fix ((ks, j), ((nary, tary, fary) as prec)) ->
      let env2 = push_rec_types prec env in
      let fary' = Array.map (fun f -> simplify_matchapp_rec env2 sigma f []) fary in
      mkApp (mkFix ((ks, j), (nary, tary, fary')), Array.of_list (rels_of_levels env args))
  | App (f, rels) ->
      let args' =
        List.append
          (CArray.map_to_list (fun rel -> Environ.nb_rel env - destRel sigma rel) rels)
          args
      in
      simplify_matchapp_rec env sigma f args'
  | Lambda (x,t,e) ->
      let na = List.length args in
      if na = 0 then
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        mkLambda (x,t, simplify_matchapp_rec env2 sigma e [])
      else
        let (fargs, body) = decompose_lam_upto_n env sigma na term in
        let (fargs, body, args1, args2) =
          let nf = List.length fargs in
          if nf < na then
            (fargs, body, CList.firstn nf args, CList.skipn nf args)
          else
            (CList.skipn (nf-na) fargs, EConstr.compose_lam (CList.firstn (nf-na) fargs) body, args, [])
        in
        let rels1 = rels_of_levels env args1 in
        let term' = Vars.substl (List.rev rels1) body in
        simplify_matchapp_rec env sigma term' args2
  | LetIn (x,e,t,b) ->
      let e' = simplify_matchapp_rec env sigma e [] in
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let b' = simplify_matchapp_rec env2 sigma b args in
      mkLetIn (x,e',t,b')
  | Case (ci, u, pms, ((mpred_nas, mpred_body) as mpred), iv, item, bl) ->
      let (_, _, _, (mpred_ctx, _), _, _, bl0) = EConstr.annotate_case env sigma (ci, u, pms, mpred, iv, item, bl) in
      if CList.is_empty args then
        let bl' =
          Array.map2
            (fun (nas,body) (ctx,_) ->
              let env2 = EConstr.push_rel_context ctx env in
              (nas, simplify_matchapp_rec env2 sigma body []))
            bl bl0
        in
        mkCase (ci, u, pms, mpred, iv, item, bl')
      else
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
        let mpred_env = EConstr.push_rel_context mpred_ctx env in
        let na = List.length args in
        let (mpred_fargs, mpred_body) = decompose_prod_n_acc env [] na mpred_body in
        if List.exists (fun (x,t) -> not (Vars.closed0 sigma t)) mpred_fargs then
          user_err (Pp.str "[codegen] could not move arg of (match ... end arg) because dependent-match (dependent argument):" +++
                    Printer.pr_econstr_env env sigma term)
        else
          let rels = rels_of_levels mpred_env args in
          let mpred_body = Vars.substl (List.rev rels) mpred_body in
          let bl' =
            Array.map2
              (fun (nas,body) (ctx,_) ->
                let env2 = EConstr.push_rel_context ctx env in
                (nas, simplify_matchapp_rec env2 sigma body args))
              bl bl0
          in
          mkCase (ci, u, pms, (mpred_nas, mpred_body), iv, item, bl')

let simplify_matchapp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  let ret = simplify_matchapp_rec env sigma term [] in
  ignore (Typing.type_of env sigma ret); (* typing check of transformed term *)
  ret

