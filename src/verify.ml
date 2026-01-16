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

let codegen_solve () : unit Proofview.tactic =
  let gr = Rocqlib.lib_ref "codegen.verification_anchor" in
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

let verify_transformation (env : Environ.env) (sigma : Evd.evar_map) (lhs_fun : EConstr.t) (rhs_fun : EConstr.t) : (Evd.evar_map * verification_step option) =
  if not (optread_transformation_verification ()) then
    (sigma, None)
  else if EConstr.eq_constr sigma lhs_fun rhs_fun then
    (sigma, None)
  else
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
    let ((), pv, env, unsafe, tree) =
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
    (sigma, Some { vstep_lhs_fun=lhs_fun; vstep_rhs_fun=rhs_fun; vstep_goal=ty; vstep_proof=proof })

let combine_verification_steps (env : Environ.env) (sigma: Evd.evar_map) (first_term : EConstr.t) (rev_steps : verification_step list) (last_term : EConstr.t) : Evd.evar_map * EConstr.types * EConstr.t =
  (*
  List.iteri
    (fun i { vstep_lhs_fun=lhs_fun; vstep_rhs_fun=rhs_fun; vstep_goal=goal; vstep_proof=proof } ->
      msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] [" ++ Pp.int i ++ Pp.str "] lhs_fun=" +++ Printer.pr_econstr_env env sigma lhs_fun);
      msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] [" ++ Pp.int i ++ Pp.str "] rhs_fun=" +++ Printer.pr_econstr_env env sigma rhs_fun);
      msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] [" ++ Pp.int i ++ Pp.str "] goal=" +++ Printer.pr_econstr_env env sigma goal);
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
    | { vstep_proof=last_step_proof } :: rest ->
        let proof = List.fold_left
          (fun acc_proof { vstep_lhs_fun=prev_lhs_fun; vstep_rhs_fun=prev_rhs_fun; vstep_proof=prev_proof } ->
            mkApp (eq_trans, [| val_type; mkApp (prev_lhs_fun, args); mkApp (prev_rhs_fun, args); mkApp (last_term, args); mkApp (prev_proof, args); acc_proof |]))
          (mkApp (last_step_proof, args))
          rest
        in
        let eq_proof = it_mkLambda proof prod_ctx in
        eq_proof
  in
  (*msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] eq_prop=" ++ Printer.pr_econstr_env env sigma eq_prop);
    msg_debug_hov (Pp.str "[codegen:combine_equality_proofs] eq_proof=" ++ Printer.pr_econstr_env env sigma eq_proof);*)
  (sigma, eq_prop, eq_proof)
