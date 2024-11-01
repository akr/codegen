From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

Ltac2 rec numprods (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _b t' => Int.add 1 (numprods t')
  | _ => 0
  end.

Ltac2 numargs (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _fn args => Array.length args
  | _ => 0
  end.

Ltac2 mkRel (i : int) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Rel i).

Ltac2 mkApp (fn : constr) (args : constr array) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.App fn args).

Ltac2 mkProd (b : binder) (t : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Prod b t).

Ltac2 mkLambda (b : binder) (t : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Lambda b t).

Ltac2 mkCase (cinfo : Constr.Unsafe.case) (ret : constr) (rel : Constr.Binder.relevance)
  (cinv : Constr.Unsafe.case_invert) (item : constr) (branches : constr array) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Case cinfo (ret, rel) cinv item branches).

Ltac2 mkInd (ind : inductive) (u : instance) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Ind ind u).

Ltac2 destInd (t : constr) : inductive * instance :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind ind u => (ind, u)
  | _ => Control.backtrack_tactic_failure "not ind-expression"
  end.

Ltac2 mkConstructUi (indexp : constr) (i : int) : constr :=
  let (ind, u) := destInd indexp in
  Constr.Unsafe.make (Constr.Unsafe.Constructor (Constr.Unsafe.constructor ind i) u).

Ltac2 decompose_app (t : constr) : constr * constr array :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App fn args => (fn, args)
  | _ => (t, [| |])
  end.

Ltac2 rec compose_prod (bs : binder list) (t : constr) : constr :=
  match bs with
  | [] => t
  | b :: bs' => mkProd b (compose_prod bs' t)
  end.

Ltac2 rec decompose_prod (t : constr) : binder list * constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b c =>
      let (bs, body) := decompose_prod c in
      ((b :: bs), body)
  | _ => ([], t)
  end.

Ltac2 rec compose_lambda (bs : binder list) (t : constr) : constr :=
  match bs with
  | [] => t
  | b :: bs' => mkLambda b (compose_lambda bs' t)
  end.

Ltac2 rec decompose_lambda (t : constr) : binder list * constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda b c =>
      let (bs, body) := decompose_lambda c in
      ((b :: bs), body)
  | _ => ([], t)
  end.

Ltac2 rec decompose_lambda_n (n : int) (t : constr) : binder list * constr :=
  if Int.le n 0 then
    ([], t)
  else
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Lambda b c =>
        let (bs, body) := decompose_lambda_n (Int.sub n 1) c in
        ((b :: bs), body)
    | _ => Control.backtrack_tactic_failure "lambdas not enough"
    end.

Ltac2 isCase (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Case _ _ _ _ _ => true
  | _ => false
  end.

Ltac2 destCase (t : constr) : (Constr.Unsafe.case * constr * Constr.Binder.relevance * Constr.Unsafe.case_invert * constr * constr array) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Case cinfo (ret, rel) cinv item branches => (cinfo, ret, rel, cinv, item, branches)
  | _ => Control.backtrack_tactic_failure "not match-expression"
  end.

Ltac2 string_app3 (s1 : string) (s2 : string) (s3 : string) : string :=
  String.app s1 (String.app s2 s3).

Ltac2 string_app5 (s1 : string) (s2 : string) (s3 : string) (s4 : string) (s5 : string) : string :=
  String.concat "" [s1; s2; s3; s4; s5].

Ltac2 message_of_array (f : 't -> message) (ary : 't array) : message :=
  let len := Array.length ary in
  let sary := Array.map (fun e => Message.to_string (f e)) ary in
  if Int.equal len 0 then
    Message.of_string "[| |]"
  else
    Message.of_string (string_app3 "[| " (String.concat "; " (Array.to_list sary)) " |]").

Ltac2 message_of_tuple2 (f1 : 't1 -> message) (f2 : 't2 -> message) (x : 't1 * 't2) : message :=
  match x with
  | (x1, x2) =>
      Message.of_string (string_app5 "(" (Message.to_string (f1 x1)) ", " (Message.to_string (f2 x2)) ")")
  end.

Ltac2 message_of_binder (b : binder) : message :=
    Message.of_string
    (string_app5
      "("
      (match Constr.Binder.name b with
      | None => "_"
      | Some id => Ident.to_string id
      end)
      " : "
      (Message.to_string (Message.of_constr (Constr.Binder.type b)))
      ")").

Ltac2 map_invert (f : constr -> constr) (cinv : Constr.Unsafe.case_invert) : Constr.Unsafe.case_invert :=
  match cinv with
  | Constr.Unsafe.NoInvert => Constr.Unsafe.NoInvert
  | Constr.Unsafe.CaseInvert indices => Constr.Unsafe.CaseInvert (Array.map f indices)
  end.

Ltac2 cinv_liftn (n : int) (k : int) (cinv : Constr.Unsafe.case_invert) : Constr.Unsafe.case_invert :=
  map_invert (Constr.Unsafe.liftn n k) cinv.

Ltac2 nf_type (t : constr) : constr :=
  Std.eval_cbv RedFlags.all (Constr.type t).

Ltac2 make_proof_term_for_matchapp (goal_type : constr) : constr :=
  let (eq, eq_type, lhs, rhs) :=
    match! goal_type with
    | _ = _ =>
        match Constr.Unsafe.kind goal_type with
        | Constr.Unsafe.App eq args =>
            (eq, Array.get args 0, Array.get args 1, Array.get args 2)
        | _ => Control.backtrack_tactic_failure "goal is not equality"
        end
    | _ => Control.backtrack_tactic_failure "goal is not equality"
    end
  in
  let (lhs_fn, lhs_args) := decompose_app lhs in
  let (cinfo1, ret1, rel1, cinv1, item1, branches1) :=
    match Constr.Unsafe.kind lhs_fn with
    | Constr.Unsafe.Case cinfo (ret, rel) cinv item branches => (cinfo, ret, rel, cinv, item, branches)
    | _ => Control.backtrack_tactic_failure "LHS is not match-expression"
    end
  in
  let (rhs_fn, rhs_args) := decompose_app rhs in
  let (cinfo2, ret2, rel2, cinv2, item2, branches2) :=
    match Constr.Unsafe.kind rhs_fn with
    | Constr.Unsafe.Case cinfo (ret, rel) cinv item branches => (cinfo, ret, rel, cinv, item, branches)
    | _ => Control.backtrack_tactic_failure "RHS is not match-expression"
    end
  in
  if Bool.neg (Constr.equal item1 item2) then
    Control.backtrack_tactic_failure "different match-item in LHS and RHS"
  else
  let (item_binder, _ret_type) :=
    match Constr.Unsafe.kind ret1 with
    | Constr.Unsafe.Lambda binder ret => (binder, ret)
    | _ =>  Control.backtrack_tactic_failure "return-clause is not Lambda"
    end
  in
  let new_ret_item := mkRel 1 in
  let new_ret := Constr.Unsafe.make (Constr.Unsafe.Lambda item_binder
    (mkApp eq [| eq_type;
      mkApp (mkCase cinfo1 ret1 rel1 cinv1 new_ret_item branches1) lhs_args;
      mkApp (mkCase cinfo2 ret2 rel2 cinv2 new_ret_item branches2) rhs_args |]))
  in
  let item_type := Std.eval_cbv RedFlags.all (Constr.Binder.type item_binder) in
  let item_type_nf := Std.eval_cbv RedFlags.all item_type in
  let (item_type_fn, item_type_params) := decompose_app item_type_nf in
  let numparams := Array.length item_type_params in
  let (item_type_ind, _item_type_u) := destInd item_type_fn in
  let item_type_ind_data := Ind.data item_type_ind in
  let numcstrs := Ind.nconstructors item_type_ind_data in

  let new_branches :=
    Array.init numcstrs (fun j =>
      let cstr := (mkConstructUi item_type_fn j) in
      let cstr_type := nf_type cstr in
      let cstr_type_numprods := numprods cstr_type in
      let cstr_numargs := Int.sub cstr_type_numprods numparams in
      let branch1 := Array.get branches1 j in
      let (binders1, branch1_body) := decompose_lambda_n cstr_numargs branch1 in
      let branch2 := Array.get branches2 j in
      let (_binders2, branch2_body) := decompose_lambda_n cstr_numargs branch2 in
      let branch1' := mkApp branch1_body lhs_args in
      let branch2' := mkApp branch2_body rhs_args in
      let subgoal_type := compose_prod binders1 (mkApp eq [| eq_type; branch1'; branch2' |]) in
      let subgoal := open_constr:(_) in
      Unification.unify_with_current_ts (Constr.type subgoal) subgoal_type;
      let subgoal_args := Array.init cstr_numargs (fun k => mkRel (Int.sub cstr_numargs k)) in
      let new_branch := compose_lambda binders1 (mkApp subgoal subgoal_args) in
      new_branch) in

  let proof_term := (mkCase cinfo1 new_ret rel1 cinv1 item1 new_branches) in
  proof_term.

Lemma L : forall (x : list nat),
    match x with nil => Nat.add 1 | cons m _ => Nat.add m end 2
  = match x with nil => Nat.add 1 2 | cons m _ => Nat.add m 2 end.
Proof.
  intros.
(*
1 goal
x : list nat
______________________________________(1/1)
match x with
| nil => Nat.add 1
| (m :: _)%list => Nat.add m
end 2 = match x with
        | nil => 1 + 2
        | (m :: _)%list => m + 2
        end
*)
  Control.refine (fun () => make_proof_term_for_matchapp (Control.goal ())).

(*
2 goals
x : list nat
______________________________________(1/2)
1 + 2 = 1 + 2
______________________________________(2/2)
forall m : nat, list nat -> m + 2 = m + 2
*)
Show Proof.
(*
(fun x : list nat =>
 match
   x as x0
   return
     (match x0 with
      | nil => Nat.add 1
      | (m :: _)%list => Nat.add m
      end 2 = match x0 with
              | nil => 1 + 2
              | (m :: _)%list => m + 2
              end)
 with
 | nil => ?Goal
 | (m :: l)%list => ?Goal0 m l
 end)
*)
    reflexivity.
  intros.
  reflexivity.
Qed.
