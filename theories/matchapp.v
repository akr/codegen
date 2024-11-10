From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

Ltac2 array_map3 (f : 'a -> 'b -> 'c -> 'd) (a : 'a array) (b : 'b array) (c : 'c array) :=
  Control.assert_valid_argument "array_map3" (Int.equal (Array.length a) (Array.length b));
  Control.assert_valid_argument "array_map3" (Int.equal (Array.length a) (Array.length c));
  Array.init (Array.length a) (fun i => f (Array.get a i) (Array.get b i) (Array.get c i)).

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

Ltac2 mkLetIn (b : binder) (e : constr) (t : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.LetIn b e t).

Ltac2 mkCase (cinfo : Constr.Unsafe.case) (ret : constr) (rel : Constr.Binder.relevance)
  (cinv : Constr.Unsafe.case_invert) (item : constr) (branches : constr array) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Case cinfo (ret, rel) cinv item branches).

Ltac2 mkInd (ind : inductive) (u : instance) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Ind ind u).

Ltac2 mkFix (decargs : int array) (entry : int) (binders : binder array) (funcs : constr array) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Fix decargs entry binders funcs).

Ltac2 destInd (t : constr) : inductive * instance :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind ind u => (ind, u)
  | _ => Control.backtrack_tactic_failure "not ind-expression"
  end.

Ltac2 destFix_opt (t : constr) : (int array * int * binder array * constr array) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Fix decargs entry binders bodies => Some (decargs, entry, binders, bodies)
  | _ => None
  end.

Ltac2 destFix (t : constr) : int array * int * binder array * constr array :=
  Option.get (destFix_opt t).

(* Ltac2 Eval (destFix constr:(fix even (n : nat) : bool := match n with O => true | S m => negb (even m) end)). *)

Ltac2 substFix (decargs : int array) (binders : binder array) (bodies : constr array) : constr array :=
  let h := Array.length bodies in
  let fix_terms := Array.rev (Array.init h (fun i => mkFix decargs i binders bodies)) in
  let new_bodies := Array.map (Constr.Unsafe.substnl (Array.to_list fix_terms) 0) bodies in
  new_bodies.

(*
Ltac2 Eval
  let (decargs, _entry, binders, bodies) :=
    destFix constr:(fix even (n : nat) : bool := match n with O => true | S m => odd m end
                    with odd (n : nat) : bool := match n with O => false | S m => even m end
                    for even) in
  substFix decargs binders bodies. 
*)

Ltac2 destEq_opt (t : constr) : (constr * constr * constr * constr) option :=
  match! t with
  | _ = _ =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App eq args =>
          Some (eq, Array.get args 0, Array.get args 1, Array.get args 2)
      | _ => None
      end
  | _ => None
  end.

Ltac2 mkConstructUi (indterm : constr) (i : int) : constr :=
  let (ind, u) := destInd indterm in
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


Ltac2 mkApp_beta (fn : constr) (args : constr array) : constr :=
  let nargs := Array.length args in
  let nbinders :=
    let (binders, _body) := decompose_lambda fn in
    List.length binders
  in
  let n := if Int.le nargs nbinders then nargs else nbinders in
  let (binders, body) := decompose_lambda_n n fn in
  let fn' := Constr.Unsafe.substnl (Array.to_list (Array.rev (Array.sub args 0 n))) 0 body in
  mkApp fn' (Array.sub args n (Int.sub nargs n)).

(*
Ltac2 Eval mkApp_beta constr:(fun a b c => a + b + c) [| constr:(1); constr:(2); constr:(3) |].
Ltac2 Eval mkApp_beta constr:(fun a b c => a + b + c) [| constr:(1); constr:(2) |].
Ltac2 Eval mkApp_beta constr:(fun a b => match a with O => fun c => a + b | S m => fun c => b + c end) [| constr:(1); constr:(2); constr:(3) |].
*)

Ltac2 make_subgoal (ctx : constr list) (ty : constr) : constr :=
  let hole := preterm:(_) in
  let pre := List.fold_right (fun ty pre => preterm:(fun (H:$constr:ty) => $preterm:pre)) ctx hole in
  let t := Constr.Pretype.pretype
             Constr.Pretype.Flags.open_constr_flags_no_tc
             Constr.Pretype.expected_without_type_constraint
             pre
  in
  let (_binders, body) := decompose_lambda t in
  Unification.unify_with_current_ts (Constr.type body) ty;
  body.

(*
Ltac2 Eval make_subgoal [constr:(nat); constr:(bool)] constr:(bool).
*)

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

Ltac2 message_of_list (f : 't -> message) (s : 't list) : message :=
  message_of_array f (Array.of_list s).

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

Ltac2 nf_of (t : constr) : constr :=
  Std.eval_cbv RedFlags.all t.

Ltac2 nftype_of (t : constr) : constr :=
  nf_of (Constr.type t).

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
      let cstr_type := nftype_of cstr in
      let cstr_type_numprods := numprods cstr_type in
      let cstr_numargs := Int.sub cstr_type_numprods numparams in
      let branch1 := Array.get branches1 j in
      let (binders1, branch1_body) := decompose_lambda_n cstr_numargs branch1 in
      let branch2 := Array.get branches2 j in
      let (_binders2, branch2_body) := decompose_lambda_n cstr_numargs branch2 in
      let branch1' := mkApp branch1_body lhs_args in
      let branch2' := mkApp branch2_body rhs_args in
      let subgoal_type := compose_prod binders1 (mkApp eq [| eq_type; branch1'; branch2' |]) in
      let subgoal := make_subgoal [] subgoal_type in
      let subgoal_args := Array.init cstr_numargs (fun k => mkRel (Int.sub cstr_numargs k)) in
      let new_branch := compose_lambda binders1 (mkApp subgoal subgoal_args) in
      new_branch) in

  let proof_term := (mkCase cinfo1 new_ret rel1 cinv1 item1 new_branches) in
  proof_term.

Ltac2 Notation codegen_matchapp := Control.refine (fun () => make_proof_term_for_matchapp (Control.goal ())).

(*
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
  codegen_matchapp.

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
*)


Ltac2 make_proof_term_for_fix (goal_type : constr) :=
  let (eq, _eq_type, lhs, rhs) :=
    match destEq_opt goal_type with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "goal is not equality"
    end
  in
  let (fn1, args1) := decompose_app lhs in
  let (decargs1, entry1, binders1, bodies1) :=
    match destFix_opt fn1 with
    | Some x => x
    | None => Control.backtrack_tactic_failure "LHS is not fix-expression"
    end
  in
  let h := Array.length bodies1 in
  let fix_terms1 := Array.init h (fun i => mkFix decargs1 i binders1 bodies1) in
  let substituted_bodies1 := substFix decargs1 binders1 bodies1 in
  let (fn2, args2) := decompose_app rhs in
  if Bool.neg (Array.equal Constr.equal args1 args2) then
    Control.backtrack_tactic_failure "matchapp-fix"
  else
  let (decargs2, _entry2, binders2, bodies2) :=
    match destFix_opt fn2 with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "RHS is not match-expression"
    end
  in
  let fix_terms2 := Array.init h (fun i => mkFix decargs2 i binders2 bodies2) in
  let substituted_bodies2 := substFix decargs2 binders2 bodies2 in
  let fn_types1 := Array.map (fun b => nf_of (Constr.Binder.type b)) binders1 in
  let subgoal_types := array_map3
    (fun fn_type body1 body2 =>
      let (arg_binders, ret_type) := decompose_prod fn_type in
      let numargs := List.length arg_binders in
      let args := Array.init numargs (fun k => mkRel (Int.sub numargs k)) in
      let new_type := compose_prod arg_binders (mkApp eq [| ret_type; mkApp_beta body1 args; mkApp_beta body2 args |]) in
      new_type)
    fn_types1 substituted_bodies1 substituted_bodies2
  in
  let ih_types :=
    Array.init h
      (fun i =>
        let fix1 := Array.get fix_terms1 i in
        let fix2 := Array.get fix_terms2 i in
        let fn_type := Array.get fn_types1 i in
        let (arg_binders, ret_type) := decompose_prod fn_type in
        let numargs := List.length arg_binders in
        let ih_type :=
          let args := Array.init numargs (fun k => mkRel (Int.sub numargs k)) in
          compose_prod arg_binders (mkApp eq [| ret_type; mkApp fix1 args; mkApp fix2 args |])
        in
        ih_type)
  in
  let subgoals := Array.map (fun subgoal_type => make_subgoal (Array.to_list ih_types) subgoal_type) subgoal_types in
  let new_funcs :=
    Array.init h
      (fun i =>
        let fix1 := Array.get fix_terms1 i in
        let fix2 := Array.get fix_terms2 i in
        let decarg := Array.get decargs1 i in
        let fn_type := Array.get fn_types1 i in
        let (arg_binders, ret_type) := decompose_prod fn_type in
        let numargs := List.length arg_binders in
        let decarg_binder := List.nth arg_binders decarg in
        let new_ret_args := Array.init numargs (fun k => if Int.equal k decarg then mkRel 1 else mkRel (Int.sub (Int.add numargs 2) k)) in
        let new_ret := mkLambda decarg_binder (mkApp eq [| ret_type; mkApp fix1 new_ret_args; mkApp fix2 new_ret_args |]) in
        let decarg_type := Constr.Binder.type decarg_binder in
        let (decarg_type_fn, decarg_type_args) := decompose_app decarg_type in
        let (decarg_ind, _decarg_u) := destInd decarg_type_fn in
        let decarg_ind_data := Ind.data decarg_ind in
        let decarg_type_numargs := Array.length decarg_type_args in
        let num_constructors := Ind.nconstructors decarg_ind_data in
        let cinfo := Constr.Unsafe.case decarg_ind in
        let branches :=
          Array.init num_constructors
            (fun j =>
              let cstr := mkConstructUi decarg_type_fn j in
              let cstr_type := nftype_of cstr in
              let (cstr_binders, _cstr_ret) := decompose_prod cstr_type in
              let cstr_binders_without_params := List.skipn decarg_type_numargs cstr_binders in
              let cstr_numargs_without_params := List.length cstr_binders_without_params in
              let branch_body_args := Array.init numargs
                (fun k =>
                  if Int.equal k decarg then
                    mkApp cstr (Array.init cstr_numargs_without_params (fun l => mkRel (Int.sub cstr_numargs_without_params l)))
                  else
                    mkRel (Int.sub (Int.add numargs (Int.add 1 cstr_numargs_without_params)) k))
              in
              let branch_body := mkApp (mkRel (Int.add 1 cstr_numargs_without_params)) branch_body_args in
              let branch := compose_lambda cstr_binders_without_params branch_body in
              branch)
        in
        let citem := mkRel (Int.sub (Int.add numargs 1) decarg) in
        let case_term := mkCase cinfo new_ret Constr.Binder.Relevant Constr.Unsafe.NoInvert citem branches in
        let subgoal_type := Array.get subgoal_types i in
        let subgoal := Constr.Unsafe.liftn (List.length arg_binders) 1 (Array.get subgoals i) in
        let let_term := mkLetIn (Constr.Binder.make None subgoal_type) subgoal case_term in
        let new_fn := compose_lambda arg_binders let_term in
        new_fn)
  in
  let new_binders := Array.map (fun ih_type => Constr.Binder.make None ih_type) ih_types in
  let new_fix_term := mkFix decargs1 entry1 new_binders new_funcs in
  let proof_term := mkApp new_fix_term args1 in
  proof_term.

Ltac2 Notation codegen_fix := Control.refine (fun () => make_proof_term_for_fix (Control.goal ())).

Lemma L : forall (x y : nat),
    (fix f1 (a n : nat) : bool := match n with O => true | S m => g1 a m end
    with g1 (a n : nat) : bool := match n with O => false | S m => f1 a m end
    for f1) x y =
    (fix f2 (a n : nat) : bool := match n with O => true | S m => g2 a m end
    with g2 (a n : nat) : bool := match n with O => false | S m => f2 a m end
    for f2) x y.
Proof.
  intros.
  codegen_fix.
  Show Proof.
    intros a n.
    destruct n.
      reflexivity.
    apply H.
  intros a n.
  destruct n.
    reflexivity.
  apply H0.
Show Proof.
Qed.

(*
    h is the number of mutual functions
    forall j, (Fj is (fix ... (fi/ki:Ti := ti) ... for fj))
    forall j, (Gj is (fix ... (gi/ki:Ti := ui) ... for gj))
    forall j, (Γ, (IH1 : F1 ~ G1), ..., (IHh : Fh ~ Gh) |- p_j : t_j[F1/f1,...,Fh/fh] ~ ui[G1/g1,...,Gh/gh])
    --------------------------------------------------------------------------------------------------------
    Γ |- (fix ...
              IHi/ki:(Fi ~ Gi) :=
                fun a1 ... an =>
                  let H := pi in
                  match a_{ki} as x return Fi a1 ... a{ki-1} x a{ki+1} ... an
                                         = Gi a1 ... a{ki-1} x a{ki+1} ... an with
                  | C1 cargs1 => H a1 ... a{ki-1} (C1 cargs1) a{ki+1} ... an
                  | ...
                  | Cm cargsm => H a1 ... a{ki-1} (Cm cargsm) a{ki+1} ... an
                  end
              ...
          for IHj) b1 ... bn : Fj b1 ... bn = Gj b1 ... bn
*)
