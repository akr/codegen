From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

Require FunctionalExtensionality.

Definition codegen_verification_anchor := tt.
Register codegen_verification_anchor as codegen.verification_anchor.

Ltac2 array_map3 (f : 'a -> 'b -> 'c -> 'd) (a : 'a array) (b : 'b array) (c : 'c array) :=
  Control.assert_valid_argument "array_map3" (Int.equal (Array.length a) (Array.length b));
  Control.assert_valid_argument "array_map3" (Int.equal (Array.length a) (Array.length c));
  Array.init (Array.length a) (fun i => f (Array.get a i) (Array.get b i) (Array.get c i)).

Ltac2 array_take (n : int) (a : 'a array) : 'a array := Array.sub a 0 n.
Ltac2 array_drop (n : int) (a : 'a array) : 'a array := Array.sub a n (Int.sub (Array.length a) n).

Ltac2 array_find (p : 'a -> bool) (a : 'a array) : int option :=
  let rec aux i n :=
    if Int.equal n 0 then
      None
    else
      if p (Array.get a i) then
        Some i
      else
        aux (Int.add i 1) (Int.sub n 1)
  in
  aux 0 (Array.length a).

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

Ltac2 destLambda_opt (t : constr) : (binder * constr) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda b e => Some (b, e)
  | _ => None
  end.

Ltac2 destLambda (t : constr) : binder * constr :=
  match destLambda_opt t with
  | Some x => x
  | None => Control.backtrack_tactic_failure "not lambda-expression"
  end.

Ltac2 destInd (t : constr) : inductive * instance :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind ind u => (ind, u)
  | _ => Control.backtrack_tactic_failure "not ind-expression"
  end.

Ltac2 destLetIn_opt (t : constr) : (binder * constr * constr) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.LetIn binder exp body => Some (binder, exp, body)
  | _ => None
  end.

Ltac2 destLetIn (t : constr) : (binder * constr * constr) :=
  Option.get (destLetIn_opt t).

Ltac2 destCase_opt (t : constr) : (Constr.Unsafe.case * constr * Constr.Binder.relevance * Constr.Unsafe.case_invert * constr * constr array) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Case cinfo (ret, rel) cinv item branches => Some (cinfo, ret, rel, cinv, item, branches)
  | _ => None
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

Ltac2 rec compose_prod_decls (ctx : (binder * constr option) list) (t : constr) : constr :=
  match ctx with
  | [] => t
  | (b, None) :: rest => mkProd b (compose_prod_decls rest t)
  | (b, Some e) :: rest => mkLetIn b e (compose_prod_decls rest t)
  end.

Ltac2 rec decompose_prod_decls (t : constr) : (binder * constr option) list * constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b c =>
      let (ctx, body) := decompose_prod_decls c in
      (((b, None) :: ctx), body)
  | Constr.Unsafe.LetIn b e c =>
      let (ctx, body) := decompose_prod_decls c in
      (((b, Some e) :: ctx), body)
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

Ltac2 rec decompose_lambda_upto (n : int) (t : constr) : binder list * constr :=
  if Int.le n 0 then
    ([], t)
  else
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Lambda b c =>
        let (bs, body) := decompose_lambda_upto (Int.sub n 1) c in
        ((b :: bs), body)
    | _ => ([], t)
    end.

Ltac2 rec compose_lambda_decls (ctx : (binder * constr option) list) (t : constr) : constr :=
  match ctx with
  | [] => t
  | (b, None) :: rest => mkLambda b (compose_lambda_decls rest t)
  | (b, Some e) :: rest => mkLetIn b e (compose_lambda_decls rest t)
  end.

Ltac2 rec decompose_lambda_decls (t : constr) : (binder * constr option) list * constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda b c =>
      let (ctx, body) := decompose_lambda_decls c in
      (((b, None) :: ctx), body)
  | Constr.Unsafe.LetIn b e c =>
      let (ctx, body) := decompose_lambda_decls c in
      (((b, Some e) :: ctx), body)
  | _ => ([], t)
  end.

Ltac2 rec compose_letin (ctx : (binder * constr) list) (t : constr) : constr :=
  match ctx with
  | [] => t
  | (b, e) :: rest => mkLetIn b e (compose_letin rest t)
  end.

Ltac2 rec decompose_letin (t : constr) : (binder * constr) list * constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.LetIn b e c =>
      let (ctx, body) := decompose_letin c in
      (((b, e) :: ctx), body)
  | _ => ([], t)
  end.

Ltac2 mkApp_beta (fn : constr) (args : constr array) : constr :=
  let rec aux nbinders t ofs :=
    let n := Int.sub (Array.length args) ofs in
    if Int.le n 0 then
      t
    else
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Lambda _ _ =>
        let (binders, body) := decompose_lambda_upto n t in
        let m := List.length binders in
        let body' := Constr.Unsafe.substnl (Array.to_list (Array.rev (Array.map (Constr.Unsafe.liftn nbinders 1) (Array.sub args ofs m)))) 0 body in
        aux nbinders body' (Int.add ofs m)
    | Constr.Unsafe.LetIn _ _ _ =>
        let (let_binders, body) := decompose_letin t in
        let m := List.length let_binders in
        compose_letin let_binders (aux (Int.add nbinders m) body ofs)
    | _ =>
        mkApp t (array_drop ofs args)
    end
  in
  aux 0 fn 0.

(*
Ltac2 mkApp_beta (fn : constr) (args : constr array) : constr :=
  let rec aux t args :=
    match args with
    | [] => t
    | first_arg :: rest_args =>
        match Constr.Unsafe.kind t with
        | Constr.Unsafe.Lambda _binder body =>
            aux (Constr.Unsafe.substnl [first_arg] 0 body) rest_args
        | Constr.Unsafe.LetIn binder exp body =>
            let args' := List.map (Constr.Unsafe.liftn 1 1) args in
            Constr.Unsafe.make (Constr.Unsafe.LetIn binder exp (aux body args'))
        | _ => mkApp t (Array.of_list args)
        end
    end
  in
  aux fn (Array.to_list args).
*)

(*
Ltac2 Eval mkApp_beta constr:(fun a b c => a + b + c) [| constr:(1); constr:(2); constr:(3) |].
Ltac2 Eval mkApp_beta constr:(fun a b c => a + b + c) [| constr:(1); constr:(2) |].
Ltac2 Eval mkApp_beta constr:(fun a b => match a with O => fun c => a + b | S m => fun c => b + c end) [| constr:(1); constr:(2); constr:(3) |].
Ltac2 Eval mkApp_beta constr:(let x := 0 in fun a b => a + b) [| constr:(1) |].
Ltac2 Eval mkApp_beta constr:(let x := 0 in fun a => let y := a + 1 in fun b => let z := a + b + 2 in fun c => c + 3) [| constr:(4) |].
Ltac2 Eval mkApp_beta constr:(let x := 0 in fun a => let y := a + 1 in fun b => let z := a + b + 2 in fun c => c + 3) [| constr:(4); constr:(5) |].
Ltac2 Eval mkApp_beta constr:(let x := 0 in fun a => let y := a + 1 in fun b => let z := a + b + 2 in fun c => c + 3) [| constr:(4); constr:(5); constr:(6) |].
Ltac2 Eval mkApp_beta constr:(let x := 0 in fun a => let y := a + 1 in fun b => let z := a + b + 2 in fun c => Nat.add (c + 3)) [| constr:(4); constr:(5); constr:(6); constr:(7) |].
Ltac2 Eval let (b,t) := destLambda constr:(fun a => a + let x := 1 in a + x) in mkLambda b (mkApp_beta t [| mkRel 1 |]).
*)

Ltac2 make_simple_subgoal (concl : constr) : constr :=
  let hole := preterm:(_ : $concl) in
  let t := Constr.Pretype.pretype
             Constr.Pretype.Flags.open_constr_flags_no_tc
             Constr.Pretype.expected_without_type_constraint
             hole
  in
  t.

Ltac2 make_subgoal (ctx : binder list) (concl : constr) :=
  let hole := preterm:(_ :> $concl) in
  let pre := List.fold_right
    (fun b p =>
      let ty := Constr.Binder.type b in
      preterm:(fun (x : $ty) => $preterm:p)) (* The variable name of the binder should be used, if possible. *)
    ctx hole
  in
  let t := Constr.Pretype.pretype
             Constr.Pretype.Flags.open_constr_flags_no_tc
             Constr.Pretype.expected_without_type_constraint
             pre
  in
  t.

(*
Ltac2 Eval make_subgoal (List.map (Constr.Binder.make None) [constr:(nat); constr:(nat)]) (mkApp constr:(@eq) [| constr:(nat); mkRel 2; mkRel 1 |]).
Ltac2 Eval make_subgoal (List.map (Constr.Binder.make None) [constr:(nat); constr:(bool)]) constr:(bool).
*)

Ltac2 make_subgoal2 (ctx : (binder * constr option) list) (concl : constr) :=
  let hole := preterm:(_ :> $concl) in
  let pre := List.fold_right
    (fun decl p =>
      match decl with
      | (b, None) =>
          let ty := Constr.Binder.type b in
          preterm:(fun (x : $ty) => $preterm:p) (* The variable name of the binder should be used, if possible. *)
      | (b, Some exp) =>
          let ty := Constr.Binder.type b in
          preterm:(let x : $ty := $exp in $preterm:p) (* The variable name of the binder should be used, if possible. *)
      end)
    ctx hole
  in
  let t := Constr.Pretype.pretype
             Constr.Pretype.Flags.open_constr_flags_no_tc
             Constr.Pretype.expected_without_type_constraint
             pre
  in
  t.

(*
Goal 0 = 1.
Proof.
Control.refine (fun () =>
  (make_subgoal2 [(Constr.Binder.make None constr:(nat), Some constr:(0));
                  (Constr.Binder.make None constr:(nat), Some constr:(1))]
                 (mkApp constr:(@eq) [| constr:(nat); mkRel 2; mkRel 1 |]))).
(*
1 goal
x0 := 0 : nat
x := 1 : nat
______________________________________(1/1)
x0 = x
*)
Show Proof.
(* (let x := 0 in let x0 := 1 in ?Goal) *)
*)

(*
Ltac2 Eval make_subgoal2 [(Constr.Binder.make None constr:(Type), None);
                          (Constr.Binder.unsafe_make None Constr.Binder.Relevant (mkRel 1), None)]
                         constr:(True).
(* fun (x : Type) (x0 : x) => ?Goal@{x0:=x; x:=x0} *)
*)

(*
Goal forall (T : Type) (x : T), True.
Proof.
Control.refine (fun () =>
  (make_subgoal2 [(Constr.Binder.make None constr:(Type), None);
                  (Constr.Binder.unsafe_make None Constr.Binder.Relevant (mkRel 1), None)]
                 constr:(True))).
(*
1 goal
x0 : Type
x : x0
______________________________________(1/1)
True
*)
Show Proof.
(* (fun (x : Type) (x0 : x) => ?Goal@{x0:=x; x:=x0}) *)
constructor.
Qed.
*)

Ltac2 destEqApp_opt (t : constr) : (constr * constr * constr array * constr * constr array) option :=
  match! t with
  | _ = _ =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App _eq args =>
          let (fn1, args1) := decompose_app (Array.get args 1) in
          let (fn2, args2) := decompose_app (Array.get args 2) in
          Some (Array.get args 0, fn1, args1, fn2, args2)
      | _ => None
      end
  | _ => None
  end.

(*
Ltac2 Eval print (of_constr constr:(@Coq.Init.Logic.eq)).
*)

Ltac2 intarray_ascending (start : int) (n : int) : int array :=
  Array.init n (fun k => Int.add start k).

Ltac2 intarray_descending (start : int) (n : int) : int array :=
  Array.init n (fun k => Int.sub start k).

Ltac2 mkRel_ascending (start : int) (n : int) : constr array :=
  Array.map mkRel (intarray_ascending start n).

Ltac2 mkRel_descending (start : int) (n : int) : constr array :=
  Array.map mkRel (intarray_descending start n).

Ltac2 make_exteq (nftype : constr) (lhs : constr) (rhs : constr) : constr :=
  let eq := constr:(@Coq.Init.Logic.eq) in
  let (binders, ret) := decompose_prod nftype in
  let n := List.length binders in
  let args := mkRel_descending n n in
  let lhs' := mkApp_beta (Constr.Unsafe.liftn n 1 lhs) args in
  let rhs' := mkApp_beta (Constr.Unsafe.liftn n 1 rhs) args in
  compose_prod binders (mkApp eq [|ret; lhs'; rhs'|]).

(* Ltac2 Eval print (of_constr (make_exteq constr:(nat -> nat -> nat) constr:(Nat.add) constr:(Nat.sub))). *)

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

Ltac2 nf_of (t : constr) : constr :=
  Std.eval_cbv RedFlags.all t.

Ltac2 nftype_of (t : constr) : constr :=
  nf_of (Constr.type t).

Ltac2 make_proof_term_for_matchapp (goal_type : constr) : constr :=
  let (eq_type, lhs_fn, lhs_args, rhs_fn, rhs_args) :=
    match destEqApp_opt goal_type with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "goal is not equality"
    end
  in
  let (cinfo1, ret1, rel1, cinv1, item1, branches1) :=
    match destCase_opt lhs_fn with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "LHS is not match-expression"
    end
  in
  let (cinfo2, ret2, rel2, cinv2, item2, branches2) :=
    match destCase_opt rhs_fn with
    | Some x => x
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
  let eq := constr:(@Coq.Init.Logic.eq) in
  let new_ret_item := mkRel 1 in
  let new_ret := Constr.Unsafe.make (Constr.Unsafe.Lambda item_binder
    (mkApp eq [| eq_type;
      mkApp (mkCase cinfo1 ret1 rel1 cinv1 new_ret_item branches1) lhs_args;
      mkApp (mkCase cinfo2 ret2 rel2 cinv2 new_ret_item branches2) rhs_args |]))
  in
  let item_type := nf_of (Constr.Binder.type item_binder) in
  let (item_type_fn, item_type_params) := decompose_app item_type in
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
      let branch1' := mkApp_beta branch1_body lhs_args in
      let branch2' := mkApp_beta branch2_body rhs_args in
      let subgoal_type := compose_prod binders1 (mkApp eq [| eq_type; branch1'; branch2' |]) in
      let subgoal := make_simple_subgoal subgoal_type in
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
  let (_eq_type, fn1, args1, fn2, args2) :=
    match destEqApp_opt goal_type with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "goal is not equality"
    end
  in
  let (decargs1, _entry1, binders1, bodies1) :=
    match destFix_opt fn1 with
    | Some x => x
    | None => Control.backtrack_tactic_failure "LHS is not fix-expression"
    end
  in
  let h1 := Array.length bodies1 in
  let fix_terms1 := Array.init h1 (fun i1 => mkFix decargs1 i1 binders1 bodies1) in
  let substituted_bodies1 := substFix decargs1 binders1 bodies1 in
  if Bool.neg (Array.equal Constr.equal args1 args2) then
    Control.backtrack_tactic_failure "matchapp-fix"
  else
  let (decargs2, entry2, binders2, bodies2) :=
    match destFix_opt fn2 with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "RHS is not match-expression"
    end
  in
  let h2 := Array.length bodies2 in
  let fix_terms2 := Array.init h2 (fun i2 => mkFix decargs2 i2 binders2 bodies2) in
  let substituted_bodies2 := substFix decargs2 binders2 bodies2 in
  let index1_of_index2 := Array.init h2
    (fun i2 =>
      let binder2 := Array.get binders2 i2 in
      let id2 :=
        match Constr.Binder.name binder2 with
        | None => Control.throw_invalid_argument "no-name fixfunc in RHS"
        | Some id2 => id2
        end
      in
      let i1_opt := array_find
        (fun b1 =>
          match Constr.Binder.name b1 with
          | None => Control.throw_invalid_argument "no-name fixfunc in LHS"
          | Some id1 => Ident.equal id1 id2
          end)
        binders1
      in
      match i1_opt with
      | None => Control.throw_invalid_argument (String.app "RHS fixfunc name not found in LHS fixfunc: " (Ident.to_string id2))
      | Some i1 => i1
      end)
  in
  let fn_types2 := Array.map (fun b => nf_of (Constr.Binder.type b)) binders2 in
  let eq := constr:(@Coq.Init.Logic.eq) in
  let subgoal_types := Array.init h2
    (fun i2 =>
      let i1 := Array.get index1_of_index2 i2 in
      let fn_type := Array.get fn_types2 i2 in
      let body2 := Array.get substituted_bodies2 i2 in
      let body1 := Array.get substituted_bodies1 i1 in
      let (arg_binders, ret_type) := decompose_prod fn_type in
      let numargs := List.length arg_binders in
      let args := Array.init numargs (fun k => mkRel (Int.sub numargs k)) in
      let new_type := compose_prod arg_binders (mkApp eq [| ret_type; mkApp_beta body1 args; mkApp_beta body2 args |]) in
      new_type)
  in
  let ih_types :=
    Array.init h2
      (fun i2 =>
        let i1 := Array.get index1_of_index2 i2 in
        let fix1 := Array.get fix_terms1 i1 in
        let fix2 := Array.get fix_terms2 i2 in
        let fn_type := Array.get fn_types2 i2 in
        let (arg_binders, ret_type) := decompose_prod fn_type in
        let numargs := List.length arg_binders in
        let ih_type :=
          let args := Array.init numargs (fun k => mkRel (Int.sub numargs k)) in
          compose_prod arg_binders (mkApp eq [| ret_type; mkApp fix1 args; mkApp fix2 args |])
        in
        ih_type)
  in
  let subgoals :=
    Array.map
      (fun subgoal_type => make_subgoal (Array.to_list (Array.map (Constr.Binder.make None) ih_types)) subgoal_type)
      subgoal_types
  in
  let new_funcs :=
    Array.init h2
      (fun i2 =>
        let i1 := Array.get index1_of_index2 i2 in
        let fix1 := Array.get fix_terms1 i1 in
        let fix2 := Array.get fix_terms2 i2 in
        let decarg := Array.get decargs1 i1 in
        let fn_type := Array.get fn_types2 i2 in
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
                    mkApp cstr (Array.append decarg_type_args (Array.init cstr_numargs_without_params (fun l => mkRel (Int.sub cstr_numargs_without_params l))))
                  else
                    mkRel (Int.sub (Int.add numargs (Int.add 1 cstr_numargs_without_params)) k))
              in
              let branch_body := mkApp (mkRel (Int.add 1 cstr_numargs_without_params)) branch_body_args in
              let branch := compose_lambda cstr_binders_without_params branch_body in
              branch)
        in
        let citem := mkRel (Int.sub (Int.add numargs 1) decarg) in
        let case_term := mkCase cinfo new_ret Constr.Binder.Relevant Constr.Unsafe.NoInvert citem branches in
        let subgoal_type := Array.get subgoal_types i2 in
        let subgoal :=
          mkApp_beta (Array.get subgoals i2) (mkRel_descending (Int.add h2 (List.length arg_binders)) h2)
        in
        let let_term := mkLetIn (Constr.Binder.make None subgoal_type) subgoal case_term in
        let new_fn := compose_lambda arg_binders let_term in
        new_fn)
  in
  let new_binders := Array.map (fun ih_type => Constr.Binder.make None ih_type) ih_types in
  let new_fix_term := mkFix decargs2 entry2 new_binders new_funcs in
  let proof_term := mkApp new_fix_term args1 in
  proof_term.

Ltac2 Notation codegen_fix := Control.refine (fun () => make_proof_term_for_fix (Control.goal ())).

(*
Lemma L : forall (x : nat),
            (fix f (n : nat) := match n with O => O | S m => S (f m) end) x
          = (fix f (n : nat) := match n with O => O | S m => (f m) + 1 end) x.
Proof.
  intros.
  codegen_fix.
Show Proof.
(*
(fun x : nat =>
 (fix H (n : nat) :
      (fix f (n0 : nat) : nat := match n0 with
                                 | 0 => 0
                                 | S m => S (f m)
                                 end) n =
      (fix f (n0 : nat) : nat := match n0 with
                                 | 0 => 0
                                 | S m => f m + 1
                                 end) n :=
    let H0 :
      forall n0 : nat,
      match n0 with
      | 0 => 0
      | S m => S ((fix f (n1 : nat) : nat := match n1 with
                                             | 0 => 0
                                             | S m0 => S (f m0)
                                             end) m)
      end =
      match n0 with
      | 0 => 0
      | S m => (fix f (n1 : nat) : nat := match n1 with
                                          | 0 => 0
                                          | S m0 => f m0 + 1
                                          end) m + 1
      end := ?Goal@{x0:=x; x:=H} in
    match
      n as n0
      return
        ((fix f (n1 : nat) : nat := match n1 with
                                    | 0 => 0
                                    | S m => S (f m)
                                    end) n0 =
         (fix f (n1 : nat) : nat := match n1 with
                                    | 0 => 0
                                    | S m => f m + 1
                                    end) n0)
    with
    | 0 => H0 0
    | S x0 => H0 (S x0)
    end) x)
*)
  intros.
  destruct n.
    reflexivity.
  rewrite<- plus_n_Sm.
  rewrite<- plus_n_O.
  f_equal.
  trivial with nocore.
Qed.
*)

(*
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
(*
(fun x y : nat =>
 (fix H (a n : nat) {struct n} :
      (fix f1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g1 a0 m
         end
       with g1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f1 a0 m
         end
       for
       f1) a n =
      (fix f2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g2 a0 m
         end
       with g2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f2 a0 m
         end
       for
       f2) a n :=
    let H1 :
      forall a0 n0 : nat,
      match n0 with
      | 0 => true
      | S m =>
          (fix f1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g1 a1 m0
             end
           with g1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f1 a1 m0
             end
           for
           g1) a0 m
      end =
      match n0 with
      | 0 => true
      | S m =>
          (fix f2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g2 a1 m0
             end
           with g2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f2 a1 m0
             end
           for
           g2) a0 m
      end := ?Goal@{x0:=x; x1:=H; x:=H0} in
    match
      n as n0
      return
        ((fix f1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g1 a0 m
            end
          with g1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f1 a0 m
            end
          for
          f1) a n0 =
         (fix f2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g2 a0 m
            end
          with g2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f2 a0 m
            end
          for
          f2) a n0)
    with
    | 0 => H1 a 0
    | S x0 => H1 a (S x0)
    end
  with H0 (a n : nat) {struct n} :
      (fix f1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g1 a0 m
         end
       with g1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f1 a0 m
         end
       for
       g1) a n =
      (fix f2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g2 a0 m
         end
       with g2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f2 a0 m
         end
       for
       g2) a n :=
    let H1 :
      forall a0 n0 : nat,
      match n0 with
      | 0 => false
      | S m =>
          (fix f1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g1 a1 m0
             end
           with g1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f1 a1 m0
             end
           for
           f1) a0 m
      end =
      match n0 with
      | 0 => false
      | S m =>
          (fix f2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g2 a1 m0
             end
           with g2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f2 a1 m0
             end
           for
           f2) a0 m
      end := ?Goal0@{x0:=x; x1:=H; x:=H0} in
    match
      n as n0
      return
        ((fix f1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g1 a0 m
            end
          with g1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f1 a0 m
            end
          for
          g1) a n0 =
         (fix f2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g2 a0 m
            end
          with g2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f2 a0 m
            end
          for
          g2) a n0)
    with
    | 0 => H1 a 0
    | S x0 => H1 a (S x0)
    end
  for
  H) x y)
*)
    intros a n.
    destruct n.
      reflexivity.
    now trivial with nocore.
  intros a n.
  destruct n.
    reflexivity.
  now trivial with nocore.
Show Proof.
(*
(fun x y : nat =>
 (fix H (a n : nat) {struct n} :
      (fix f1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g1 a0 m
         end
       with g1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f1 a0 m
         end
       for
       f1) a n =
      (fix f2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g2 a0 m
         end
       with g2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f2 a0 m
         end
       for
       f2) a n :=
    let H1 :
      forall a0 n0 : nat,
      match n0 with
      | 0 => true
      | S m =>
          (fix f1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g1 a1 m0
             end
           with g1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f1 a1 m0
             end
           for
           g1) a0 m
      end =
      match n0 with
      | 0 => true
      | S m =>
          (fix f2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g2 a1 m0
             end
           with g2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f2 a1 m0
             end
           for
           g2) a0 m
      end :=
      fun a0 n0 : nat =>
      match
        n0 as n1
        return
          (match n1 with
           | 0 => true
           | S m =>
               (fix f1 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => true
                  | S m0 => g1 a1 m0
                  end
                with g1 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => false
                  | S m0 => f1 a1 m0
                  end
                for
                g1) a0 m
           end =
           match n1 with
           | 0 => true
           | S m =>
               (fix f2 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => true
                  | S m0 => g2 a1 m0
                  end
                with g2 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => false
                  | S m0 => f2 a1 m0
                  end
                for
                g2) a0 m
           end)
      with
      | 0 => eq_refl
      | S n1 => (fun n2 : nat => H0 a0 n2) n1
      end in
    match
      n as n0
      return
        ((fix f1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g1 a0 m
            end
          with g1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f1 a0 m
            end
          for
          f1) a n0 =
         (fix f2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g2 a0 m
            end
          with g2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f2 a0 m
            end
          for
          f2) a n0)
    with
    | 0 => H1 a 0
    | S x0 => H1 a (S x0)
    end
  with H0 (a n : nat) {struct n} :
      (fix f1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g1 a0 m
         end
       with g1 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f1 a0 m
         end
       for
       g1) a n =
      (fix f2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => true
         | S m => g2 a0 m
         end
       with g2 (a0 n0 : nat) {struct n0} : bool :=
         match n0 with
         | 0 => false
         | S m => f2 a0 m
         end
       for
       g2) a n :=
    let H1 :
      forall a0 n0 : nat,
      match n0 with
      | 0 => false
      | S m =>
          (fix f1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g1 a1 m0
             end
           with g1 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f1 a1 m0
             end
           for
           f1) a0 m
      end =
      match n0 with
      | 0 => false
      | S m =>
          (fix f2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => true
             | S m0 => g2 a1 m0
             end
           with g2 (a1 n1 : nat) {struct n1} : bool :=
             match n1 with
             | 0 => false
             | S m0 => f2 a1 m0
             end
           for
           f2) a0 m
      end :=
      fun a0 n0 : nat =>
      match
        n0 as n1
        return
          (match n1 with
           | 0 => false
           | S m =>
               (fix f1 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => true
                  | S m0 => g1 a1 m0
                  end
                with g1 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => false
                  | S m0 => f1 a1 m0
                  end
                for
                f1) a0 m
           end =
           match n1 with
           | 0 => false
           | S m =>
               (fix f2 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => true
                  | S m0 => g2 a1 m0
                  end
                with g2 (a1 n2 : nat) {struct n2} : bool :=
                  match n2 with
                  | 0 => false
                  | S m0 => f2 a1 m0
                  end
                for
                f2) a0 m
           end)
      with
      | 0 => eq_refl
      | S n1 => (fun n2 : nat => H a0 n2) n1
      end in
    match
      n as n0
      return
        ((fix f1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g1 a0 m
            end
          with g1 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f1 a0 m
            end
          for
          g1) a n0 =
         (fix f2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => true
            | S m => g2 a0 m
            end
          with g2 (a0 n1 : nat) {struct n1} : bool :=
            match n1 with
            | 0 => false
            | S m => f2 a0 m
            end
          for
          g2) a n0)
    with
    | 0 => H1 a 0
    | S x0 => H1 a (S x0)
    end
  for
  H) x y)
*)
Qed.
*)

(*
    h is the number of mutual functions
    params is the inductive type parameters of T_{ki}
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
                  | C1 cargs1 => H a1 ... a{ki-1} (C1 params cargs1) a{ki+1} ... an
                  | ...
                  | Cm cargsm => H a1 ... a{ki-1} (Cm params cargsm) a{ki+1} ... an
                  end
              ...
          for IHj) b1 ... bn : Fj b1 ... bn = Gj b1 ... bn
*)

Ltac2 make_proof_term_for_letin (goal_type : constr) :=
  let (eq_type, lhs_fn, lhs_args, rhs_fn, rhs_args) :=
    match destEqApp_opt goal_type with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "goal is not equality"
    end
  in
  let (binder1, exp1, body1) :=
    match destLetIn_opt lhs_fn with
    | Some x => x
    | None => Control.backtrack_tactic_failure "LHS is not LetIn-expression"
    end
  in
  let (binder2, exp2, body2) :=
    match destLetIn_opt rhs_fn with
    | Some x => x
    | None => Control.backtrack_tactic_failure "RHS is not LetIn-expression"
    end
  in
  let eq := constr:(@Coq.Init.Logic.eq) in
  if Constr.equal exp1 exp2 then
    let lhs := mkApp body1 lhs_args in
    let rhs := mkApp body2 rhs_args in
    let subgoal_body := make_subgoal2 [(binder1, Some exp1)] (mkApp eq [|eq_type; lhs; rhs|]) in
    let proof_term := subgoal_body in
    proof_term
  else
    let exp_type := nf_of (Constr.Binder.type binder1) in
    let eq_exps := make_exteq exp_type exp1 exp2 in
    let eq_vars := make_exteq exp_type (mkRel 2) (mkRel 1) in
    let subgoal_exp := make_simple_subgoal eq_exps in
    let lhs := mkApp (Constr.Unsafe.liftn 2 1 body1) lhs_args in
    let rhs := mkApp (Constr.Unsafe.liftn 1 1 body2) rhs_args in
    let subgoal_body := make_subgoal2 [(binder1, Some exp1); (binder2, Some exp2); (Constr.Binder.make None eq_vars, None)]
                          (mkApp eq [|eq_type; lhs; rhs |]) in
    let proof_term :=
      mkApp
        subgoal_body
        [| subgoal_exp |]
    in
    proof_term.

Ltac2 Notation codegen_letin := Control.refine (fun () => make_proof_term_for_letin (Control.goal ())).

(* the binding expression is convertible.
Lemma L : forall (x w : nat),
    (let y := S x in Nat.add (y + 1)) w = (let z := S x in Nat.add (S z)) w.
Proof.
  intros.
  codegen_letin.
Show Proof. (* (fun x w : nat => let x0 := S x in ?Goal@{x0:=x}) *)
  rewrite<- plus_n_Sm.
  rewrite<- plus_n_O.
  reflexivity.
Qed.
*)

(* The binding expression is not a function.
Lemma L : forall (x : nat),
    (let y := S x in y + 1) = (let z := x + 1 in S z).
Proof.
  intros.
  codegen_letin.
Show Proof.
(*
(fun x : nat =>
 (let x0 := S x in let x1 := x + 1 in fun x2 : x0 = x1 => ?Goal0@{x0:=x; x:=x2})
   (?Goal : S x = x + 1))
*)
    rewrite<- plus_n_Sm.
    rewrite<- plus_n_O.
    reflexivity.
  rewrite<- plus_n_Sm.
  rewrite<- plus_n_O.
  rewrite x.
  reflexivity.
Qed.
*)

(* The binding expression is a function.
Lemma L : forall (x : nat),
    (let f y := S y in f x + 1) = (let g z := z + 1 in S (g x)).
Proof.
  intros.
  codegen_letin.
Show Proof.
(*
(fun x : nat =>
 (let x0 := fun y : nat => S y in
  let x1 := fun z : nat => z + 1 in
  fun x2 : forall y : nat, x0 y = x1 y => ?Goal0@{x0:=x; x:=x2})
   (?Goal : forall y : nat, S y = y + 1))
*)
    intros y.
    rewrite<- plus_n_Sm.
    rewrite<- plus_n_O.
    reflexivity.
  rewrite<- plus_n_Sm.
  rewrite<- plus_n_O.
  f_equal.
  now trivial with nocore.
Qed.
*)

(* The let-in expression is a function (partial application).
Lemma L : forall (x w : nat),
    (let y := S x in Nat.add (y + 1)) w = (let z := x + 1 in Nat.add (S z)) w.
Proof.
  intros.
  codegen_letin.
Show Proof.
(*
(fun x w : nat =>
 (let x0 := S x in let x1 := x + 1 in fun x2 : x0 = x1 => ?Goal0@{x0:=x; x:=x2})
   (?Goal : S x = x + 1))
*)
    rewrite<- plus_n_Sm.
    rewrite<- plus_n_O.
    reflexivity.
  rewrite<- plus_n_Sm.
  rewrite<- plus_n_O.
  rewrite x.
  reflexivity.
Qed.
*)

Ltac2 rec make_funext_subgoal (arg_binders_rev : binder list) (ty : constr) (t1 : constr) (t2 : constr) : constr :=
  let nbinders := List.length arg_binders_rev in
  let args := mkRel_descending nbinders nbinders in
  let lhs := mkApp t1 args in
  let rhs := mkApp t2 args in
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Prod b ty' =>
      mkApp constr:(@FunctionalExtensionality.functional_extensionality)
        [| Constr.Binder.type b; ty'; lhs; rhs;
           mkLambda b (make_funext_subgoal (b :: arg_binders_rev) ty' t1 t2) |]
  | _ =>
      let ctx := List.rev arg_binders_rev in
      snd (decompose_lambda (make_subgoal ctx (mkApp constr:(@Init.Logic.eq) [|ty; lhs; rhs|])))
  end.

Ltac2 make_proof_term_for_apparg (goal_type : constr) : constr :=
  let (eq_type, lhs_fn, lhs_args, rhs_fn, rhs_args) :=
    match destEqApp_opt goal_type with
    | Some x => x
    | _ => Control.backtrack_tactic_failure "goal is not equality"
    end
  in
  let fntype1 := nftype_of lhs_fn in
  let fntype2 := nftype_of rhs_fn in
  if Bool.neg (Constr.equal fntype1 fntype2) then
    Control.backtrack_tactic_failure "function type not equal"
  else
  (*let (_arg_binders, _rettype) := decompose_prod fntype1 in *)
  (*let argtypes := Array.map Constr.Binder.type (Array.of_list arg_binders) in (* assumes the types are closed *)*)
  let argtypes := Array.map nftype_of lhs_args in (* we want to use parametric inductive types for testing *)
  let n := Array.length lhs_args in
  Control.assert_valid_argument "number of arguments in LHS and RHS are different" (Int.equal n (Array.length rhs_args));
  let eq := constr:(@Coq.Init.Logic.eq) in
  let rec aux i :=
    if Int.equal i n then
      Control.backtrack_tactic_failure "different argument not found"
    else
    let a1 := Array.get lhs_args i in
    let a2 := Array.get rhs_args i in
    if Constr.equal a1 a2 then
      aux (Int.add i 1)
    else
    (let arg_type := Array.get argtypes i in
    let make_rhs_args x := Array.init n (fun j => if Int.equal j i then x else Array.get rhs_args j) in
    let make_goal x := mkApp eq [|eq_type; mkApp lhs_fn lhs_args; mkApp rhs_fn (make_rhs_args x)|] in
    let subgoal_arg := make_funext_subgoal [] arg_type a1 a2 in
    let subgoal_next := make_simple_subgoal (make_goal a1) in
    let eq_ind := constr:(@Coq.Init.Logic.eq_ind) in
    let pred := mkLambda (Constr.Binder.make (Some ident:(x)) arg_type) (make_goal (mkRel 1)) in
    let proof_term :=
      mkApp eq_ind [|arg_type; a1; pred; subgoal_next; a2; subgoal_arg|]
    in
    proof_term)
  in
  let proof_term := aux 0 in
  proof_term.

Ltac2 Notation codegen_apparg := Control.refine (fun () => make_proof_term_for_apparg (Control.goal ())).

(*
Lemma L (x y z : nat) (H : y = z) : x + y = x + z.
Proof.
  codegen_apparg.
Show Proof.
(*
(fun (x y z : nat) (H : y = z) =>
 eq_ind y (fun x0 : nat => x + y = x + x0) (?Goal0 : x + y = x + y) z ?Goal)
*)
    now apply H.
  now reflexivity.
Qed.
*)

(*
Definition app (f : nat -> nat) (x : nat) : nat := f x.
Lemma L (n : nat) : (let f x := x + 1 in app f n) = (let g x := S x in app g n).
Proof.
  intros.
  codegen_letin.
    intros.
    rewrite<- plus_n_Sm.
    rewrite<- plus_n_O.
    reflexivity.
  codegen_apparg.
Show Proof.
(*
(fun n : nat =>
 (let x := fun x : nat => x + 1 in
  let x0 := fun x0 : nat => S x0 in
  fun x1 : forall x1 : nat, x x1 = x0 x1 =>
  eq_ind x (fun x2 : nat -> nat => app x n = app x2 n) (?Goal0@{x:=x1} : app x n = app x n) x0
    (FunctionalExtensionality.functional_extensionality x x0
       (fun x2 : nat => ?Goal@{x2:=x1; x:=x2})))
   ((fun x : nat =>
     eq_ind (S (x + 0)) (fun n0 : nat => n0 = S x)
       (eq_ind x (fun n0 : nat => S n0 = S x) eq_refl (x + 0) (plus_n_O x))
       (x + 1) (plus_n_Sm x 0))
    :
    forall x : nat, x + 1 = S x))
*)
    now trivial with nocore.
  reflexivity.
Qed.
*)

(*
Definition app2 (f : nat -> nat -> nat) (x y : nat) : nat := f x y.
Lemma L (m n : nat) : (let f x y := x + 1 + y in app2 f m n) = (let g x y := S x + y in app2 g m n).
Proof.
  codegen_letin.
    intros.
    rewrite<- plus_n_Sm.
    rewrite<- plus_n_O.
    reflexivity.
  codegen_apparg.
Show Proof.
(*
(fun m n : nat =>
 (let x := fun x y : nat => x + 1 + y in
  let x0 := fun x0 y : nat => S x0 + y in
  fun x1 : forall x1 y : nat, x x1 y = x0 x1 y =>
  eq_ind x (fun x2 : nat -> nat -> nat => app2 x m n = app2 x2 m n)
    (?Goal0@{x:=x1} : app2 x m n = app2 x m n) x0
    (FunctionalExtensionality.functional_extensionality x x0
       (fun H : nat =>
        FunctionalExtensionality.functional_extensionality (x H) (x0 H)
          (fun H0 : nat => ?Goal@{x2:=x1; x3:=H; x:=H0}))))
   ((fun x y : nat =>
     eq_ind (S (x + 0)) (fun n0 : nat => n0 + y = S x + y)
       (eq_ind x (fun n0 : nat => S n0 + y = S x + y) eq_refl (x + 0) (plus_n_O x))
       (x + 1) (plus_n_Sm x 0))
    :
    forall x y : nat, x + 1 + y = S x + y))
*)
    now trivial with nocore.
  reflexivity.
Qed.
*)

(*
Goal forall a b,
  (fix add1 a b :=
    match a with
    | O => b
    | S a' => S (add1 a' b)
    end) a b =
  (fix add2 a b :=
    match a with
    | O => fun c => c
    | S a' => fun c => S (add2 a' c)
    end b) a b.
Proof.
  intros.
  codegen_fix.
  intros.
  codegen_matchapp.
    reflexivity.
  intros.
  codegen_apparg.
    now trivial with nocore.
  reflexivity.
Qed.
*)

(*
Goal forall a b,
  (fix add1 a b :=
    match a with
    | O => b
    | S a' => S (add1 a' b)
    end) a b =
  (fix add2 a b :=
    match a with
    | O => fun c => c
    | S a' => fun c => S (add2 a' c)
    end b) a b.
Proof.
  solve [
    repeat
      (intros;
      first [
        now reflexivity |
        now trivial with nocore |
        codegen_matchapp |
        codegen_fix |
        codegen_letin |
        codegen_apparg ]) ].
Qed.
*)

(*
Ltac2 codegen_applyhyp0 () := Std.trivial Std.Off [] (Some [ident:(nocore)]).
Ltac2 Notation codegen_applyhyp := solve [codegen_applyhyp0 ()].
*)
Ltac2 Notation "codegen_applyhyp" := solve [ trivial with nocore ].

(*
Goal 0 = 0.
intros.
Fail codegen_trivial.
reflexivity.
Qed.

Goal (forall (n : nat), n = n) -> 1 = 1.
intros.
codegen_trivial.
Qed.
*)

Ltac2 codegen_solve0 () : unit :=
  solve [
    repeat
      (intros;
      first [
        reflexivity |
        codegen_applyhyp |
        codegen_matchapp |
        codegen_fix |
        codegen_letin |
        codegen_apparg ]) ].

Ltac2 Notation codegen_solve := codegen_solve0 ().
