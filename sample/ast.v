(* intrinsically typed reflection of a Gallina subset supporting non-structural recursion *)

From mathcomp Require Import all_ssreflect.
Require Import ssrstr.
Require Import String.
Require Import Wf_nat.

(* normal (non-dependent) variables *)
Definition nenvtype : Type := seq Set.
Definition ntnth (nT : nenvtype) (i : nat) := nth unit nT i.

Definition nt_nil := @nil Set.
Definition nt_cons := @cons Set.

Definition nt_shift0 (T : Set) (nT : nenvtype) := T :: nT.
Definition nt_shift0s (Ts nT : seq Set) := Ts ++ nT.

Fixpoint nenviron (nT : nenvtype) : Set :=
  match nT with
  | [::] => unit
  | T :: nT' => prod T (nenviron nT')
  end.

Definition nenv_nil : nenviron [::] := tt.
Definition nenv_cons (T : Set) (v : T)
    (nT : nenvtype) (nenv : nenviron nT) : nenviron (T :: nT) :=
  (v, nenv).

Notation "[ 'nenv:' ]" := nenv_nil.
Notation "[ 'nenv:' x1 ; .. ; xn ]" :=
  (nenv_cons _ x1 _ (.. (nenv_cons _ xn _ nenv_nil) ..)).

Fixpoint nlookup (nT : nenvtype) (nenv : nenviron nT) (i : nat) :
    ntnth nT i :=
  match i with
  | 0 =>
    match nT as nT return nenviron nT -> ntnth nT 0 with
    | [::] => fun nenv => tt
    | T :: nT' => fun nenv => nenv.1
    end nenv
  | i'.+1 =>
    match nT as nT return nenviron nT -> ntnth nT i'.+1 with
    | [::] => fun nenv => tt
    | T :: nT' => fun nenv => nlookup nT' nenv.2 i'
      end nenv
  end.

Fixpoint nenv_cat (nt1 nt2 : nenvtype)
    (nenv1 : nenviron nt1) (nenv2 : nenviron nt2) : nenviron (nt1 ++ nt2) :=
  match nt1 return nenviron nt1 -> nenviron (nt1 ++ nt2) with
  | [::] => fun _ => nenv2
  | T :: nt1' => fun nenv1 => (nenv1.1, nenv_cat nt1' nt2 nenv1.2 nenv2)
  end nenv1.

Fixpoint nenv_take (nt1 nt2 : nenvtype)
    (nenv : nenviron (nt1 ++ nt2)) : nenviron nt1 :=
  match nt1 as nt1 return nenviron (nt1 ++ nt2) -> nenviron nt1 with
  | [::] => fun nenv => tt
  | v :: nt1' => fun nenv => (nenv.1, nenv_take nt1' nt2 nenv.2)
  end nenv.

Fixpoint nenv_drop (nt1 nt2 : nenvtype)
    (nenv : nenviron (nt1 ++ nt2)) : nenviron nt2 :=
  match nt1 return nenviron (nt1 ++ nt2) -> nenviron nt2 with
  | [::] => fun nenv => nenv
  | v :: nt1' => fun nenv => nenv_drop nt1' nt2 nenv.2
  end nenv.

Lemma nenv_take_cat (nt1 nt2 : nenvtype)
  (nenv1 : nenviron nt1) (nenv2 : nenviron nt2) :
  nenv_take nt1 nt2 (nenv_cat nt1 nt2 nenv1 nenv2) = nenv1.
Proof.
  elim: nt1 nenv1.
    by case.
  move=> T nt1 IH /= [] v nenv1 /=.
  by rewrite IH.
Defined.

Lemma nenv_drop_cat (nt1 nt2 : nenvtype)
  (nenv1 : nenviron nt1) (nenv2 : nenviron nt2) :
  nenv_drop nt1 nt2 (nenv_cat nt1 nt2 nenv1 nenv2) = nenv2.
Proof.
  elim: nt1 nenv1.
    by [].
  move=> T nt1 IH nenv1 /=.
  by apply IH.
Defined.

(* currying and uncurrying non-dependent arguments *)

(* curried function type *)
Fixpoint forall_ntT (nT : nenvtype)
    (f : nenviron nT -> Type) {struct nT} : Type :=
  match nT as nT return (nenviron nT -> Type) -> Type with
  | [::] => fun f => f nenv_nil
  | T :: nT' => fun f =>
    forall (v : T),
      let f' (nenv' : nenviron nT') := f (nenv_cons T v nT' nenv') in
      forall_ntT nT' f'
  end f.

Definition arrow_ntT (nT : nenvtype) (result : Type) : Type :=
  forall_ntT nT (fun _ => result).

Fixpoint uncurry_ntT (nT : nenvtype) (result : Type)
    (t : arrow_ntT nT result) (nenv : nenviron nT) : result :=
  match nT as nT return nenviron nT -> arrow_ntT nT result -> result with
  | [::] => fun nenv t => t
  | T :: nT' => fun nenv t =>
      uncurry_ntT nT' result (t nenv.1) nenv.2
  end nenv t.

(* curried function type *)
Fixpoint forall_ntS (nT : nenvtype)
    (f : nenviron nT -> Set) {struct nT} : Set :=
  match nT as nT return (nenviron nT -> Set) -> Set with
  | [::] => fun f => f nenv_nil
  | T :: nT' => fun f =>
    forall (v : T),
      let f' (nenv' : nenviron nT') := f (nenv_cons T v nT' nenv') in
      forall_ntS nT' f'
  end f.

Fixpoint uncurry_ntS (nT : nenvtype) (Dr : nenviron nT -> Set)
    (f : forall_ntS nT Dr)
    (nenv : nenviron nT) : Dr nenv :=
  match nT return
    forall (Dr : nenviron nT -> Set)
           (f : forall_ntS nT Dr)
           (nenv : nenviron nT), Dr nenv
  with
  | [::] => fun Dr f nenv =>
      let: tt := nenv in f
  | T :: nT' => fun Dr f nenv =>
      (* replacing v to nenv.1 and nenv' to nenv.2 causes a type error *)
      let: (v, nenv') := nenv in
      let Dr' (nenv'' : nenviron nT') :=
        Dr (nenv_cons T v nT' nenv'') in
      uncurry_ntS nT' Dr' (f v) nenv'
  end Dr f nenv.

(* curried function type *)
Definition arrow_ntS nT Tr := forall_ntS nT (fun _ => Tr).

Fixpoint uncurry_S (Ts : nenvtype) (Tv : Set)
    (f : arrow_ntS Ts Tv) (nenv : nenviron Ts) : Tv :=
  match Ts as Ts return arrow_ntS Ts Tv -> nenviron Ts -> Tv with
  | [::] => fun f nenv => f
  | T :: Ts' => fun f nenv => uncurry_S Ts' Tv (f nenv.1) nenv.2
  end f nenv.

Fixpoint curry_ntS (nT : seq Set) (Tr : nenviron nT -> Set)
    (f : forall (nenv : nenviron nT), Tr nenv) : forall_ntS nT Tr :=
  match nT as nT
      return forall (Tr : nenviron nT -> Set),
        (forall (nenv : nenviron nT), Tr nenv) -> forall_ntS nT Tr with
  | [::] => fun Tr f => f tt
  | T :: nT' => fun Tr f (a : T) => curry_ntS nT' _
     (fun (nenv' : nenviron nT') => f (a, nenv'))
  end Tr f.

Fixpoint forall_ntP (nT : nenvtype)
    (f : nenviron nT -> Prop) {struct nT} : Prop :=
  match nT as nT return (nenviron nT -> Prop) -> Prop with
  | [::] => fun f => f nenv_nil
  | T :: nT' => fun f =>
    forall (v : T),
      let f' (nenv' : nenviron nT') := f (nenv_cons T v nT' nenv') in
      forall_ntP nT' f'
  end f.

(* global environment *)

(* global environment type *)

(* global function takes non-dependent arguments and
   returns non-dependent value *)
Definition gty : Type := nenvtype * Set.

Definition gtyC (nT : nenvtype) (Tr : Set) : gty := (nT, Tr).

Definition nt4gty (G : gty) : nenvtype := G.1.
Definition Tr4gty (G : gty) : Set := G.2.

Definition gtype (G : gty) : Set :=
  let nT := nt4gty G in
  let Tr := Tr4gty G in
  forall (nenv : nenviron nT), Tr.

Definition default_G : gty := gtyC [::] unit.
Definition default_g : gtype default_G := fun _ => tt.

Definition genvtype : Type := seq (string * gty).

Fixpoint gtlookup (gT : genvtype) (name : string) : gty :=
  match gT with
  | [::] => default_G
  | name_G :: gT' => if name_G.1 == name then name_G.2 else gtlookup gT' name
  end.

Fixpoint genviron (gT : genvtype) : Set :=
  match gT with
  | [::] => unit
  | name_G :: gT' => prod (gtype name_G.2) (genviron gT')
  end.

Fixpoint glookup (gT : genvtype) (genv : genviron gT) (name : string) :
    gtype (gtlookup gT name) :=
  match gT as gT return genviron gT -> gtype (gtlookup gT name) with
  | [::] => fun genv => default_g
  | (n, G) :: gT' => fun genv =>
      let g := genv.1 in
      let genv' := genv.2 in
      if n == name as b return gtype (if b then G else gtlookup gT' name)
      then g else glookup gT' genv' name
  end genv.

Definition genv_nil : genviron [::] := tt.
Definition genv_cons (name : string) (G : gty) (g : gtype G)
    (gT : genvtype) (genv : genviron gT) : genviron ((name, G) :: gT) :=
   (g, genv).

Notation "[ 'genv:' ]" := genv_nil.
Notation "[ 'genv:' x1 ; .. ; xn ]" :=
  (genv_cons x1.1 _ x1.2 _ (.. (genv_cons xn.1 _ xn.2 _ genv_nil) ..)).

Fixpoint genv_cat (gt1 gt2 : genvtype)
  (genv1 : genviron gt1) (genv2 : genviron gt2) : genviron (gt1 ++ gt2) :=
  match gt1 as gt1 return genviron gt1 -> genviron (gt1 ++ gt2) with
  | [::] => fun genv1 => genv2
  | T :: gt1' => fun genv1 =>
      (genv1.1, genv_cat gt1' gt2 genv1.2 genv2)
  end genv1.

Definition uncurry (nT : nenvtype) (Tr : Set) (cf : arrow_ntS nT Tr) :=
  uncurry_S nT Tr cf : gtype (gtyC nT Tr).

Definition gtent (name : string) (nT : nenvtype) (Tr : Set) : (string * gty) :=
  (name, gtyC nT Tr).

Definition gent (name : string) (nT : nenvtype) (Tr : Set)
    (cf : arrow_ntS nT Tr) : (string * gtype (gtyC nT Tr)) :=
  (name, (uncurry nT Tr cf)).

(* beginning environment is empty *)
Definition GT0 : genvtype := [::].
Definition GENV0 : genviron GT0 := genv_nil.

(* types for several primitives *)
Definition GT1' := [::
  (gtent "tt" [::] unit);
  (gtent "true" [::] bool);
  (gtent "false" [::] bool);
  (gtent "O" [::] nat);
  (gtent "S" [:: nat] nat);
  (gtent "negb" [:: bool] bool);
  (gtent "ltn" [:: nat; nat] bool)
].
Definition GT1 := GT1' ++ GT0.

(* values for the primitives *)
Definition GENV1 : genviron GT1 := genv_cat GT1' GT0 [genv:
  (gent "tt" [::] _ tt);
  (gent "true" [::] _ true);
  (gent "false" [::] _ false);
  (gent "O" [::] _ 0);
  (gent "S" [:: nat] _ S);
  (gent "negb" [:: bool] _ negb);
  (gent "ltn" [:: nat; nat] _ ltn)
] GENV0.

(* closed-term Prop representation *)

Definition pty (gT : genvtype) (nT : nenvtype) : Type :=
  genviron gT -> nenviron nT -> Prop.
Definition ptype (gT : genvtype) (nT : nenvtype) (P : pty gT nT)
    (genv : genviron gT) (nenv : nenviron nT) : Prop :=
  P genv nenv.

Definition uncurry_pty (gT : genvtype) (nT : nenvtype)
    (f : genviron gT -> arrow_ntT nT Prop) : pty gT nT :=
  (fun (genv : genviron gT) => uncurry_ntT nT Prop (f genv)).

Definition pty_shift0 (gT : genvtype) (T : Set) (nT : nenvtype)
    (P : pty gT nT) (nT' := nt_shift0 T nT) : pty gT nT' :=
  fun (genv : genviron gT) (nenv' : nenviron nT') =>
    P genv nenv'.2.

Fixpoint pty_shift0s (gT : genvtype) (Ts nT : seq Set) (P : pty gT nT) :
    pty gT (Ts ++ nT) :=
  match Ts with
  | [::] => P
  | T :: Ts' => pty_shift0 gT T (Ts' ++ nT) (pty_shift0s gT Ts' nT P)
  end.

Definition penvtype (gT : genvtype) (nT : nenvtype) : Type := seq (pty gT nT).
Definition default_pty (gT : genvtype) (nT : nenvtype) : pty gT nT :=
  fun (genv : genviron gT) (nenv : nenviron nT) => True.
Definition ptnth (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT)
    (i : nat) : pty gT nT :=
  nth (default_pty gT nT) pT i.

Definition default_prf (gT : genvtype) (nT : nenvtype)
    (genv : genviron gT) (nenv : nenviron nT) :
    ptype gT nT (default_pty gT nT) genv nenv := I.

Definition pt_shift0 (gT : genvtype) (T : Set) (nT : nenvtype)
    (pT : penvtype gT nT) : penvtype gT (nt_shift0 T nT) :=
  map (pty_shift0 gT T nT) pT.

Fixpoint pt_shift0s (gT : genvtype) (Ts nT : nenvtype)
    (pT : penvtype gT nT) : penvtype gT (Ts ++ nT) :=
  match pT with
  | [::] => nil
  | P :: pT' => pty_shift0s gT Ts nT P :: pt_shift0s gT Ts nT pT'
  end.

Fixpoint penviron (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT)
    (genv : genviron gT) (nenv : nenviron nT) : Prop :=
  match pT with
  | [::] => True
  | P :: pT' => prod (ptype gT nT P genv nenv) (penviron gT nT pT' genv nenv)
  end.

Definition penv_nil (gT : genvtype) (nT : nenvtype)
    (genv : genviron gT) (nenv : nenviron nT) :
    penviron gT nT [::] genv nenv := I.
Definition penv_cons (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT)
    (P : pty gT nT) (genv : genviron gT) (nenv : nenviron nT)
    (prf : ptype gT nT P genv nenv) (penv : penviron gT nT pT genv nenv) :
    penviron gT nT (P :: pT) genv nenv :=
  (prf, penv).

Notation "[ 'penv:' ]" := (penv_nil _ _ _ _).
Notation "[ 'penv:' prf1 ; .. ; prfn ]" :=
  (let gT := _ in
  let nT := _ in
  let genv := _ in
  let nenv := _ in
  penv_cons gT nT _ _ genv nenv prf1
    (.. (penv_cons gT nT _ _ genv nenv prfn (penv_nil _ _ _ _)) ..)).

Fixpoint plookup (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT)
    (genv : genviron gT) (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv)
    (i : nat) : ptype gT nT (ptnth gT nT pT i) genv nenv :=
  match i with
  | 0 =>
    match pT as pT return
        penviron gT nT pT genv nenv ->
        ptype gT nT (ptnth gT nT pT 0) genv nenv with
    | [::] => fun penv =>
        default_prf gT nT genv nenv
    | P :: pT' => fun penv =>
        let prf := penv.1 in prf
    end penv
  | i'.+1 =>
    match pT as pT return
        penviron gT nT pT genv nenv ->
        ptype gT nT (ptnth gT nT pT i'.+1) genv nenv with
    | [::] => fun penv =>
        default_prf gT nT genv nenv
    | P :: pT' => fun penv =>
        let penv' := penv.2 in
        plookup gT nT pT' genv nenv penv' i'
    end penv
  end.

(* curried proof arguments function type *)
Fixpoint arrow_pt (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT) (Tr : Set)
    (genv : genviron gT) (nenv : nenviron nT) {struct pT} : Set :=
  match pT with
  | [::] => Tr
  | P :: pT' => ptype gT nT P genv nenv -> arrow_pt gT nT pT' Tr genv nenv
  end.

Fixpoint uncurry_pt (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT) (Tr : Set)
  (genv : genviron gT) (nenv : nenviron nT)
  (cf : arrow_pt gT nT pT Tr genv nenv)
  (penv : penviron gT nT pT genv nenv) {struct pT} : Tr :=
  match pT as pT
      return penviron gT nT pT genv nenv -> arrow_pt gT nT pT Tr genv nenv -> Tr
  with
  | [::] => fun penv cf => cf
  | T :: pT' => fun penv cf =>
      let prf := penv.1 in
      let penv' := penv.2 in
      uncurry_pt gT nT pT' Tr genv nenv (cf prf) penv'
  end penv cf.

(* curried normal and proof arguments function type *)
Definition forall_nt_pt (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT)
    (Tr : Set) : Set :=
  forall (genv : genviron gT), forall_ntS nT ((arrow_pt gT nT pT Tr) genv).

Definition uncurry_nt_pt (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT)
    (Tr : Set) (cf : forall_nt_pt gT nT pT Tr)
    (genv : genviron gT) (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv) : Tr :=
  let cf' := uncurry_ntS nT (fun nenv => arrow_pt gT nT pT Tr genv nenv) (cf genv) nenv in
  uncurry_pt gT nT pT Tr genv nenv cf' penv.

(* lenv, lemma environment *)

Definition lty gT : Type :=
  {nT:nenvtype &
   (penvtype gT nT * pty gT nT)%type}.

Definition ltyC (gT : genvtype) (nT : nenvtype) (pT : penvtype gT nT)
    (P : pty gT nT) : lty gT :=
  (existT (fun nT => (penvtype gT nT * pty gT nT)%type) nT (pT, P)).

Definition nt4lty (gT : genvtype) (H : lty gT) : nenvtype := projT1 H.
Definition pt4lty (gT : genvtype) (H : lty gT) : penvtype gT (nt4lty gT H) := (projT2 H).1.
Definition P4lty (gT : genvtype) (H : lty gT) : pty gT (nt4lty gT H) := (projT2 H).2.

Definition ltype (gT : genvtype) (H : lty gT) (genv : genviron gT) : Prop :=
  let nT := nt4lty gT H in
  let pT := pt4lty gT H in
  let P := P4lty gT H in
  forall (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv), P genv nenv.

Definition default_L (gT : genvtype) : lty gT :=
  let nT := [::] in let pT := [::] in
  ltyC gT nT pT (fun (genv : genviron gT) (nenv : nenviron nT) => True).
Definition default_l (gT : genvtype) (genv : genviron gT) :
    ltype gT (default_L gT) genv :=
  let nT := nt4lty gT (default_L gT) in
  let pT := pt4lty gT (default_L gT) in
  fun (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv) => I.

Definition lenvtype (gT : genvtype) : Type := seq (string * lty gT).

Fixpoint ltlookup (gT : genvtype) (lT : lenvtype gT) (name : string) : lty gT :=
  match lT with
  | [::] => default_L gT
  | name_H :: lT' => if name_H.1 == name then name_H.2 else ltlookup gT lT' name
  end.

Fixpoint lenviron (gT : genvtype) (lT : lenvtype gT) (genv : genviron gT) : Prop :=
  match lT with
  | [::] => True
  | name_H :: lT' => prod (ltype gT name_H.2 genv) (lenviron gT lT' genv)
  end.

Fixpoint llookup (gT : genvtype) (lT : lenvtype gT)
    (genv : genviron gT) (lenv : lenviron gT lT genv)
    (name : string) : ltype gT (ltlookup gT lT name) genv :=
  match lT as lT return lenviron gT lT genv -> ltype gT (ltlookup gT lT name) genv with
  | [::] => fun lenv => default_l gT genv
  | (n, H) :: lT' => fun lenv =>
      let h := lenv.1 in
      let lenv' := lenv.2 in
      if n == name as b return ltype gT (if b then H else ltlookup gT lT' name) genv
      then h else llookup gT lT' genv lenv' name
  end lenv.

Definition lenv_nil gT genv : lenviron gT [::] genv := I.
Definition lenv_cons gT genv (name : string) (H : lty gT) (h : ltype gT H genv)
    (lT : lenvtype gT) (lenv : lenviron gT lT genv) : lenviron gT ((name, H) :: lT) genv :=
   (h, lenv).

Notation "[ 'lenv:' ]" := (lenv_nil _ _).
Notation "[ 'lenv:' x1 ; .. ; xn ]" :=
  (lenv_cons _ _ x1.1 _ x1.2 _ (.. (lenv_cons _ _ xn.1 _ xn.2 _ (lenv_nil _)) ..)).

Fixpoint lenv_cat (gT : genvtype) (lt1 lt2 : lenvtype gT) (genv : genviron gT)
    (lenv1 : lenviron gT lt1 genv) (lenv2 : lenviron gT lt2 genv) :
    lenviron gT (lt1 ++ lt2) genv :=
  match lt1 as lt1 return lenviron gT lt1 genv -> lenviron gT (lt1 ++ lt2) genv with
  | [::] => fun lenv1 => lenv2
  | T :: lt1' => fun lenv1 =>
      (lenv1.1, lenv_cat gT lt1' lt2 genv lenv1.2 lenv2)
  end lenv1.

Definition lty_shift0 (name_G : string * gty) (gT : genvtype)
    (gT' := name_G::gT)
    (H : lty gT) : lty gT'.
Proof.
  exists (nt4lty gT H).
  split.
    apply (@map (pty gT (nt4lty gT H))).
      move=> prf genv'.
      by exact (prf genv'.2).
    by exact (pt4lty gT H).
  move=> genv'.
  by exact ((P4lty gT H) genv'.2).
Defined.

Definition lt_shift0 (name_G : string * gty) (gT : genvtype)
    (lT : lenvtype gT) : lenvtype (name_G::gT) :=
  map (fun name_H => (name_H.1, lty_shift0 name_G gT name_H.2)) lT.

(* renv, recursive function environment *)

Definition rty gT : Type :=
  {nT:nenvtype & option (pty gT nT)} * Set.

Definition rtyC (gT : genvtype) (nT : nenvtype)
    (Popt : option (pty gT nT)) (Tr : Set) : rty gT :=
  (existT (fun nT => option (pty gT nT)) nT Popt, Tr).

Definition nt4rty (gT : genvtype) (R : rty gT) : nenvtype := projT1 R.1.
Definition Popt4rty (gT : genvtype) (R : rty gT) : option (pty gT (nt4rty gT R)) := projT2 R.1.
Definition Tr4rty (gT : genvtype) (R : rty gT) : Set := R.2.

Definition Popttype (gT : genvtype) (nT : nenvtype)
    (Popt : option (pty gT nT))
    (genv : genviron gT) (nenv : nenviron nT) : Prop :=
  match Popt with
  | None => True
  | Some P => ptype gT nT P genv nenv
  end.

Definition rtype (gT : genvtype) (R : rty gT) (genv : genviron gT) : Set :=
  let nT := nt4rty gT R in
  let Popt := Popt4rty gT R in
  let Tr := Tr4rty gT R in
  forall (nenv : nenviron nT)
         (penv : Popttype gT nT Popt genv nenv),
         Tr.

Definition default_R (gT : genvtype) : rty gT :=
  rtyC gT [::] None unit.
Definition default_r (gT : genvtype) (genv : genviron gT) :
    rtype gT (default_R gT) genv :=
  fun _ _ => tt.

Definition renvtype (gT : genvtype) : Type := seq (string * rty gT).

Fixpoint rtlookup (gT : genvtype) (rT : renvtype gT) (name : string) : rty gT :=
  match rT with
  | [::] => default_R gT
  | name_R :: rT' => if name_R.1 == name then name_R.2 else rtlookup gT rT' name
  end.

Fixpoint renviron (gT : genvtype) (rT : renvtype gT) (genv : genviron gT) : Set :=
  match rT with
  | [::] => unit
  | name_R :: rT' => prod (rtype gT name_R.2 genv) (renviron gT rT' genv)
  end.

Fixpoint rlookup (gT : genvtype) (rT : renvtype gT)
    (genv : genviron gT) (renv : renviron gT rT genv)
    (name : string) : rtype gT (rtlookup gT rT name) genv :=
  match rT as rT return renviron gT rT genv -> rtype gT (rtlookup gT rT name) genv with
  | [::] => fun renv => default_r gT genv
  | (n, R) :: rT' => fun renv =>
      let r := renv.1 in
      let renv' := renv.2 in
      if n == name as b return rtype gT (if b then R else rtlookup gT rT' name) genv
      then r else rlookup gT rT' genv renv' name
  end renv.

Definition renv_nil gT genv : renviron gT [::] genv := tt.
Definition renv_cons gT genv (name : string) (R : rty gT) (r : rtype gT R genv)
    (rT : renvtype gT) (renv : renviron gT rT genv) : renviron gT ((name, R) :: rT) genv :=
   (r, renv).

Notation "[ 'renv:' ]" := (renv_nil _ _).
Notation "[ 'renv:' x1 ; .. ; xn ]" :=
  (renv_cons _ _ x1.1 _ x1.2 _ (.. (renv_cons _ _ xn.1 _ xn.2 _ (renv_nil _ _)) ..)).

Definition arrow_Popt (gT : genvtype) (nT : nenvtype)
    (Popt : option (pty gT nT)) (Tr : Set)
    (genv : genviron gT) (nenv : nenviron nT) : Set :=
  match Popt with
  | None => Tr
  | Some P => ptype gT nT P genv nenv -> Tr
  end.

Definition uncurry_Popt (gT : genvtype) (nT : nenvtype)
    (Popt : option (pty gT nT)) (Tr : Set)
    (genv : genviron gT) (nenv : nenviron nT)
    (cf : arrow_Popt gT nT Popt Tr genv nenv)
    (prf : Popttype gT nT Popt genv nenv) : Tr :=
  match Popt as Popt
      return Popttype gT nT Popt genv nenv -> arrow_Popt gT nT Popt Tr genv nenv -> Tr
  with
  | None => fun prf cf => cf
  | Some P => fun prf cf => cf prf
  end prf cf.

Definition forall_nt_Popt (gT : genvtype) (nT : nenvtype)
    (Popt : option (pty gT nT)) (Tr : Set)
    (genv : genviron gT) : Set :=
  forall_ntS nT (arrow_Popt gT nT Popt Tr genv).

Definition uncurry_nt_Popt (gT : genvtype) (nT : nenvtype)
    (Popt : option (pty gT nT)) (Tr : Set)
    (genv : genviron gT)
    (cf : forall_nt_Popt gT nT Popt Tr genv)
    (nenv : nenviron nT) (prf : Popttype gT nT Popt genv nenv) : Tr :=
    let cf' := uncurry_ntS nT (fun nenv => arrow_Popt gT nT Popt Tr genv nenv) cf nenv in
    uncurry_Popt gT nT Popt Tr genv nenv cf' prf.

Definition oapp {A B : Type} (f : A -> B) (v : option A) : option B :=
  match v with
  | None => None
  | Some v => Some (f v)
  end.

Definition uncurryR (gT : genvtype) (nT : nenvtype)
    (cPopt : option (genviron gT -> arrow_ntT nT Prop))
    (Tr : Set) (Popt := oapp (uncurry_pty gT nT) cPopt)
    (genv : genviron gT)
    (cf : forall_nt_Popt gT nT Popt Tr genv) :
    rtype gT (rtyC gT nT Popt Tr) genv :=
  uncurry_nt_Popt gT nT Popt Tr genv cf.

Definition rtent (gT : genvtype) (name : string) (nT : nenvtype)
    (cPopt : option (genviron gT -> arrow_ntT nT Prop))
    (Tr : Set) : (string * rty gT) :=
  (name, rtyC gT nT (oapp (uncurry_pty gT nT) cPopt) Tr).

Definition rent (gT : genvtype) (name : string) (nT : nenvtype)
    (cPopt : option (genviron gT -> arrow_ntT nT Prop))
    (Tr : Set) (Popt := oapp (uncurry_pty gT nT) cPopt)
    (genv : genviron gT)
    (cf : forall_nt_Popt gT nT Popt Tr genv) :
    (string * rtype gT (rtyC gT nT Popt Tr) genv) :=
  (name, (uncurryR gT nT cPopt Tr genv cf)).

(* utilitiy functions for exp and eval *)

Fixpoint transplant_nenv (nT : nenvtype) (nargs : seq nat)
    (nenv : nenviron nT) (nT' := map (ntnth nT) nargs)
    {struct nargs} : nenviron nT' :=
  match nargs as nargs return nenviron (map (ntnth nT) nargs) with
  | [::] => tt
  | narg :: nargs' =>
      (nlookup nT nenv narg, transplant_nenv nT nargs' nenv)
  end.

Definition transplant_pty (gT : genvtype) (nT : nenvtype)
    (nargs : seq nat)
    (nT' := map (ntnth nT) nargs)
    (t' : pty gT nT') : pty gT nT :=
  fun (genv : genviron gT) (nenv : nenviron nT) =>
  t' genv (transplant_nenv nT nargs nenv).

Definition transplant_pt (gT : genvtype) (nT : nenvtype)
    (nargs : seq nat)
    (nT' := map (ntnth nT) nargs)
    (pT' : penvtype gT nT') : penvtype gT nT :=
  map (transplant_pty gT nT nargs) pT'.

Record cstrT (Tv : Set) : Type := CstrT {
  cstr_Tms : seq Set;
  cstr_cstr : arrow_ntS cstr_Tms Tv;
}.

Definition Tms4Ct (Tv : Set) (Ct : cstrT Tv) : seq Set :=
  let: CstrT Tms cstr := Ct in Tms.

Definition cstr4Ct (Tv : Set) (Ct : cstrT Tv) : arrow_ntS (Tms4Ct Tv Ct) Tv :=
  let: CstrT Tms cstr := Ct in cstr.

Definition nmatcher_branch_type (Tv : Set) (Ct : cstrT Tv) (Tr : Set) : Set :=
  arrow_ntS (Tms4Ct Tv Ct) Tr.

Fixpoint curry_nmatch_branch' (Ts : seq Set) (Tr : Set)
    (branch : nenviron Ts -> Tr) : arrow_ntS Ts Tr :=
  match Ts as Ts return
      (nenviron Ts -> Tr) -> arrow_ntS Ts Tr with
  | [::] => fun branch => branch tt
  | T :: Ts' => fun branch (v : T) =>
    curry_nmatch_branch' Ts' Tr (fun nenv => branch (v, nenv))
  end branch.

Definition curry_nmatch_branch (Tv : Set) (Ct : cstrT Tv) (Tr : Set)
    (Ts := Tms4Ct Tv Ct)
    (branch : nenviron Ts -> Tr) : nmatcher_branch_type Tv Ct Tr :=
  curry_nmatch_branch' Ts Tr branch.

Definition nmatcher_branch_types Tv Cts Tr :=
  [seq nmatcher_branch_type Tv Ct Tr | Ct <- Cts].

Definition nmatcher_type Tv Cts Tr :=
  arrow_ntS (nmatcher_branch_types Tv Cts Tr) Tr.

(* c : constructor *)

Definition dmatcher_branch_type (Tv : Set) (Ct : cstrT Tv) (Tr : Set)  (v : Tv) : Set :=
  let Tms := Tms4Ct Tv Ct in
  let cstr := cstr4Ct Tv Ct in
  forall_ntS Tms (fun (nenv : nenviron Tms) =>
    uncurry_S Tms Tv cstr nenv = v -> Tr).

Definition dmatcher_branch_types Tv Cts Tr v :=
  [seq dmatcher_branch_type Tv Ct Tr v | Ct <- Cts].

Definition dmatcher_type (Tv : Set) (Cts : seq (cstrT Tv)) (Tr : Set) (v : Tv) :=
  arrow_ntS (dmatcher_branch_types Tv Cts Tr v) Tr.

Definition dmatch_pty (gT : genvtype) (nT : nenvtype)
    (i : nat) (Tv := ntnth nT i)
    (Ts : seq Set) (nT' := nt_shift0s Ts nT)
    (c : arrow_ntS Ts Tv) : pty gT nT' :=
  fun (genv : genviron gT) (nenv : nenviron nT') =>
    let v := nlookup nT (nenv_drop Ts nT nenv) i in
    let v' := uncurry_S Ts Tv c (nenv_take Ts nT nenv) in
    v' = v.

Definition curry_dmatch_branch
    (Tv : Set) (Ct : cstrT Tv) (Tr : Set) (v : Tv)
    (Ts := Tms4Ct Tv Ct) (c := cstr4Ct Tv Ct)
    (branch : forall (fields : nenviron Ts),
      uncurry_S Ts Tv c fields = v -> Tr) :
    dmatcher_branch_type Tv Ct Tr v :=
  curry_ntS Ts (fun fields => uncurry_S Ts Tv c fields = v -> Tr) branch.

Definition matcher_branch_proofelim (Tv : Set) (Ct : cstrT Tv)
    (Tr : Set) (v : Tv)
    (dbranch : dmatcher_branch_type Tv Ct Tr v)
    (nbranch : nmatcher_branch_type Tv Ct Tr) : Prop :=
    let Tms : seq Set := Tms4Ct Tv Ct in
    let c : arrow_ntS Tms Tv := cstr4Ct Tv Ct in
    forall_ntP Tms (fun (members : nenviron Tms) =>
    forall (prf : uncurry_S Tms Tv c members = v),
    uncurry_ntS Tms (fun members => uncurry_S Tms Tv c members = v -> Tr)
      dbranch members prf =
    uncurry_S Tms Tr nbranch members).

Fixpoint matcher_proofelims_type (Tv : Set) (constructors: seq (cstrT Tv))
    (Tr : Set) (v : Tv)
    (nbranches : nenviron [seq nmatcher_branch_type Tv Ct Tr | Ct <- constructors])
    (dbranches : nenviron [seq dmatcher_branch_type Tv Ct Tr v | Ct <- constructors]) :=
  match constructors return
    nenviron [seq nmatcher_branch_type Tv Ct Tr | Ct <- constructors] ->
    nenviron [seq dmatcher_branch_type Tv Ct Tr v | Ct <- constructors] ->
    Prop
  with
  | [::] => fun _ _ => True
  | Ct :: constructors' => fun nbranches dbranches =>
      let: (nbranch, nbranches') := nbranches in
      let: (dbranch, dbranches') := dbranches in
      matcher_branch_proofelim Tv Ct Tr v dbranch nbranch /\
      matcher_proofelims_type Tv constructors' Tr v nbranches' dbranches'
  end nbranches dbranches.

Record Matcher (Tv : Set) (Cts : seq (cstrT Tv)) : Type := mkMatcher {
  nmatcher (Tr : Set) (v : Tv) :
    arrow_ntS (nmatcher_branch_types Tv Cts Tr) Tr;
  dmatcher (Tr : Set) (v : Tv) :
    arrow_ntS (dmatcher_branch_types Tv Cts Tr v) Tr;
  proofelim (Tr : Set) (v : Tv) :
    forall_ntP (dmatcher_branch_types Tv Cts Tr v) (fun dbranches =>
    forall_ntP (nmatcher_branch_types Tv Cts Tr) (fun nbranches =>
    matcher_proofelims_type Tv Cts Tr v nbranches dbranches ->
    uncurry_S (dmatcher_branch_types Tv Cts Tr v) Tr
      (dmatcher Tr v) dbranches =
    uncurry_S (nmatcher_branch_types Tv Cts Tr) Tr
      (nmatcher Tr v) nbranches))
}.

(* expression in GADT-like style

  f : global function name
  r : recursive function name
  h : proof function name
  C : constructor
  v : normal (non-dependent) variable
  p : proof variable (can depend on normal variables)

  B : recursive function body name
  D : decreasing proof argument initializer
      (typically "lt_wf v" for "Acc lt v")
  i : decreasing argument index

    v and p are represented as de Bruijn index.

  program = def*

  def = f v* := exp                     (* non-recursive function *)
      | f v* := fix r (r := B)+ [D]     (* recursive function *)
      | B r+ v* i := exp                (* recursive function body, Set decreasing argument *)
      | B r+ v* p := exp                (* recursive function body, Prop decreasing argument *)

    The recursive function, f, doesn't take the decreasing argument for
    non-structural argument, p.
    It is generated from D.

  exp = v
      | app
      | rapp
      | nmatch v with | C v* => exp | ... end
      | dmatch v with | C v* p => exp | ... end
      | leta v p := app in exp
      | letr v := rapp in exp
      | letp p := proof in exp
      | letn v := v with | C v* => exp | ... end
      | letd v := v with | C v* p => exp | ... end

  app = f v*
  rapp = r v* [p]
  proof = h v* p*

Semantics:

  There are 5 environments:
  - gT/genv : global environment
  - lT/lenv : global lemma environment
  - rT/renv : recursive function environment
  - nT/nenv : normal (non-dependent) environment
  - pT/penv : proof environment

  leta binds a new variable v0 in nenv to the value of (f v1...) and
  a new variable in penv to the proof of (v0 = f v1...).
  letr binds a new variable v0 in nenv to the value of (r v1... [p]).
  letp binds a new variable p0 in penv to the value of (h v1... p1...).

*)

Inductive papp_exp (gT : genvtype) (lT : lenvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) (P : pty gT nT) : Type :=
| papp_expC : forall (name : string) (nargs pargs : seq nat)
    (nT' := map (ntnth nT) nargs) (pT' : penvtype gT nT')
    (P' : pty gT nT')
    (H1 : ltyC gT nT' pT' P' = ltlookup gT lT name)
    (H2 : transplant_pt gT nT nargs pT' = map (ptnth gT nT pT) pargs)
    (H3 : transplant_pty gT nT nargs P' = P),
    papp_exp gT lT nT pT P.

Definition eval_papp (gT : genvtype) (lT : lenvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) (P : pty gT nT)
    (genv : genviron gT) (lenv : lenviron gT lT genv)
    (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv)
    (e : papp_exp gT lT nT pT P) : ptype gT nT P genv nenv.
Proof.
  refine (
  match e in (papp_exp _ _ _ _ _) return (ptype gT nT P genv nenv) with
  | papp_expC name nargs pargs pT' P' H1 H2 H3 => _
  end).
  clear e.
  rename l into nT'.
  set prf := llookup gT lT genv lenv name.
  rewrite<- H1 in prf.
  set nenv' : nenviron nT' := transplant_nenv nT nargs nenv.
  specialize (prf nenv').
  rewrite /pt4lty /P4lty /= in prf.
  rewrite /ptype.
  rewrite -H3 /transplant_pty /=.
  clear H1 H3 P.
  rename P' into P.
  elim: pargs pT' H2 prf.
    move=> /= pT' H2 prf.
    rewrite /transplant_pt in H2.
    case: pT' H2 prf => [H2 prf|]; last by [].
    by apply prf.
  move=> parg pargs IH pT' H2 prf.
  simpl in H2.
  rewrite /transplant_pt in H2.
  case: pT' IH H2 prf => [|P' pT' IH H2 prf]; first by [].
  simpl in H2.
  simpl in prf.
  case: H2 => H3 H2.
  apply (IH pT').
    by apply H2.
  clear IH.
  move=> penv'.
  apply prf.
  split.
    clear H2.
    rewrite /transplant_pty in H3.
    rewrite /ptype /=.
    rewrite /nenv'.
    apply (@f_equal _ _ (fun f => f genv nenv)) in H3.
    rewrite H3.
    by apply (plookup gT nT pT genv nenv penv parg).
  by apply penv'.
Defined.

Inductive rapp_exp (gT : genvtype) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) (Tr : Set) : Type :=
| rapp_expC : forall (name : string) (nargs : seq nat) (pargopt : option nat)
    (nT' := map (ntnth nT) nargs) (Popt : option (pty gT nT'))
    (H1 : rtyC gT nT' Popt Tr = rtlookup gT rT name)
    (H2 : match Popt with None => None | Some P => Some (transplant_pty gT nT nargs P) end =
          match pargopt with None => None | Some parg => Some (ptnth gT nT pT parg) end),
    rapp_exp gT rT nT pT Tr.

Definition eval_rapp (gT : genvtype) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) (Tr : Set)
    (genv : genviron gT) (renv : renviron gT rT genv)
    (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv)
    (re : rapp_exp gT rT nT pT Tr) : Tr.
Proof.
  refine (
  match re with
  | rapp_expC name nargs pargopt Popt H1 H2 => _
  end).
  clear re.
  rename l into nT'.
  set f := rlookup gT rT genv renv name.
  rewrite<- H1 in f.
  set nenv' : nenviron nT' := transplant_nenv nT nargs nenv.
  specialize (f nenv').
  rewrite /nt4rty /Popt4rty /Tr4rty /Popttype /ptype /= in f.
  clear H1.
  apply: f.
  case: Popt H2; last by [].
  move=> P.
  case: pargopt; last by [].
  move=> parg.
  case=> H.
  rewrite (_ : P genv nenv' = ptnth gT nT pT parg genv nenv); last by rewrite -H.
  by exact (plookup gT nT pT genv nenv penv parg).
Defined.

Definition leta_eq (gT : genvtype) (nT : nenvtype)
    (Tv : Set) (name : string) (nargs : seq nat)
    (nT' := map (ntnth nT) nargs)
    (H : gtyC nT' Tv = gtlookup gT name) : pty gT (Tv :: nT) :=
  fun genv nenv =>
    let f := eq_rec_r gtype (glookup gT genv name) H in
    nenv.1 = f (transplant_nenv nT nargs nenv.2).

Inductive exp (gT : genvtype) (lT : lenvtype gT) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) : Set -> Type :=
| var : forall (i : nat), exp gT lT rT nT pT (ntnth nT i)
| app : forall (Tr : Set) (name : string) (nargs : seq nat)
    (nT' := map (ntnth nT) nargs)
    (H : gtyC nT' Tr = gtlookup gT name),
    exp gT lT rT nT pT Tr
| leta : forall (Tv Tr : Set) (name : string) (nargs : seq nat)
    (nT' := map (ntnth nT) nargs)
    (H : gtyC nT' Tv = gtlookup gT name)
    (Peq : pty gT (Tv :: nT) := leta_eq gT nT Tv name nargs H),
    exp gT lT rT (Tv :: nT) (Peq :: pt_shift0 gT Tv nT pT) Tr ->
    exp gT lT rT nT pT Tr
| rappC : forall (Tr : Set),
    rapp_exp gT rT nT pT Tr ->
    exp gT lT rT nT pT Tr
| letrC : forall (Tv Tr : Set),
    rapp_exp gT rT nT pT Tv ->
    exp gT lT rT (Tv :: nT) (pt_shift0 gT Tv nT pT) Tr ->
    exp gT lT rT nT pT Tr
| letpC : forall (Tr : Set) (P : pty gT nT),
    papp_exp gT lT nT pT P ->
    exp gT lT rT nT (P :: pT) Tr ->
    exp gT lT rT nT pT Tr
| nmatch : forall (Tr : Set) (i : nat) (Tv := ntnth nT i),
    nmatch_exp gT lT rT nT pT Tv Tr [::] ->
    exp gT lT rT nT pT Tr
| letn : forall (Tv2 Tr : Set) (i : nat) (Tv1 := ntnth nT i),
    nmatch_exp gT lT rT nT pT Tv1 Tv2 [::] ->
    exp gT lT rT (Tv2 :: nT) (pt_shift0 gT Tv2 nT pT) Tr ->
    exp gT lT rT nT pT Tr
| dmatch : forall (Tr : Set) (i : nat),
    dmatch_exp gT lT rT nT pT i Tr [::] ->
    exp gT lT rT nT pT Tr
| letd : forall (Tv2 Tr : Set) (i : nat),
    dmatch_exp gT lT rT nT pT i Tv2 [::] ->
    exp gT lT rT (Tv2 :: nT) (pt_shift0 gT Tv2 nT pT) Tr ->
    exp gT lT rT nT pT Tr
with nmatch_exp (gT : genvtype) (lT : lenvtype gT) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) :
    forall (Tv : Set) (Tr : Set) (Cts : seq (cstrT Tv)), Type :=
| nmatch_nil : forall (Tv Tr : Set) (Cts : seq (cstrT Tv)),
    Matcher Tv Cts ->
    nmatch_exp gT lT rT nT pT Tv Tr Cts
| nmatch_cons : forall (Tv Tr : Set) (Ct : cstrT Tv) (Cts : seq (cstrT Tv))
    (Ts : seq Set := Tms4Ct Tv Ct),
    let nT' := nt_shift0s Ts nT in
    let pT' := pt_shift0s gT Ts nT pT in
    exp gT lT rT nT' pT' Tr ->
    nmatch_exp gT lT rT nT pT Tv Tr (Ct :: Cts) ->
    nmatch_exp gT lT rT nT pT Tv Tr Cts
with dmatch_exp (gT : genvtype) (lT : lenvtype gT) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) :
    forall (i:nat) (Tv := ntnth nT i) (Tr : Set)
    (Cts : seq (cstrT Tv)), Type :=
| dmatch_nil : forall (i : nat) (Tv := ntnth nT i)
    (Tr : Set) (Cts : seq (cstrT Tv)),
    Matcher Tv Cts ->
    dmatch_exp gT lT rT nT pT i Tr Cts
| dmatch_cons : forall (i : nat) (Tv := ntnth nT i)
    (Tr : Set) (Ct : cstrT Tv) (Cts : seq (cstrT Tv))
    (Ts : seq Set := Tms4Ct Tv Ct)
    (c : arrow_ntS Ts Tv := cstr4Ct Tv Ct),
    let nT' := nt_shift0s Ts nT in
    let pT' := (dmatch_pty gT nT i Ts c) :: (pt_shift0s gT Ts nT pT) in
    exp gT lT rT nT' pT' Tr ->
    dmatch_exp gT lT rT nT pT i Tr (Ct :: Cts) ->
    dmatch_exp gT lT rT nT pT i Tr Cts.

Definition rapp gT lT rT nT pT Tr name nargs pargopt Popt H1 H2 :=
  rappC gT lT rT nT pT Tr (rapp_expC gT rT nT pT Tr name nargs pargopt Popt H1 H2).

Definition letr gT lT rT nT pT Tv Tr name nargs pargopt Popt H1 H2 body :=
  letrC gT lT rT nT pT Tv Tr (rapp_expC gT rT nT pT Tv name nargs pargopt Popt H1 H2) body.

Definition letp gT lT rT nT pT Tr name P nargs pargs pT' P' H1 H2 H3 body :=
  letpC gT lT rT nT pT Tr P (papp_expC gT lT nT pT P name nargs pargs pT' P' H1 H2 H3) body.

(* matcher functions for basic types *)

Definition Empty_set_nmatcher (Tr : Set) (v : Empty_set) : Tr :=
  match v with
  end.

Definition Empty_set_dmatcher (Tr : Set) (v : Empty_set) : Tr :=
  match v as v' return v' = v -> Tr with
  end erefl.

Lemma Empty_set_matcher_proofelim (Tr : Set) (v : Empty_set) :
  True ->
  Empty_set_dmatcher Tr v =
  Empty_set_nmatcher Tr v.
Proof.
  by [].
Defined.

Definition Empty_set_matcher := mkMatcher Empty_set [::]
  Empty_set_nmatcher Empty_set_dmatcher Empty_set_matcher_proofelim.

Definition unit_tt := CstrT unit [::] tt.

Definition unit_nmatcher (Tr : Set) (v : unit)
    (branch_tt : Tr) : Tr :=
  match v with
  | tt => branch_tt
  end.

Definition unit_dmatcher (Tr : Set) (v : unit)
    (branch_tt : tt = v -> Tr) : Tr :=
  match v as v' return v' = v -> Tr with
  | tt => branch_tt
  end erefl.

Lemma unit_matcher_proofelim (Tr : Set) (v : unit)
  (dbranch_tt : tt = v -> Tr)
  (nbranch_tt : Tr) :
  ((forall (prf : tt = v), dbranch_tt prf = nbranch_tt) /\
   True) ->
  unit_dmatcher Tr v dbranch_tt =
  unit_nmatcher Tr v nbranch_tt.
Proof.
  case: v dbranch_tt nbranch_tt.
  move=> dtt ntt [] HO _ /=.
  by apply HO.
Defined.

Definition unit_matcher := mkMatcher unit [:: unit_tt]
  unit_nmatcher unit_dmatcher unit_matcher_proofelim.

Definition bool_true := CstrT bool [::] true.
Definition bool_false := CstrT bool [::] false.

Definition bool_nmatcher (Tr : Set) (v : bool)
    (branch_true : Tr) (branch_false : Tr) : Tr :=
  match v with
  | true => branch_true
  | false => branch_false
  end.

Definition bool_dmatcher (Tr : Set) (v : bool)
    (branch_true : true = v -> Tr) (branch_false : false = v -> Tr) : Tr :=
  match v as v' return v' = v -> Tr with
  | true => branch_true
  | false => branch_false
  end erefl.

Lemma bool_matcher_proofelim (Tr : Set) (v : bool)
  (dbranch_true : true = v -> Tr) (dbranch_false : false = v -> Tr)
  (nbranch_true : Tr) (nbranch_false : Tr) :
  ((forall (prf : true = v), dbranch_true prf = nbranch_true) /\
   (forall (prf : false = v), dbranch_false prf = nbranch_false) /\
   True) ->
  bool_dmatcher Tr v dbranch_true dbranch_false =
  bool_nmatcher Tr v nbranch_true nbranch_false.
Proof.
  case: v dbranch_true dbranch_false nbranch_true nbranch_false =>
      dT dF nT nF [] HT [] HF _ /=.
    by apply HT.
  by apply HF.
Defined.

Definition bool_matcher := mkMatcher bool [:: bool_true; bool_false]
  bool_nmatcher bool_dmatcher bool_matcher_proofelim.

Definition nat_O := CstrT nat [::] O.
Definition nat_S := CstrT nat [:: nat] S.

Definition nat_nmatcher (Tr : Set) (v : nat)
    (branch_O : Tr) (branch_S : nat -> Tr) : Tr :=
  match v with
  | O => branch_O
  | S n => branch_S n
  end.

Definition nat_dmatcher (Tr : Set) (v : nat)
    (branch_O : O = v -> Tr) (branch_S : forall n, S n = v -> Tr) : Tr :=
  match v as v' return v' = v -> Tr with
  | O => branch_O
  | S n => branch_S n
  end erefl.

Lemma nat_matcher_proofelim (Tr : Set) (v : nat)
  (dbranch_O : O = v -> Tr) (dbranch_S : forall n, S n = v -> Tr)
  (nbranch_O : Tr) (nbranch_S : nat -> Tr) :
  ((forall (prf : O = v), dbranch_O prf = nbranch_O) /\
   (forall (n : nat) (prf : S n = v), dbranch_S n prf = nbranch_S n) /\
   True) ->
  nat_dmatcher Tr v dbranch_O dbranch_S =
  nat_nmatcher Tr v nbranch_O nbranch_S.
Proof.
  case: v dbranch_O dbranch_S nbranch_O nbranch_S =>
      [|n] dO dS nO nS [] HO [] HS _ /=.
    by apply HO.
  by apply HS.
Defined.

Definition nat_matcher := mkMatcher nat [:: nat_O; nat_S]
  nat_nmatcher nat_dmatcher nat_matcher_proofelim.

(* evaluation (denotation) *)

Lemma penviron_shift0
  (gT : genvtype)
  (nT : nenvtype)
  (pT : penvtype gT nT)
  (genv : genviron gT)
  (nenv : nenviron nT)
  (Tv : Set)
  (v : Tv)
  (nT' := Tv :: nT)
  (nenv' := nenv_cons Tv v nT nenv : nenviron (Tv :: nT)) :
  penviron gT nT' (pt_shift0 gT Tv nT pT) genv nenv' = penviron gT nT pT genv nenv.
Proof.
  elim: pT.
    by [].
  move=> /= P pT' IH.
  apply (@f_equal Prop _ (fun x => (ptype gT nT P genv nenv * x)%type)).
  by apply IH.
Defined.

Lemma pt_shift0s_empty gT nT pT : pt_shift0s gT [::] nT pT = pT.
Proof.
  elim: pT.
    by [].
  move=> P pT IH /=.
  by rewrite IH.
Defined.

Lemma ptype_shift0s (gT : genvtype) (nt1 nt2 : nenvtype) (P : pty gT nt2)
    (genv : genviron gT) (nenv1 : nenviron nt1) (nenv2 : nenviron nt2) :
  ptype gT (nt1 ++ nt2) (pty_shift0s gT nt1 nt2 P) genv (nenv_cat nt1 nt2 nenv1 nenv2) =
  ptype gT nt2 P genv nenv2.
Proof.
  rewrite /ptype.
  elim: nt1 nenv1.
    by [].
  move=> T nt1 IH nenv1 /=.
  by rewrite /pty_shift0 IH.
Defined.

Lemma penviron_shift0s
  (gT : genvtype)
  (nt1 nt2 : nenvtype)
  (pT : penvtype gT nt2)
  (genv : genviron gT)
  (nenv1 : nenviron nt1)
  (nenv2 : nenviron nt2)
  (nT' := nt1 ++ nt2)
  (nenv' := nenv_cat nt1 nt2 nenv1 nenv2) :
  penviron gT nT' (pt_shift0s gT nt1 nt2 pT) genv nenv' = penviron gT nt2 pT genv nenv2.
Proof.
  elim: pT.
    by [].
  move=> P pT IH /=.
  rewrite IH.
  apply (@f_equal Prop _ (fun x => (x * penviron gT nt2 pT genv nenv2)%type)).
  by rewrite ptype_shift0s.
Defined.

Lemma penviron_dmatch_pty (gT : genvtype) (Ts nT : nenvtype)
  (genv : genviron gT)
  (nenv : nenviron nT)
  (fields : nenviron Ts)
  (pT : penvtype gT nT)
  (i : nat)
  (Tv := ntnth nT i)
  (v := nlookup nT nenv i)
  (c : arrow_ntS Ts Tv) :
  penviron gT (Ts ++ nT)
    (dmatch_pty gT nT i Ts c :: pt_shift0s gT Ts nT pT)
    genv (nenv_cat Ts nT fields nenv) =
  ((uncurry_S Ts Tv c fields = v) *
   penviron gT (Ts ++ nT) (pt_shift0s gT Ts nT pT)
     genv (nenv_cat Ts nT fields nenv))%type.
Proof.
  simpl.
  apply (@f_equal Prop Prop
    (fun x =>
      (x * penviron gT (Ts ++ nT) (pt_shift0s gT Ts nT pT)
        genv (nenv_cat Ts nT fields nenv))%type)).
  rewrite /ptype /dmatch_pty /v /=.
  by rewrite nenv_drop_cat nenv_take_cat.
Defined.

Definition eval_app (gT : genvtype)
    (nT : nenvtype) (Tr : Set)
    (genv : genviron gT) (nenv : nenviron nT)
    (name : string) (nargs : seq nat) (nT' := map (ntnth nT) nargs)
    (H : gtyC nT' Tr = gtlookup gT name) : Tr :=
  let f := glookup gT genv name in
  let f' := eq_rec_r gtype f H in
  f' (transplant_nenv nT nargs nenv).

Fixpoint eval (gT : genvtype) (lT : lenvtype gT) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT) (Tr : Set)
    (genv : genviron gT) (lenv : lenviron gT lT genv) (renv : renviron gT rT genv)
    (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv)
    (e : exp gT lT rT nT pT Tr) : Tr :=
  match e with
  | var i => nlookup nT nenv i
  | app Tr name nargs H => eval_app gT nT Tr genv nenv name nargs H
  | leta Tv Tr name nargs H body =>
      let v := eval_app gT nT Tv genv nenv name nargs H in
      let nT' := Tv :: nT in
      let pT' := pt_shift0 gT Tv nT pT in
      let nenv' := nenv_cons Tv v nT nenv in
      let penv' := eq_ind_r id penv (penviron_shift0 gT nT pT genv nenv Tv v) in
      let Peq := leta_eq gT nT Tv name nargs H in
      let prfeq : ptype gT nT' Peq genv nenv' := erefl in
      let pT'' := Peq :: pT' in
      let penv'' := penv_cons gT nT' pT' Peq genv nenv' prfeq penv' in
      eval gT lT rT nT' pT'' Tr genv lenv renv nenv' penv'' body
  | rappC Tr re => eval_rapp gT rT nT pT Tr genv renv nenv penv re
  | letrC Tv Tr re body =>
      let v := eval_rapp gT rT nT pT Tv genv renv nenv penv re in
      let nT' := Tv :: nT in
      let nenv' := nenv_cons Tv v nT nenv in
      let penv' := eq_ind_r id penv (penviron_shift0 gT nT pT genv nenv Tv v) in
      eval gT lT rT nT' (pt_shift0 gT Tv nT pT) Tr genv lenv renv nenv' penv' body
  | letpC Tr P pe body =>
      let prf := eval_papp gT lT nT pT P genv lenv nenv penv pe in
      let pT' := P :: pT in
      let penv' := penv_cons gT nT pT P genv nenv prf penv in
      eval gT lT rT nT pT' Tr genv lenv renv nenv penv' body
  | nmatch Tr i branches =>
      let Tv := ntnth nT i in
      let v := nlookup nT nenv i in
      (eval_nmatch gT lT rT nT pT genv lenv renv nenv penv Tv Tr [::] branches) v
  | letn Tv2 Tr i branches body =>
      let Tv1 := ntnth nT i in
      let v1 := nlookup nT nenv i in
      let v2 := eval_nmatch gT lT rT nT pT genv lenv renv nenv penv Tv1 Tv2 [::] branches v1 in
      let nT' := Tv2 :: nT in
      let nenv' := nenv_cons Tv2 v2 nT nenv in
      let penv' := eq_ind_r id penv (penviron_shift0 gT nT pT genv nenv Tv2 v2) in
      eval gT lT rT nT' (pt_shift0 gT Tv2 nT pT) Tr genv lenv renv nenv' penv' body
  | dmatch Tr i branches =>
      eval_dmatch gT lT rT nT pT genv lenv renv nenv penv i Tr [::] branches
  | letd Tv2 Tr i branches body =>
      let v2 := eval_dmatch gT lT rT nT pT genv lenv renv nenv penv i Tv2 [::] branches in
      let nT' := Tv2 :: nT in
      let nenv' := nenv_cons Tv2 v2 nT nenv in
      let penv' := eq_ind_r id penv (penviron_shift0 gT nT pT genv nenv Tv2 v2) in
      eval gT lT rT nT' (pt_shift0 gT Tv2 nT pT) Tr genv lenv renv nenv' penv' body
  end
with eval_nmatch (gT : genvtype) (lT : lenvtype gT) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT)
    (genv : genviron gT) (lenv : lenviron gT lT genv) (renv : renviron gT rT genv)
    (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv)
    (Tv Tr : Set) (Cts : seq (cstrT Tv))
    (e : nmatch_exp gT lT rT nT pT Tv Tr Cts) : Tv -> nmatcher_type Tv Cts Tr :=
  match e in nmatch_exp _ _ _ _ _ Tv Tr Cts
          return Tv -> nmatcher_type Tv Cts Tr with
  | nmatch_nil Tv' Tr' Cts' matcher => nmatcher Tv' Cts' matcher Tr'
  | nmatch_cons Tv' Tr' Ct Cts' branch brest =>
      let Ts := Tms4Ct Tv' Ct in
      let frest := eval_nmatch gT lT rT nT pT genv lenv renv nenv penv Tv' Tr'
        (Ct :: Cts') brest in
      let fbranch (fields : nenviron Ts) :=
        let penv' := eq_ind_r id penv (penviron_shift0s gT Ts nT pT genv fields nenv) in
        eval gT lT rT (nt_shift0s Ts nT) (pt_shift0s gT Ts nT pT) Tr'
          genv lenv renv (nenv_cat Ts nT fields nenv) penv' branch in
      fun (v : Tv') => frest v (curry_nmatch_branch Tv' Ct Tr' fbranch)
  end
with eval_dmatch (gT : genvtype) (lT : lenvtype gT) (rT : renvtype gT)
    (nT : nenvtype) (pT : penvtype gT nT)
    (genv : genviron gT) (lenv : lenviron gT lT genv) (renv : renviron gT rT genv)
    (nenv : nenviron nT) (penv : penviron gT nT pT genv nenv)
    (i : nat) (Tv := ntnth nT i) (v := nlookup nT nenv i)
    (Tr : Set) (Cts : seq (cstrT Tv))
    (e : dmatch_exp gT lT rT nT pT i Tr Cts) :
    dmatcher_type Tv Cts Tr v :=
  match e in dmatch_exp _ _ _ _ _ i Tr Cts
    return let Tv := ntnth nT i in dmatcher_type Tv Cts Tr (nlookup nT nenv i) with
  | dmatch_nil i Tr' Cts' matcher =>
      let Tv := ntnth nT i in
      dmatcher Tv Cts' matcher Tr' (nlookup nT nenv i)
  | dmatch_cons i Tr' Ct Cts' branch brest =>
      let Tv := ntnth nT i in
      let Ts := Tms4Ct Tv Ct in
      let c := cstr4Ct Tv Ct in
      let Tv' := ntnth nT i in
      let v : Tv' := nlookup nT nenv i in
      let frest := eval_dmatch gT lT rT nT pT genv lenv renv nenv penv i Tr'
        (Ct :: Cts')
        brest in
      let fbranch (fields : nenviron Ts) (H : uncurry_S Ts Tv' c fields = v) :=
        let penv' := eq_ind_r id penv (penviron_shift0s gT Ts nT pT genv fields nenv) in
        let penv'' := eq_ind_r id (H, penv') (penviron_dmatch_pty _ _ _ _ _ _ _ _ _) in
        eval gT lT rT (nt_shift0s Ts nT) (dmatch_pty gT nT i Ts c :: pt_shift0s gT Ts nT pT) Tr'
          genv lenv renv (nenv_cat Ts nT fields nenv) penv'' branch in
      frest (curry_dmatch_branch Tv' Ct Tr' v fbranch)
  end.

(* Convert several definitions into our environment *)

Definition LT1 : lenvtype GT1 := [::].
Definition LENV1 : lenviron GT1 LT1 GENV1 := [lenv:].

(* Original definition of simple (non-recursive) function *)
Definition negb_negb b := negb (negb b).

(* AST for negb_negb *)
Definition negb_negb_AST :=
  let gT := GT1 in
  let lT := LT1 in
  let rT := [::] in
  let nT := [:: bool] in
  let pT : penvtype gT nT := [::] in
  let Tr := bool in
    let name := "negb" in let nargs := [::0] in let H := erefl in
    leta gT lT rT nT pT bool bool name nargs H
    (let nT' := bool :: nT in
     let pT := leta_eq gT nT bool name nargs H :: pt_shift0 gT bool nT pT in
     let nT := nT' in
    let name := "negb" in let nargs := [::0] in let H := erefl in
    leta gT lT rT nT pT bool bool name nargs H
    (let nT' := bool :: nT in
     let pT := leta_eq gT nT bool name nargs H :: pt_shift0 gT bool nT pT in
     let nT := nT' in
    var gT lT rT nT pT 0)).

(* define a function using the AST *)
Definition negb_negb2 b :=
  let gT := GT1 in
  let genv := GENV1 in
  let lT := LT1 in
  let lenv := LENV1 in
  let rT := [::] in
  let renv : renviron gT rT genv := [renv:] in
  let nT := [:: bool] in
  let nenv : nenviron nT := [nenv: b] in
  let pT : penvtype gT nT := [::] in
  let penv : penviron gT nT pT genv nenv := [penv:] in
  let Tr := bool in
  eval gT lT rT nT pT Tr genv lenv renv nenv penv negb_negb_AST.

(* original function negb_negb, and
   AST-defined function negb_negb2 is convertible *)
Definition negb_negb_ok : negb_negb = negb_negb2 := erefl.

(* import negb_negb into our environment *)
Definition GTENT2 := gtent "negb_negb" [:: bool] bool.
Definition GT2' := [:: GTENT2].
Definition GT2 := GT2' ++ GT1.

(* we import negb_negb, but importing negb_negb2 is also possible
   because they are convertible *)

Definition GENT2 := gent "negb_negb" [:: bool] _ negb_negb.
Definition GENV2 : genviron GT2 := genv_cat GT2' GT1 [genv: GENT2] GENV1.

Definition LT2 := lt_shift0 GTENT2 GT1 LT1.
Definition LENV2 : lenviron GT2 LT2 GENV2 := LENV1.

(* Now, we try to import a (structural) recursive function *)

(* We assume a body of recursive function is defined separately.
  This makes us possible to compare the body and AST without
  concerning recursion. *)

Definition downto0_body (downto0 : nat -> unit) (n : nat) : unit :=
  match n with
  | 0 => tt
  | n'.+1 => downto0 n'
  end.

Fixpoint downto0 (n : nat) {struct n} : unit :=
  downto0_body downto0 n.

(* Define the AST for downto0_body *)
Definition downto0_AST :=
  let gT := GT2 in
  let lT := LT2 in
  let rT : renvtype gT := [:: ("downto0", rtyC gT [::nat] None unit)] in
  let nT := [:: (*n*)nat] in
  let pT := [::] in
  let Tr := unit in
  let i := (*n*)0 in
  let Tv := ntnth nT i in
  nmatch gT lT rT nT pT Tr i
    (nmatch_cons gT lT rT nT pT Tv Tr nat_S [::]
        (let nT := nat :: nT in let pT := [::] in
         rappC gT lT rT nT pT Tr
           (rapp_expC gT rT nT pT Tr "downto0" [:: (*n*)0] None None erefl erefl))
      (nmatch_cons gT lT rT nT pT Tv Tr nat_O [:: nat_S]
          (app gT lT rT nT pT Tr "tt" [::] erefl)
        (nmatch_nil gT lT rT nT pT Tv Tr [:: nat_O; nat_S] nat_matcher))).

(* We can define downto0_body' using the AST *)
Definition downto0_body' (downto0 : nat -> unit) (n : nat) : unit :=
  let gT := GT2 in
  let genv := GENV2 in
  let lT := LT2 in
  let lenv := LENV2 in
  let rT : renvtype gT := [:: ("downto0", rtyC gT [::nat] None unit)] in
  let renv : renviron gT rT genv :=
    [renv: rent gT "downto0" [:: nat] None unit genv (downto0)] in
  let nT := [:: nat] in
  let nenv : nenviron nT := [nenv: n] in
  let pT : penvtype gT nT := [::] in
  let penv : penviron gT nT pT genv nenv := [penv:] in
  let Tr := unit in
  eval gT lT rT nT pT Tr genv lenv renv nenv penv downto0_AST.

(* downto0_body and downto0_body' are convertible *)
Definition downto0_body_ok : downto0_body = downto0_body' := erefl.

(* We confirmed the body of downto0 is correctly represented by the AST and
  downto0 itself is a simple recursive function just calling the body.
  We consider the AST represent downto0 correctly.
  So, we import downto0 into our global environment. *)

Definition GTENT3 := gtent "downto0" [:: nat] unit.
Definition GT3' := [:: GTENT3].
Definition GT3 : genvtype := GT3' ++ GT2.
Definition GENV3 : genviron GT3 := ((uncurry [:: nat] _ downto0), GENV2).
Definition LT3 : lenvtype GT3 := lt_shift0 GTENT3 GT2 LT2.
Definition LENV3 : lenviron GT3 LT3 GENV3 := LENV2.

(* Note that unfortunately, downto0' using downto0_body' causes an error:
| Recursive definition of downto0' is ill-formed.
| Recursive call to downto0' has principal argument equal to
| "nenv.1" instead of a subterm of "n".
This error is caused because Coq termination checker doesn't unfold
somthing in eval. *)
Fail Fixpoint downto0' (n : nat) {struct n} : unit :=
  downto0_body' downto0' n.

(* Coq termination checker accepts the definition if we
unfold downto0_body' before *)
Definition downto0_body'' := Eval compute in downto0_body'.
Fixpoint downto0'' (n : nat) {struct n} : unit :=
  downto0_body'' downto0'' n.
Definition downto0''_ok : downto0 = downto0'' := erefl.

(* However, "Eval compute" unfold all definitions including GENV2.
It means the resulting term will be entire program which can be very big.
So, we don't use this definition here.
Selective unfolding is possible using Ltac, though. *)

(* Now, we try to import a (non-structural) recursive function *)

Fail Fixpoint upto (i n : nat) : unit :=
  match i < n with
  | true => upto i.+1 n
  | false => tt
  end.
(* Cannot guess decreasing argument of fix. *)

(* upto can be defined using Fixpoint and proof-editing mode *)
Fixpoint upto (i n : nat) (acc : Acc lt (n - i)) {struct acc} : unit.
  refine (
    match i < n as b' return (b' = (i < n)) -> unit with
    | true => fun (H : true = (i < n)) => upto i.+1 n _
    | false => fun (H : false = (i < n)) => tt
    end erefl).
  apply Acc_inv with (x:=n-i); first by [].
  apply/ltP.
  rewrite subnSK; last by [].
  by apply leqnn.
Defined.

(* We define upto in separated style: lemma, body and recursive function.
  This style makes us possible to compare the body and AST without
  concerning recursion.  *)

Lemma upto_lemma (i n : nat) (b : bool) (j : nat)
  (acc : Acc lt (n - i))
  (Hb : b = (i < n))
  (Hm : true = b)
  (Hj : j = i.+1) : Acc lt (n - j).
Proof.
  rewrite {}Hj.
  rewrite {}Hb in Hm.
  apply Acc_inv with (x:=n-i); first by [].
  apply/ltP.
  rewrite subnSK; last by [].
  by apply leqnn.
Defined.

Definition upto_body (upto : forall (i n : nat), Acc lt (n - i) -> unit)
    (i n : nat) (acc : Acc lt (n - i)) : unit :=
  let b := i < n in let Hb : b = (i < n) := erefl in
  match b as b' return b' = b -> unit with
  | true => fun (Hm : true = b) =>
    let j := i.+1 in let Hj : j = i.+1 := erefl in
    let acc' := upto_lemma i n b j acc Hb Hm Hj in
    upto j n acc'
  | false => fun (Hm : false = b) => tt
  end erefl.

Fixpoint upto' (i n : nat) (acc : Acc lt (n - i)) {struct acc} : unit :=
  upto_body upto' i n acc.

Lemma upto'_ok : upto = upto'. Proof. reflexivity. Qed.

Definition upto_lemma_nt := [::(*j*)nat; (*b*)bool; (*n*)nat; (*i*)nat].

Definition upto_lemma_pt : penvtype GT3 upto_lemma_nt :=
  let u := uncurry_pty GT3 upto_lemma_nt in
  [::
    (u (fun genv j b n i => j = glookup GT3 genv "S" (i,tt) (*i.+1*)));
    (u (fun genv j b n i => true = b));
    (u (fun genv j b n i => b = glookup GT3 genv "ltn" (i,(n,tt))));
    (u (fun genv j b n i => Acc lt (n - i)))
  ].

Definition upto_lemma_P : pty GT3 upto_lemma_nt :=
  uncurry_pty GT3 upto_lemma_nt
    (fun genv j b n i => Acc lt (n - j)).

Definition upto_lemma_lty := ltyC GT3 upto_lemma_nt upto_lemma_pt upto_lemma_P.

Definition GT4 := GT3.
Definition GENV4 := GENV3.
Definition LT4 : lenvtype GT4 := ("upto_lemma", upto_lemma_lty) :: LT3.

Definition LENV4 : lenviron GT4 LT4 GENV4 :=
  let gT := GT4 in
  let genv := GENV4 in
  let nT := upto_lemma_nt in
  let pT := upto_lemma_pt in
  (((fun (nenv : nenviron nT)
      (penv : penviron gT nT pT genv nenv) =>
    let j := nenv.1 in let b := nenv.2.1 in
    let n := nenv.2.2.1 in let i := nenv.2.2.2.1 in
    let Hj := penv.1 in let Hm := penv.2.1 in
    let Hb := penv.2.2.1 in
    let acc := penv.2.2.2.1 in
    upto_lemma i n b j acc Hb Hm Hj) : ltype gT upto_lemma_lty genv), LENV3).

(* Eval cbv zeta delta [upto_body_AST upto_if_AST upto_false_AST upto_true_AST3 upto_true_AST2 upto_true_AST1] in upto_body_AST . *)

Section upto_body_AST.
Let nT1 := [:: (*n*)nat; (*i*)nat].
Let nT2 := [:: (*b*)bool; (*n*)nat; (*i*)nat].
Let nT3 := [:: (*j*)nat; (*b*)bool; (*n*)nat; (*i*)nat].
Let rtyF := Some (fun (_ : genviron GT4) (nenv : (*i*)nat * ((*n*)nat * unit)) =>
  Acc lt ((*n*)nenv.2.1 - (*i*)nenv.1)).
Let rT := [:: ("upto", rtyC GT4 nT1 rtyF unit)].
Let pT1 := [:: fun (_ : genviron GT4) (nenv : nenviron nT1) => Acc lt ((*n*)nenv.1 - (*i*)nenv.2.1)].
Let pT2 := [:: (*Hb*)fun (genv : genviron GT4) (nenv : nenviron nT2) =>
                  (*b*)nenv.1 = glookup GT4 genv "ltn" ((*i*)nenv.2.2.1, ((*n*)nenv.2.1, tt));
  (*acc*)fun (_ : genviron GT4) (nenv : nenviron nT2) => Acc lt ((*n*)nenv.2.1 - (*i*)nenv.2.2.1)].
Let pT3 := (fun (_ : genviron GT4) (nenv : nenviron nT2) => false = nenv.1) :: pT2.
Let pT4 := (fun (_ : genviron GT4) (nenv : nenviron nT2) => true = nenv.1) :: pT2.
Let pT5 := [:: fun (genv : genviron GT4) (nenv : nenviron nT3) =>
    (*j*)nenv.1 = glookup GT4 genv "S" ((*i*)nenv.2.2.2.1, tt);
  fun (_ : genviron GT4) (nenv : nenviron nT3) => true = (*b*)nenv.2.1;
  fun (genv : genviron GT4) (nenv : nenviron nT3) =>
    (*b*)nenv.2.1 = glookup GT4 genv "ltn" ((*i*)nenv.2.2.2.1, ((*n*)nenv.2.2.1, tt));
  fun (_ : genviron GT4) (nenv : nenviron nT3) =>
    Acc lt ((*n*)nenv.2.2.1 - (*i*)nenv.2.2.2.1)].
Let pT6 := (fun (_ : genviron GT4) (nenv : nenviron nT3) =>
  Acc lt ((*n*)nenv.2.2.1 - (*j*)nenv.1)) :: pT5.

Let upto_lemma_pty := fun (_ : genviron GT4) (nenv : nenviron upto_lemma_nt) =>
  Acc lt ((*n*)nenv.2.2.1 - (*j*)nenv.1).

(* This reduces (b = glookup GT4 genv "ltn" (i, (n, tt))) to
  nenv.1 = genv.2.2.2.2.2.2.2.2.1 (nenv.2.2.1, (nenv.2.1, tt)).
Eval cbv beta zeta iota delta [pT2 uncurry_pty nT2 uncurry_ntT glookup GT4 GT3 GT3' GT2 GTENT3 GTENT2 GT2' GT1 GT1' GT0 cat
gtent eq_op Equality.op Equality.class string_eqType string_eqMixin eqstr string_dec
string_rec string_rect sumbool_rec sumbool_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
Bool.bool_dec bool_rec bool_rect] in pT2. *)

(*
leta b Hb := ltn i n in
  dmatch b with
  | true Hm =>
      leta j Hj := S i in
      letp acc' := upto_lemma i n b j acc Hb Hm Hj in
      upto j n acc'
  | false Hm =>
      tt
  end
*)
Definition upto_body_AST :=
  leta GT4 LT4 rT nT1 pT1 bool unit (* b Hb := *) "ltn" [:: (*i*)1; (*n*)0] erefl
    (dmatch GT4 LT4 rT nT2 pT2 unit (*b*)0
      (dmatch_cons GT4 LT4 rT nT2 pT2 (*b*)0 unit (* | false Hm *) bool_false [::]
        (app GT4 LT4 rT nT2 pT3 unit "tt" [::] erefl)
        (dmatch_cons GT4 LT4 rT nT2 pT2 (*b*)0 unit (* | true Hm *) bool_true [:: bool_false]
          (leta GT4 LT4 rT nT2 pT4 nat unit (* j Hj := *) "S" [:: (*i*)2] erefl
            (letp GT4 LT4 rT nT3 pT5 unit (* acc' := *) "upto_lemma" upto_lemma_pty
              [:: (*j*)0; (*b*)1; (*n*)2; (*i*)3]
              [:: (*Hj*)0; (*Hm*)1; (*Hb*)2; (*acc*)3]
              upto_lemma_pt upto_lemma_P erefl erefl erefl
              (rapp GT4 LT4 rT nT3 pT6 unit
                "upto" [:: (*j*)0; (*n*)2] (Some (*acc'*)0) rtyF erefl erefl)))
          (dmatch_nil GT4 LT4 rT nT2 pT2 (*b*)0 unit [:: bool_true; bool_false]
             bool_matcher)))).

End upto_body_AST.

(* We can define upto_body' using the AST *)
Definition upto_body' (upto : forall (i n : nat), Acc lt (n - i) -> unit)
    (i n : nat) (acc : Acc lt (n - i)) : unit :=
  let gT := GT4 in
  let genv := GENV4 in
  let lT := LT4 in
  let lenv := LENV4 in
  let rT : renvtype gT := [:: ("upto",
                 rtyC gT [::(*i*)nat; (*n*)nat]
                  (Some (fun genv nenv =>
                        let i := nenv.1 in let n := nenv.2.1 in
                        Acc lt (n - i)))
                  unit) ] in
  let renv : renviron gT rT genv :=
    [renv: rent gT "upto" [::nat;nat]
                (Some (fun genv i n => Acc lt (n - i)))
                unit genv upto] in
  let nT := [:: (*n*)nat; (*i*)nat] in
  let nenv : nenviron nT := [nenv: n; i] in
  let u := uncurry_pty gT nT in
  let pT : penvtype gT nT := [::
    (u (fun genv n i => Acc lt (n - i)))
  ] in
  let penv : penviron gT nT pT genv nenv := (acc,I) in
  let Tr := unit in
  eval gT lT rT nT pT Tr genv lenv renv nenv penv upto_body_AST.

(* upto_body and upto_body' are convertible *)
Lemma upto_body_ok : upto_body = upto_body'. Proof. reflexivity. Qed.

(* We confirmed the body of upto is correctly represented by the AST and
  upto itself is a simple recursive function just calling the body.
  We consider the AST represent upto correctly.
  So, we import upto into our global environment.
*)

(* Since our genv cannot have Prop argument, we need to define
  a function without Prop argument.
  Acc argument is easy to generate from non-dependent argument.
*)

Definition upto_without_acc (i n : nat) :=
  upto i n (lt_wf (n - i)).

Definition GTENT5 := gtent "upto" [:: nat; nat] unit.
Definition GT5' := [:: GTENT5].
Definition GT5 : genvtype := GT5' ++ GT4.
Definition GENV5 : genviron GT5 := ((uncurry [:: nat;nat] _ upto_without_acc), GENV4).
Definition LT5 : lenvtype GT5 := lt_shift0 GTENT5 GT4 LT4.
Definition LENV5 : lenviron GT5 LT5 GENV5 := LENV4.

(* Note that the recursive function can be defined using the AST.
  It needs that upto_body should be reduced before Coq termination checker.
*)

(* upto_body' is not usable to define the recursive function
| The command has indeed failed with message:
| Recursive definition of upto'' is ill-formed.
| ...
| Recursive call to upto'' has not enough arguments.
| Recursive definition is: "fun i n : nat => [eta upto_body' upto'' i n]".
*)
Fail Fixpoint upto'' (i n : nat) (acc : Acc lt (n - i)) {struct acc} : unit :=
  upto_body' upto'' i n acc.

(* However, upto_body'', the normal form of upto_body' is usable *)
Definition upto_body'' := Eval cbv in upto_body'.
Print upto_body''.
Lemma upto_body''_ok : upto_body' = upto_body''. reflexivity. Qed.

Fixpoint upto'' (i n : nat) (acc : Acc lt (n - i)) {struct acc} : unit :=
  upto_body'' upto'' i n acc.
Lemma upto''_ok : upto = upto''. reflexivity. Qed.
