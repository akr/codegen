Inductive lseq (T : Type) : Type :=
| lnil : lseq T
| lcons : T -> lseq T -> lseq T.
Arguments lnil {_}.
Arguments lcons {_} _ _.

Definition lseq_consume {T : Type} :=
  fix f (s : lseq T) : unit :=
  match s with
  | lnil => tt
  | lcons x s' => f s'
  end.

Inductive bseq (T : Type) : Type :=
| bnil : bseq T
| bcons : T -> bseq T -> bseq T.
Arguments bnil {_}.
Arguments bcons {_} _ _.

Definition borrow_lseq {T : Type} :=
  fix f (s : lseq T) : bseq T :=
    match s with
    | lnil => bnil
    | lcons x s => bcons x (f s)
    end.

Definition borrow_lseq_bool := @borrow_lseq bool.

Definition copy_bseq {T : Type} :=
  fix f (s : bseq T) : lseq T :=
    match s with
    | bnil => lnil
    | bcons x s => lcons x (f s)
    end.

Definition lncons {T : Type} (n : nat) (x : T) (s : lseq T) :=
  let aux :=
    fix aux (m : nat) (acc : lseq T) :=
    match m with
    | O => acc
    | S m' => aux m' (lcons x acc)
    end
  in
  aux n s.

Definition lnseq {T : Type} (n : nat) (x : T) : lseq T :=
  lncons n x lnil.

Definition bhead {T : Type} (x0 : T) (s : bseq T) : T :=
  match s with
  | bnil => x0
  | bcons x s' => x
  end.

Definition lbehead {T : Type} (s : lseq T) : lseq T :=
  match s with
  | lnil => lnil
  | lcons x s' => s'
  end.

Definition blast {T : Type} :=
  fix f (x0 : T) (s : bseq T) : T :=
  match s with
  | bnil => x0
  | bcons x s' => f x s'
  end.

Definition lbelast {T : Type} (s : bseq T) : lseq T :=
  let aux :=
    fix aux (x0 : T) (s : bseq T) : lseq T :=
    match s with
    | bnil => lcons x0 lnil
    | bcons x s' => lcons x0 (aux x s')
    end
  in
  match s with
  | bnil => lnil
  | bcons x s' => aux x s'
  end.

Definition bsize {T : Type} (s : bseq T) : nat :=
  let fix aux (s : bseq T) (n : nat) :=
    match s with
    | bnil => n
    | bcons _ s' => aux s' (S n)
    end
  in
  aux s 0.

Definition bnth {T : Type} (x0 : T) :=
  fix bnth (s : bseq T) (i : nat) : T :=
  match s with
  | bnil => x0
  | bcons x s' =>
      match i with
      | O => x
      | S i' => bnth s' i'
      end
  end.

Definition lset_nth {T : Type} (x0 : T) :=
  fix aux (s : lseq T) (i : nat) (y : T) : lseq T :=
  match s with
  | lnil => lncons i x0 (lcons y lnil)
  | lcons x s' =>
      match i with
      | O => lcons y s'
      | S i' => lcons x (aux s' i' y)
      end
  end.

Definition bnilp {T : Type} (s : bseq T) : bool :=
  match s with
  | bnil => true
  | bcons _ _ => false
  end.

Definition lcatrev {T : Type} :=
  fix lcatrev (s1 s2 : lseq T) : lseq T :=
  match s1 with
  | lnil => s2
  | lcons x s' => lcatrev s' (lcons x s2)
  end.

Definition lrev {T : Type} (s : lseq T) : lseq T :=
  lcatrev s lnil.

Definition bcatrev {T : Type} :=
  fix bcatrev (s1 : bseq T) (s2 : lseq T) : lseq T :=
  match s1 with
  | bnil => s2
  | bcons x s' => bcatrev s' (lcons x s2)
  end.

Definition brev {T : Type} (s : bseq T) : lseq T :=
  bcatrev s lnil.

Definition lcat {T : Type} :=
  fix lcat (s1 s2 : lseq T) : lseq T :=
    match s1 with
    | lnil => s2
    | lcons x s => lcons x (lcat s s2)
    end.

Definition blcat {T : Type} :=
  fix blcat (s1 : bseq T) (s2 : lseq T) : lseq T :=
    match s1 with
    | bnil => s2
    | bcons x s => lcons x (blcat s s2)
    end.

Definition lmap {A B : Type} (f : A -> B) :=
  fix lmap (s : bseq A) : lseq B :=
    match s with
    | bnil => lnil
    | bcons x s => lcons (f x) (lmap s)
    end.

Definition lfilter {T : Type} (f : T -> bool) :=
  fix lfilter (s : bseq T) : lseq T :=
    match s with
      | bnil => lnil
      | bcons x s => if f x then lcons x (lfilter s) else lfilter s
      end.

Definition lmask {T : Type} :=
  fix mask (m : bseq bool) (s : bseq T) : lseq T :=
    match m, s with
    | bcons true m', bcons x s'  => lcons x (mask m' s')
    | bcons false m', bcons x s' => mask m' s'
    | _, _ => lnil
    end.

Definition ltake {T : Type} :=
  fix ltake (n : nat) (s : bseq T) : lseq T :=
    match n, s with
    | S n', bcons x s' => lcons x (ltake n' s')
    | _, _ => lnil
    end.

Definition ldrop {T : Type} :=
  fix ldrop (n : nat) (s : lseq T) : lseq T :=
    match n, s with
    | O, _ => s
    | _, lnil => lnil 
    | S n', lcons x s' => ldrop n' s'
    end.

Definition bdrop {T : Type} :=
  fix bdrop (n : nat) (s : bseq T) : bseq T :=
    match n, s with
    | O, _ => s
    | _, bnil => s 
    | S n', bcons x s' => bdrop n' s'
    end.

Definition lrot {T : Type} (n : nat) (s : bseq T) : lseq T :=
  blcat (bdrop n s) (ltake n s).

Definition lrotr {T : Type} (n : nat) (s : bseq T) : lseq T :=
  lrot (bsize s - n) s.
