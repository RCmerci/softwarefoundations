From XX Require Export Basic.
Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' Hn].
  - reflexivity.
  - simpl.
    rewrite -> Hn.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction m.
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite -> IHm.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem double_negb:
  forall n :bool, n = negb (negb n).
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.


Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - rewrite -> IHn.
    simpl.
    rewrite <- double_negb.
    reflexivity.
Qed.
