Inductive day: Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite -> H.
  simpl.
  reflexivity.
Qed.
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n (* as [| n'] *) eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
  - reflexivity.
  - rewrite <- H.
    destruct b.
    + reflexivity.
    + reflexivity.
Qed.
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [].
  reflexivity.
  reflexivity.
  Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros H1 H2 b.
  rewrite -> H2.
  rewrite -> H2.
  reflexivity.
Qed.



Theorem and_false_always_false:
  forall b, andb false b = false.
Proof. reflexivity. Qed.

Theorem or_true_always_true:
  forall b, orb true b = true.
Proof. reflexivity. Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c H.
  destruct b.
  - rewrite <- or_true_always_true with c.
    rewrite <- H.
    destruct c.
    + reflexivity.
    + reflexivity.
  - rewrite <- and_false_always_false with c.
    rewrite -> H.
    reflexivity.
Qed.


Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | A m' => B m'
  | B m' => A (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B m' => S O + 2 * (bin_to_nat m')
  | A m' => 2* (bin_to_nat m')
  end.

Example test_bin_incr1 :
  incr (B Z) = A (B Z).
Proof. reflexivity. Qed.
Example test_bin_incr2 :
  incr (A (B Z)) = B (B Z).
Proof. reflexivity. Qed.
Example test_bin_incr3 :
  incr (B (B Z)) = A (A (B Z)).
Proof. reflexivity. Qed.

Example test_bin_to_nat1 :
  bin_to_nat (A (B Z)) = S (S O).
Proof. reflexivity. Qed.
Example test_bin_to_nat2 :
  bin_to_nat (A (A (B Z))) = S (S (S (S O))).
Proof. reflexivity. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.
