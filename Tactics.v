From XX Require Export Poly.
From XX Require Export Basic.
From XX Require Export Induction.


Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.
  intros.
  apply H0. Qed.
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros.
  rewrite <- rev_involutive with nat l'.
  rewrite <- H.
  reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_exercise : forall(n m x p : nat),
     m = (minustwo x) ->
     (n + p) = m ->
     (n + p) = (minustwo x).
Proof.
  intros.
  apply trans_eq with m.
  - apply H0.
  - apply H.
Qed.

Theorem S_injective : forall(n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros.
  injection H.
  intros.
  apply H0.
Qed.

Theorem injection_ex1 : forall(n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.


Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  injection H0.
  intros.
  symmetry.
  apply H2.
Qed.


Theorem discriminate_ex1 : forall(n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.



Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros.
  discriminate H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  induction n as [| n'].
  - intros. simpl in H.
    destruct m.
    + reflexivity.
    + discriminate H.
  - intros. rewrite <- plus_n_Sm in H.
    destruct m as [| m'].
    + discriminate H.
    + simpl in H.
      rewrite <- plus_n_Sm in H.
      apply S_injective in H.
      apply S_injective in H.
      apply IHn' in H.
      rewrite H.
      reflexivity.
Qed.
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  induction n.
  - intros.  destruct m.
    + reflexivity.
    + discriminate H.
  - intros. destruct m.
    + discriminate.
    + simpl in H.
      apply IHn in H.
      rewrite H.
      reflexivity.
Qed.


Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros. generalize dependent n.
  induction l.
  - intros. reflexivity.
  - intros. destruct n.
    + discriminate.
    + injection H as H.
      apply IHl in H.
      simpl.
      apply H.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
Lemma list_cons_eq : forall X (l1 l2 : list X) (x : X),
  l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros X l1 l2 x H. rewrite H. reflexivity.
Qed.
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  induction l.
  - simpl.
    intros.
    injection H as H.
    rewrite <- H.
    rewrite <- H0.
    reflexivity.
  - intros.
    destruct l1.
    + destruct x. simpl in H.
      destruct (split l). discriminate H.
    + destruct x. simpl in H.
      destruct (split l).
      destruct l2.
      * discriminate H.
      * injection H. intros.
        simpl.
        rewrite H3.
        rewrite H1.
        apply list_cons_eq.
        apply IHl.
        rewrite H2.
        rewrite H0.
        reflexivity.
Qed.


Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros.
  destruct (f b) eqn:E.
  - destruct (f true) eqn:E1.
    + apply E1.
    + destruct (f false) eqn:E2.
      * reflexivity.
      * destruct b.
        -- rewrite E1 in E. discriminate.
        -- rewrite E2 in E. discriminate.
  - destruct (f false) eqn:E1.
    + destruct (f true) eqn:E2.
      * destruct b.
        -- rewrite E2 in E. discriminate.
        -- rewrite E1 in E. discriminate.
      * reflexivity.
    + apply E1.
Qed.


Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  induction n.
  - destruct m.
    + reflexivity.
    + reflexivity.
  - destruct m.
    + reflexivity.
    + simpl.
      apply IHn.
Qed.


Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros.
  apply eqb_true in H.
  apply eqb_true in H0 as H2.
  rewrite H.
  apply H0.
Qed.


Definition split_combine_statement : Prop :=
  forall X Y (l : list (X * Y)) l1 l2,
    length l1 = length l2 ->
    combine l1 l2 = l ->
    split l = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l l1 l2 H H1.
  generalize dependent l1.
  generalize dependent l2.
  induction l.
  - destruct l1.
    + destruct l2.
      * reflexivity.
      * discriminate.
    + destruct l2.
      * discriminate.
      * discriminate.
  - intros.
    destruct l1.
    + destruct l2.
      * discriminate H1.
      * discriminate H.
    + destruct l2.
      * discriminate H.
      * injection H.
        simpl in H1.
        injection H1.
        intros.
        apply IHl in H3.
        -- rewrite <- H2.
           simpl.
           rewrite H3.
           reflexivity.
        -- apply H0.
Qed.


Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                            (x : X) (l lf : list X) ,
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l.
  generalize dependent x.
  induction l.
  - simpl. discriminate.
  - intros.
    simpl in H.
    destruct (test x) eqn:E.
    + injection H.
      intros.
      rewrite <- H1.
      apply E.
    + apply IHl in H.
      apply H.
Qed.


Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h::t => andb (test h) (forallb test t)
  end.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.
Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h::t => if test h then true else existsb test t
  end.
Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb' oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.
Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l.
  - reflexivity.
  - simpl.
    destruct (test x) eqn:E.
    + unfold existsb'.
      simpl.
      rewrite E.
      reflexivity.
    + rewrite IHl.
      unfold existsb'.
      simpl.
      rewrite E.
      reflexivity.
Qed.
