Set Warnings "-notation-overridden,-parsing".
From SF Require Export IndProp.

Definition relation (X : Type) := X -> X -> Prop.

Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
Qed.

Theorem le_not_partial_function :
  not (partial_function le).
Proof.
  unfold not.
  unfold partial_function.
  intros H.
  assert (0 = 1) as Nonsense. {
    apply H with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.
Qed.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intros n.
  apply le_n.
Qed.

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo. Qed.

Theorem lt_trans :
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  - apply Hnm.
  - apply Hmo.
Qed.

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  not (symmetric le).
Proof.
  unfold not.
  unfold symmetric.
  intros.
  assert (1 <= 0) as Nonsense. {
    apply H.
    apply le_S.
    apply le_n. }
  inversion Nonsense.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Definition equivalence {X : Type} (R : relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).




