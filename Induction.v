Set Nested Proofs Allowed.
Require Export Basics.

Theorem plus_n_0_firsttry : forall n:nat,
  n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_0: forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_0. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  Admitted.