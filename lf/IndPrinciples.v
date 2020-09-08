Check nat_ind.

Theorem mult_0_r' : forall n : nat,
    n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros. apply H. Qed.

Theorem plus_one_r' : forall n : nat,
    n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind.

Inductive Toy : Type :=
| con1 (b : bool)
| con2 (n : nat) (t : Toy).

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list_ind.

Definition P_m0r (n : nat) : Prop :=
  n * 0 = 0.

Theorem mult_0_r'' : forall n : nat,
    P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_m0r in IHn.
    unfold P_m0r.
    simpl. apply IHn.
Qed.

Inductive le1 : nat -> nat -> Prop :=
| le1_n : forall n, le1 n n
| le1_S : forall n m, (le1 n m) -> (le1 n (S m)).

Inductive le2 (n : nat) : nat -> Prop :=
| le2_n : le2 n n
| le2_S m (H : le2 n m) : le2 n (S m).

Check le1_ind.
Check le2_ind.


