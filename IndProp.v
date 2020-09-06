Set Warnings "-notation-overridden,-parsing".
From SF Require Export Logic.
From Coq Require Export Lia.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* We can think of the definition of ev as defining a Coq property ev : nat → Prop, together with "evidence constructors" ev_0 : ev 0 and ev_SS : ∀ n, ev n → ev (S (S n)). *)

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Print ev_4.

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros.
  simpl.
  apply ev_SS. apply ev_SS.
  apply H.
Qed.

Theorem ev_double : forall n,
    ev (double n).
Proof.
  intros.
  induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_inversion :
  forall (n : nat), ev n ->
             (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros.
  destruct H as [ | n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split.
    +  reflexivity.
    + apply E'.
Qed.

Theorem ev_minus2 : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  Abort.

Theorem evSS_ev_remember : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros.
  remember (S (S n)) as k eqn:Hk.
  destruct H as [|n' E'] eqn:EE.
  - discriminate Hk.
  - injection Hk. intros. rewrite <- H0. apply E'.
Qed.

Theorem evSS_ev : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [H0 | H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]].
    injection Hnm as Heq. rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  apply E'.
Qed.

Theorem ev_even_firsttry : forall n,
    ev n -> even n.
Proof.
  intros n E. inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
  - generalize dependent E'.
Abort.

Lemma ev_even : forall n,
    ev n -> even n.
Proof.
  intros n E.
  induction E as [| n' E' IH].
  - exists 0. reflexivity.
  - unfold even in IH.
    destruct IH as [k Hk].
    rewrite Hk. unfold even. exists (S k).
    simpl. reflexivity.
Qed.

Theorem ev_even_iff :
  forall n, ev n <-> even n.
Proof.
  intros.
  split.
  - apply ev_even.
  - unfold even. intros [k Hk].
    rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m,
    ev n -> ev m -> ev (n + m).
Proof.
  intros.
  induction H as [|n' H' IH'].
  - simpl. apply H0.
  - simpl. apply ev_SS. apply IH'.
Qed.

Theorem ev_ev_ev : forall n m,
    ev (n + m) -> ev n -> ev m.
Proof.
  intros.
  induction H0 as [|n' H' IH'].
  - simpl in H. apply H.
  - simpl in H.
    inversion H as [|H1 n'' HE].
    apply IH'.
    apply n''.
Qed.

Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

  Notation "n <= m" := (le n m).

  Theorem test_le1 :
    3 <= 3.
  Proof.
    apply le_n. Qed.

  Theorem test_le2 :
    3 <= 6.
  Proof.
    apply le_S. apply le_S. apply le_S. apply le_n.
  Qed.

  Theorem test_le3:
    (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros. inversion H. inversion H2.
  Qed.

  Definition lt (n m : nat) := le (S n) m.

  Notation "m < n" := (lt m n).

  End Playground.

Inductive square_of : nat -> nat -> Prop :=
| sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
| ne_1 n (H : ev (S n)) : next_ev n (S n)
| ne_2 n (H : ev (S (S n))) : next_ev n (S (S n)).










