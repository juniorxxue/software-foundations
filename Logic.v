Set Warnings "-notaion-overridden, -parsing".
From SF Require Export Tactics.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H1. apply H1.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  reflexivity.
  reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Search plus.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct n.
    + reflexivity.
    + destruct m.
      discriminate.
      discriminate.
  - destruct m.
    reflexivity.
    destruct n.
    discriminate.
    discriminate.
Qed.

Example and_exercise' :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct n.
    + reflexivity.
    + destruct m.
      * inversion H.
      * inversion H.
  - destruct m.
    + reflexivity.
    + destruct n.
      * inversion H.
      * inversion H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.

Lemma eq_mult_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. simpl. reflexivity.
Qed.




