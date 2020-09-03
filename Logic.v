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

Lemma mult_eq_0:
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  destruct n.
  - left. reflexivity.
  - destruct m.
    + right. reflexivity.
    + simpl in H. discriminate H.
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

Module MyNot.

  Definition not (P : Prop) := P -> False.
  Notation "~ x" := (not x) : type_scope.
  Check not : Prop -> Prop.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not : forall (P : Prop),
    not P -> (forall (Q: Prop), P -> Q).
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros.
  discriminate H.
Qed.

Theorem not_False :
  not False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ not P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G. apply G. apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
    (P -> Q) -> (not Q -> not P).
Proof.
  intros.
  unfold not.
  intros.
  apply H in H1.
  unfold not in H0.
  apply H0 in H1.
  destruct H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    not (P /\ not P).
Proof.
  intros.
  unfold not.
  intros [H1 H2].
  apply H2 in H1.
  destruct H1.
Qed.

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = True *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

Module MyIff.
  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity)
                          : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros.
  split.
  - apply H.
  - apply H.
Qed.

Lemma not_true_iff_false : forall b,
    b <> true <-> b = false.
Proof.
  intros. split.
  - intros. apply not_true_is_false. apply H.
  - intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [H1 | [H2 H3]].
    + split.
      * left. apply H1.
      * left. apply H1.
    + split.
      * right. apply H2.
      * right. apply H3.
  - intros [[H1 | H2] [H3 | H4]].
    + left. apply H1.
    + left. apply H1.
    + left. apply H3.
    + right. split.
      * apply H2.
      * apply H4.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply eq_mult_0.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H1 | [H2 | H3]].
    + left. left. apply H1.
    + left. right. apply H2.
    + right. apply H3.
  - intros [[H1 | H2] | H3].
    + left. apply H1.
    + right. left. apply H2.
    + right. right. apply H3.
Qed.
















