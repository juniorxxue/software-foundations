Set Warnings "-notaion-overridden, -parsing".
From SF Require Export Tactics.

Check forall n : nat, pred (S n) = n.
Check fun n: nat => S (pred n) = n.

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
  destruct H.
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

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  apply mult_0. apply H.
Qed.

Definition even x := exists n : nat, x = double n.

Lemma four_is_even :
  even 4.
Proof.
  unfold even.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  simpl.
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
    (forall x, P x) -> not (exists x, not (P x)).
Proof.
  intros X P H.
  unfold not.
  intros [x H0].
  apply H0.
  apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [H1 | H2]].
    + left. exists x. apply H1.
    + right. exists x. apply H2.
  - intros [[x1 H1] | [x2 H2]].
    + exists x1. left. apply H1.
    + exists x2. right. apply H2.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_l : In 4 [1;2;3;4;5].
Proof.
  simpl. right. right. right. left.
  reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros until x.
  induction l as [| x' l' IHl'].
  - simpl. intros. apply H.
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Check plus_comm.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H.
  unfold not.
  intros.
  rewrite H0 in H.
  simpl in H.
  apply H.
Qed.

Axiom functional_extensionality : forall {X Y : Type}
                                    {f g : X -> Y},
    (forall (x : X), f x = g x) -> f = g.

Example function_extensionality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros.
  apply plus_comm.
Qed.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_lemma:
  forall X (l1 l2 : list X),
    rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros X l1.
  induction l1.
  - intros l2. reflexivity.
  - intros l2. simpl. rewrite <- app_assoc. simpl. apply IHl1.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold tr_rev.
  rewrite tr_rev_lemma.
  apply app_nil_r.
Qed.

Check app_nil_r.

Lemma evenb_double : forall k, evenb (double k) = true.
Proof.
  intros.
  induction k.
  - simpl. reflexivity.
  - simpl. apply IHk.
Qed.

Check evenb_S.

Search double.

Lemma evenb_double_conv : forall n, exists k,
      n = if evenb n
          then double k
          else S (double k).
Proof.
  intros.
  induction n.
  - simpl. exists 0. reflexivity.
  - rewrite evenb_S. simpl.
    destruct (evenb n) eqn:E.
    + simpl. destruct IHn as [k H].
      rewrite H. exists k. reflexivity.
    + simpl. destruct IHn. exists (S x).
      rewrite H. reflexivity.
Qed.

Check even.

Theorem even_bool_prop : forall n,
    evenb n = true <-> even n.
Proof.
  intros n.
  split.
  - intros. destruct (evenb_double_conv n) as [k Hk].
    rewrite H in Hk. rewrite Hk. simpl. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
    n1 =? n2 = true <-> n1 = n2.
Proof.
  Admitted.

Lemma plus_eqb_example : forall n m p: nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  Admitted.

























