From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Locate "+".
Print Init.Nat.add.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Check string_dec.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [H1 | H2].
  - reflexivity.
  - unfold not in H2. simpl in H2. destruct H2.
    reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [H1 | H2].
  - rewrite H1. split. reflexivity. reflexivity.
  - split.
    + intro contra. discriminate contra.
    + intros H. exfalso. apply H2. apply H.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y.
  rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
           (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
                            (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" :=
  (t_update m x v)
    (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
  "foo" !-> true;
  _ !-> false).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros A x v.
  unfold t_empty.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v; m) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  assert(H: eqb_string x x = true).
  rewrite eqb_string_true_iff.
  reflexivity.
  rewrite H.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  assert (H2: eqb_string x1 x2 = false).
  rewrite eqb_string_false_iff.
  apply H.
  rewrite H2.
  reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Proof.
  Admitted.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_string x x0) eqn:E.
  - apply eqb_string_true_iff in E.
    f_equal. apply E.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                             v1 v2 x1 x2,
    x1 <> x2 -> (x1 !-> v1 ; x2 !-> v2 ; m) =
              (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_string x1 x) eqn:E1.
  - destruct (eqb_string x2 x) eqn:E2.
    + apply eqb_string_true_iff in E1.
      apply eqb_string_true_iff in E2.
      rewrite <- E2 in E1.
      destruct H. apply E1.
    + reflexivity.
  - destruct (eqb_string x2 x) eqn:E2.
    + reflexivity.
    + reflexivity.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
                               (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
                          (at level 100).

Example examplemap'' :=
  ("Church" |-> true; "Turing" |-> false).

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

(* Definition inclusion_update : forall (A : Type) (m m' : partial_map A) x vx, *)
(*     inclusion m m' -> inclusion (x |-> vx ; m) (x |-> vx ; m'). *)



