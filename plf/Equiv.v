Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From PLF Require Export Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Theorem skip_left : forall c,
    cequiv
    <{ skip; c }>
    c.
Proof.
  intros c st st'.
  split. intros H.
  - inversion H. subst.
    inversion H2. subst.
    assumption.
  - apply E_Seq.
    apply E_Skip.
Qed.

Theorem skip_right : forall c,
    cequiv
    <{ c; skip }>
    c.
Proof.
  intros c st st'.
  split. intros H.
  - inversion H. subst.
    inversion H5. subst.
    assumption.
  - intros.
    apply E_Seq with st'.
    assumption.
    apply E_Skip.
Qed.

Theorem if_true_simple : forall c1 c2,
    cequiv
    <{ if true then c1 else c2 end }>
    c1.
Proof.
  intros.
  split.
  intros H.
  - inversion H; subst. assumption. discriminate.
  - apply E_IfTrue. reflexivity. Qed.

Theorem if_true: forall b c1 c2,
  bequiv b <{true}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. Qed.

(* Unset Printing Notations. *)

Theorem if_false : forall b c1 c2,
    bequiv b <{ false }> ->
    cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b is true *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
    + (* b is false *)
      assumption.
  - (* <- *)
    apply E_IfFalse.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. assumption.
Qed.

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  intros.
  unfold cequiv. intros.
  split.
  - intros.
    inversion H; subst.
    + apply E_IfFalse.
      simpl. rewrite H5. trivial. trivial.
    + apply E_IfTrue.
      simpl. rewrite H5. trivial. trivial.
  - intros.
    inversion H; subst.
    + apply E_IfFalse.
      simpl in H5.
      assert (Hnegb: negb (negb (beval st b)) = beval st b).
      eapply negb_involutive.
      rewrite <- Hnegb. rewrite H5. trivial. trivial.
    + apply E_IfTrue.
      simpl in H5.
      assert (Hnegb: negb (negb (beval st b)) = beval st b).
      eapply negb_involutive.
      rewrite <- Hnegb. rewrite H5. trivial. trivial.
Qed.

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros.
  unfold cequiv.
  intros.
  split; intros.
  - inversion H0; subst; clear H0.
    + constructor.
    + unfold bequiv in H. simpl in H.
      pose proof (H st) as Contra.
      rewrite H3 in Contra. inversion Contra.
  - inversion H0; subst.
    apply E_WhileFalse.
    apply H.
Qed.
