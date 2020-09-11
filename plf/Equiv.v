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

Theorem aequiv_example : aequiv <{X - X}> <{ 0 }>.
Proof.
  intros st. simpl. lia.
Qed.

Theorem bequiv_example : bequiv <{X - X = 0}> <{ true }>.
Proof.
  intros st.
  unfold beval.
  rewrite aequiv_example.
  reflexivity.
Qed.

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

Check E_Seq.
Check E_Skip.

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
  - assert (H: st' =[ skip ]=> st').{
      apply E_Skip.
    }.


