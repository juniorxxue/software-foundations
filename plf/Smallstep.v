Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

Inductive tm : Type :=
| C : nat -> tm
| P : tm -> tm -> tm.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
    (step
       (P (C n1) (C n2))
       (C (n1 + n2)))
| ST_Plus1 : forall t1 t1' t2,
    (step t1 t1') -> (step (P t1 t2)
                          (P t1' t2))
| ST_Plus2 : forall n1 t2 t2',
    (step t2 t2') -> (step (P (C n1) t2)
                          (P (C n1) t2')).

Notation " t '-->' t' " := (step t t') (at level 50, left associativity).
Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1.
  apply ST_PlusConstConst.
Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 1) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C 4)).
Proof.
  apply ST_Plus2.
  apply ST_Plus2.
  apply ST_PlusConstConst.
Qed.


Definition relation (X : Type) := X -> X -> Prop.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Module Temp4.

  Inductive tm1 : Type :=
  | tru : tm1
  | fls : tm1
  | test : tm1 -> tm1 -> tm1 -> tm1.

  Inductive value : tm1 -> Prop :=
  | v_tru : value tru
  | v_fls : value fls.

  Inductive step1 : tm1 -> tm1 -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (step1 (test tru t1 t2)
             t1)
  | ST_IfFalse : forall t1 t2,
      (step1 (test fls t1 t2)
             t2)
  | ST_If : forall t1 t1' t2 t3,
      (step1 t1 t1') ->
      (step1 (test t1 t2 t3)
            (test t1' t2 t3)).
  Notation " t '--->' t' " := (step1 t t') (at level 40).

  Definition bool_step_propl :=
    fls ---> fls.

End Temp4.

(* Multi-Step Reduction *)
Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : forall (x : X), multi R x x
| multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Notation " t '-->*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros.
  apply multi_step with y.
  apply H.
  apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
    multi R x y -> multi R y z -> multi R x z.
Proof.
  intros.
  induction H.
  - assumption.
  - apply multi_step with y.
    assumption.
    apply IHmulti.
    apply H0.
Qed.

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
      (P (C (0 + 3))
         (P (C 2) (C 4))).
  apply ST_Plus1.
  apply ST_PlusConstConst.
  apply multi_step with
      (P (C (0 + 3))
         (C (2 + 4))).
  apply ST_Plus2.
  apply ST_PlusConstConst.
  apply multi_R.
  apply ST_PlusConstConst.
Qed.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n, ev n -> ev (S (S n)).

Check ev_SS.

Check ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)).





