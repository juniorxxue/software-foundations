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
