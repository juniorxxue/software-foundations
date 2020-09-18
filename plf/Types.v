Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.
Hint Constructors multi : core.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Inductive bvalue : tm -> Prop :=
| bv_tru : bvalue tru
| bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
| nv_zro : nvalue zro
| nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.
Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall v,
      nvalue v ->
      (prd (scc v)) --> v
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall v,
       nvalue v ->
      (iszro (scc v)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

Inductive ty : Type :=
| Bool : ty
| Nat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool
where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
  - apply T_Fls.
  - apply T_Zro.
  - apply T_Scc. apply T_Zro.
Qed.

Example scc_hastype_nat__hastype_nat : forall t,
  |- scc t \in Nat ->
  |- t \in Nat.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Lemma bool_canonical : forall t,
    |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t Ht [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion Ht.
    + inversion Ht.
Qed.

Lemma nat_canonical : forall t,
    |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t Ht [Hb | Hn].
  - inversion Hb.
    + subst. inversion Ht.
    + subst. inversion Ht.
  - assumption.
Qed.
(* Use type error to invert it *)

Theorem progress : forall t T,
  |- t \in T ->
          value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_Tru and
     T_Fls, were eliminated immediately by auto *)
  - (* T_Test *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (test t1' t2 t3). auto.
  - (* T_Succ *)
    destruct IHHT.
    + left.
Admitted.

(* Type Preservation *)
Theorem preservation : forall t t' T,
    |- t \in T ->
            t --> t' ->
            |- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst; clear HE.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Check step.

Check multi.

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.
