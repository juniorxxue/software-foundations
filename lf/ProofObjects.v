Set Warnings "-notation-overridden,-parsing".
From SF Require Export IndProp.
Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition P_implies_P : forall (P : Prop), P -> P.
Proof.
  intros P H.
  apply H.
Qed.

Definition P_implies_P' : forall (P : Prop), P -> P :=
  fun (P : Prop) (H : P) => H.

Print P_implies_P.
Print P_implies_P'.

Definition add1 : nat -> nat.
  intros n.
  Show Proof.
  apply S.
  Show Proof.
  apply n.
  Show Proof.
Defined.

Module And.
  Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

  Arguments conj [P] [Q].

  Notation "P /\ Q" := (and P Q) : type_scope.

  Print prod.

  Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
    fun (P Q R : Prop) => fun (H1 : P /\ Q) =>
                      fun (H2 : Q /\ R) =>
                        match H1, H2 with
                        | conj p q, conj q' r => conj p r
                        end.

End And.

Print True.

Check (fun x => x) I.

Locate "_ /\ _".
Check and.
Print and.
Print or.

Module MyEquality.

  Inductive eq {X : Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

  Notation "x == y" := (eq x y)
                         (at level 70, no associativity)
                       : type_scope.
End MyEquality.

