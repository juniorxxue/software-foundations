From SF Require Export Poly.

(* the goal to be proved is exactly the same as some hypothesis in the context 
or some previously proved lemma. *)
Theorem silly1 : forall (n m o p : nat),
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <-eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. (* implication *)
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 2 = true ->
  oddb 3 = true.
Proof.
  intros eq1 eq2.
  apply eq1.
  apply eq2.
Qed.

Theorem silly3_firsttry : forall (n : nat),
  true = (n =? 5) ->
  (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H. Qed.

Search rev.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry. apply rev_involutive. Qed.

(* The apply with tactic.  *)
Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  transitivity m.
  apply H2. apply H1.
Qed.

(* injection and discriminate *)
Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite -> H1. rewrite -> H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m o : nat),
  [n;m] = [o;o] -> [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros H1 H2. rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros.
  injection H as eq1 eq2.
  assert (H1 : y :: l = z :: l). rewrite eq2. rewrite H0. reflexivity.
  injection H1 as eq3. rewrite eq1. rewrite eq3.
  reflexivity.
Qed.

Theorem eqb_0_l : forall n,
  0 =? n = true -> n = 0.
Proof.
  intros.
  destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - simpl. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true -> [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

Example discriminate_ex3 : 
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros.
  discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  (S n) =? (S m) = b ->
  n =? m = b.
Proof.
  intros.
  simpl in H.
  apply H. Qed.

Theorem silly3 : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) -> true = (n =? 5) -> true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem double_injective: forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. intros m eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq. destruct m as [| m'] eqn:E.
    + discriminate eq.
    + apply f_equal. apply IHn'. simpl in eq.
      injection eq as goal. apply goal. Qed.
