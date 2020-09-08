Set Nested Proofs Allowed.
Inductive day : Type :=
| mon
| tues
| wed
| thur
| fri
| sat
| sun.

Definition next_weekday (d:day) : day :=
match d with
| mon => tues
| tues => wed
| wed => thur
| thur => fri
| fri => sat
| sat => sun
| sun => mon
end.

Compute (next_weekday mon).

Compute (next_weekday (next_weekday sat)).

Example test_next_weekday:
  (next_weekday (next_weekday sat)) = mon.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true
| false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* Definition andb (b1:bool) (b2:bool) : bool := *)
(*   match b1, b2 with *)
(*   | true, true => true *)
(*   | _, _ => false *)
(*   end. *)

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb : false || false || false || true = true.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).

Inductive rgb : Type :=
| red   : rgb
| green : rgb
| blue  : rgb.

Inductive color : Type :=
| black   : color
| white   : color
| primary : rgb -> color.

Definition monochrome (c: color) : bool :=
  match c with
  | black     => true
  | white     => true
  | primary _ => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black       => false
  | white       => false
  | primary red => true
  | primary _   => false
  end.

Inductive bit : Type :=
| B0
| B1.

Inductive nybble : Type :=
| bits : bit -> bit -> bit -> bit -> nybble.

Check (bits B1 B0 B1 B1).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | bits B0 B0 B0 B0 => true
  | bits _ _ _ _     => false
  end.

Compute (all_zero (bits B1 B0 B1 B1)).
Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n:nat) : nat :=
  match n with
  | O    => O
  | S n' => n'
  end.

End NatPlayground.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Example test_evenb: evenb (S (S O)) = true.
Proof. simpl. reflexivity. Qed.

Definition oddb (n:nat) : bool :=
  negb (evenb n).

Module NatPlaygroud2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O    => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O    => O
  | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

Compute (minus 10 8).

End NatPlaygroud2.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Compute (factorial 3).
Compute (factorial 5).

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Compute (eqb 4 4).

(** less than and equal <= **)
Fixpoint leb (n m: nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.

(**
Fixpoint ltb (n m: nat) : bool :=
  match n with
  | O => match m with
         | O => false
         | S m' => true
          end
  | S n' => match m with
            | O => false
            | S m' => ltb n' m'
            end
  end.
**)

Definition ltb (n m:nat) : bool :=
  andb (leb n m) (negb (eqb n m)).

Compute (ltb 2 4).
Compute (leb 2 4).
Compute (negb (eqb 2 4)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity.  Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* Theorem plus_n_O : forall n : nat, n + 0 = n. *)
(* Proof. *)
(*   intros n. simpl. reflexivity. Qed. *)

Theorem plus_1_1 : forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_1 : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.

Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exericise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
  Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n  m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_1.
  rewrite -> H.
  reflexivity. Qed.


Theorem plus_1_neq_0_firsttry : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  (* relate to nat constructor *)
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2: forall b c : bool,
    andb b c = true -> c = true.
Proof.
  (* intros b c. *)
  (* intros H. *)
  (* destruct b eqn:Eb. *)
  (* - rewrite <- H. *)
  (*   reflexivity. *)
  (* - rewrite <- H. *)
  (*   reflexivity. *)
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
