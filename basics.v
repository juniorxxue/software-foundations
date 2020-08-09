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

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | _, _ => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | false, false => false
  | _, _ => true
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



