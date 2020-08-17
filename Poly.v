Set Warnings "-notation-overridden,-parsing".

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list.

Check (nil nat).

Check (cons nat 3 (nil nat)).

Check nil.

Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble : Type :=
| a : mumble
| b : mumble -> nat -> mumble
| c : mumble.

Inductive grumble (X : Type) : Type :=
| d : mumble -> grumble X
| e : X -> grumble X.

Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).

End MumbleGrumble.

Check O.

Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Check (cons _ 1 (cons _ 2 (cons _ 3 (nil _)))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X : Type} : Type :=
  | nil' : list'
  | cons' : X -> list'.

