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
