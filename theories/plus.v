Class Plus (A : Type) : Type :=
  plus : A -> A -> A.
Arguments plus {A _}.

Infix "+" := plus.
Instance Plus_nat : Plus nat := Nat.add.

Instance Plus_pointwise {A B} `{Plus B} : Plus (A -> B) :=
  fun f g x => f x + g x.

Definition test {A B C} (f g : A -> B -> C -> nat) := f + g.
