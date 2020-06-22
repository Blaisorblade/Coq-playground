Require Import stdpp.base.
Set Primitive Projections.

Record foo := {
  a : nat;
  b : nat;
}.
Instance: Proper ((=) ==> (=)) a.
solve_proper. Qed.
Print a.
