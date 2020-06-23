From stdpp Require Import prelude.

Definition foo := ∀ A, A.

Arguments foo : simpl never.

Goal foo.
hnf.
intro.
