From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Lemma sep_demo {PROP: sbi} (P1: PROP)  (P2 P3: Prop) (Himpl: P2 -> P3) :
  P1 ∗ ⌜P2⌝ -∗ P1 ∗ ⌜P3⌝.
Proof.
  iIntros "[HP %HP2]".
  iFrame.
  iPureIntro.
  exact (Himpl HP2).
Qed.
