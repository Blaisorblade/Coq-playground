From iris.proofmode Require Import tactics.
From iris.base_logic Require Import iprop.

Section foo.
  Context `(Σ : gFunctors).
  Definition foo : iProp Σ := ∃ (x : nat), x ≡ 0.
End foo.
Opaque foo.

Lemma bar Σ : ⊢ foo Σ .
Proof.
  by iExists 0. Restart.
  iStartProof.
  eapply coq_tactics.tac_exist.
  Fail apply (class_instances_bi.from_exist_exist _).
  apply: (class_instances_bi.from_exist_exist _).
  (* notypeclasses refine (class_instances_bi.from_exist_exist _). *)
  by eexists 0.
Qed.
