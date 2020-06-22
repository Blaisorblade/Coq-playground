From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
Import bi.

Section sbi_instances.
  Context {PROP : sbi}.
  Implicit Types P Q R : PROP.

  (* Here [iApply] works. *)
  Lemma foo0 P : □ P -∗ P.
  Proof. iIntros "H". iApply "H". Qed.

  (* But here it fails! *)
  Lemma foo1 P : ▷ □ P -∗ ▷ P.
  Proof. iIntros "H". Fail iApply "H". iNext. iApply "H". Qed.

  (* Here's a possible fix, but I'm unsure whether it respects the interplay of
  FromAssumption, KnownLFromAssumption and KnownRFromAssumption,
  as it is not fully documented.
  Should I add this for both KnownLFromAssumption and KnownRFromAssumption? *)
  Global Instance from_assumption_later_later p P Q :
    FromAssumption p P Q → FromAssumption p (▷ P) (▷ Q)%I.
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption
      later_intuitionistically_if_2 => ->. exact: later_mono.
  Qed.
  Lemma foo P : ▷ □ P -∗ ▷ P.
  Proof. iIntros "H". iApply "H". Qed.

End sbi_instances.
