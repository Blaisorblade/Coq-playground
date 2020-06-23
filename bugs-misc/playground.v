From iris.si_logic Require Import siprop bi.

(** Taken from [base_logic.bi]. *)
(** New unseal tactic that also unfolds the BI layer.
    TODO: Can we get rid of this? *)
Ltac unseal := (* Coq unfold used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp; simpl; unfold sbi_emp; simpl;
  unfold siProp_emp, bupd, bi_bupd_bupd, bi_pure,
  bi_and, bi_or, bi_impl, bi_forall, bi_exist,
  bi_sep, bi_wand, bi_persistently, sbi_internal_eq, sbi_later; simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
  sbi_internal_eq, sbi_sep, sbi_wand, sbi_persistently; simpl;
  unfold plainly, bi_plainly_plainly; simpl;
  siProp_primitive.unseal.

Local Arguments siProp_holds !_ /.

Lemma notnot (P : siProp) : (⊢ (P → False) → False) → ¬¬P 0.
Proof.
  case; unseal.
  have Hle: 0 ≤ 0 by [lia] => /(_ 0 I 0 Hle) {Hle} HNotNotP0' HNotP0.
  apply: HNotNotP0'.
  move => n Hnl0 HP0; apply: HNotP0.
  move: HP0; have {Hnl0} ->: n = 0 by [lia].
  apply.
Qed.

Lemma notnot_inv (P : siProp) : ¬¬P 0 → ⊢ (P → False) → False.
Proof.
  rewrite /not => HNotNotP0; split; unseal => _ _ n _.
  have Hle': 0 ≤ n by [lia]=> /(_ 0 Hle') {Hle' n}.
  exact HNotNotP0.
Qed.

Lemma notnot_equiv (P : siProp) : (⊢ (P → False) → False) ↔ ¬¬P 0.
Proof. split; eauto using notnot, notnot_inv. Qed.
