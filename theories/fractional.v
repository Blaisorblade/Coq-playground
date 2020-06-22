From iris.base_logic Require Import invariants.
(* From iris.bi Require Import ascii. *)
From iris.algebra Require Import ofe cmra frac agree gmap.

Definition fractionalR (o : ofeT) : cmraT := prodR fracR (agreeR (leibnizO o)).
Lemma fractional_op A p q (rv : agreeR (leibnizO A)) :
  (p, rv) ⋅ (q, rv) ≡ ((p + q)%Qp, rv).
Proof. by rewrite -pair_op agree_idemp. Qed.

Section sec.
Context {A : ofeT} `{!inG Σ (fractionalR A)}.

Lemma own_fractional_sep γ p q (rv : agreeR (leibnizO A)) :
  own γ ((p + q)%Qp, rv) ⊣⊢
  own γ (p, rv) ∗ own γ (q, rv).
Proof. by rewrite -own_op fractional_op. Qed.
End sec.

(* Copied from Iris [gmap], I don't have it in my old version. *)
Lemma singleton_op `{Countable K} {A : cmraT} (i : K) (x y : A) :
  {[ i := x ]} ⋅ {[ i := y ]} =@{gmap K A} {[ i := x ⋅ y ]}.
Proof. by apply (merge_singleton _ _ _ x y). Qed.

Section sec.
Context {A : ofeT} `{Countable L} `{!inG Σ (gmapR L (fractionalR A))}.

Definition frac_pack (a : L) (p : frac) (rv : agreeR A)  :=
  singletonM (K := L) (M := gmap L (fractionalR _)) a (p, rv).

Lemma frac_pack_op p q (rv : agreeR (leibnizO A)) (a : L) :
  frac_pack a (p + q) rv ≡ frac_pack a p rv ⋅ frac_pack a q rv.
Proof. by rewrite /frac_pack -fractional_op singleton_op. Qed.

Lemma own_frac_pack_sep γ p q (rv : agreeR (leibnizO A)) (a : L) :
  own γ (frac_pack a (p + q)%Qp rv) ⊣⊢
  own γ (frac_pack a p rv) ∗ own γ (frac_pack a q rv).
Proof. by rewrite -own_op frac_pack_op. Qed.
End sec.
