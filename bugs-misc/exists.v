From mathcomp Require Import ssreflect ssrnat eqtype ssrbool seq tuple.
Import EqNotations.

Print val.
Print sval.
Lemma sig_bool_eq {A : Type} {P : A -> bool} (x y: {z | P z}): val x = val y -> x = y.
Proof. apply val_inj. Restart.
Proof.
  case: x y => [x Px] [y Py] /= Hxy; destruct Hxy.
  apply eq_exist_uncurried. exists (Logic.eq_refl _).
  apply eq_irrelevance.
Qed.

Require Import ProofIrrelevance.

Section dep_pair.
Context {A : Type} {P : A -> Prop}.
Definition dep_pair := ex_intro P.
Lemma dep_pair_eq (a1 a2 : A) p1 p2: a1 = a2 -> dep_pair a1 p1 = dep_pair a2 p2.
Proof.
  intros ->.
  (* Now f_equal can reduce the equality to a homogeneous one, so it works. *)
  f_equal.
  apply proof_irrelevance.
Qed.
End dep_pair.
(*
Print sig.
Print sigT. *)
