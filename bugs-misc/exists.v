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
