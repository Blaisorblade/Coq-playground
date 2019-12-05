Require Import stdpp.list.
Require Import iris.algebra.base.
Section last_props.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

Lemma head_nonempty l : length l > 0 → is_Some (head l).
Proof. case: l => /= [/gt_irrefl //|a l _]. eauto. Qed.
Lemma last_nonempty h l t : l = h :: t → is_Some (last l).
Proof. move->. elim: t => /= [|a [|a' t] /= IHt]; eauto. Qed.
Lemma last_nonempty_2 l : length l > 0 → is_Some (last l).
Proof. rewrite -head_reverse -reverse_length. apply head_nonempty. Qed.
Lemma last_nonempty_again h t l : l = h :: t → is_Some (last l).
Proof. move->. apply: last_nonempty_2. cbn; lia. Qed.

Lemma last_none_empty l : last l = None → l = [].
Proof. by elim: l => [//|a [//|a' l IHl {}/IHl //]]. Qed.

Lemma last_concat l a : last l = Some a → ∃ l', l = l' ++ [a].
Proof.
  elim: l => [?| a' [??| a'' l IHl]]; simplify_eq/=; first by exists [].
  by move => {}/IHl [l' ->]; exists (a' :: l').
Qed.

(* Search _ (is_Some (head _)).
Search _ (length _ > 0).
Search _ (1 <= length _).
Search _ (0 < length _). *)
End last_props.
