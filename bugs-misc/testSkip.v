Definition foo : nat. skipType. Defined.
Eval cbv in @skip False.

Lemma bar : 1 = 2. skip. Qed.
Lemma baz : @eq Type nat bool. skip. Qed.
About nat.
About bool.

Definition cast {A B} : A = B -> A -> B :=
  fun Heq a => match Heq with eq_refl => a end.

Eval cbv in (cast eq_refl 1). (* = 1 : nat *)
Definition err : bool := cast baz 0.
Eval cbv in err.
