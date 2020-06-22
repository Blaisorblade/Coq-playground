From iris.algebra Require Import ofe.

Instance equiv_ext_discrete_fun {A B} :
  subrelation (≡@{A -d> B}) (pointwise_relation A (≡)).
Proof. done. Qed.

Instance dist_ext_discrete_fun {A B n} :
  subrelation (dist n (A := A -d> B)) (pointwise_relation A (dist n)).
Proof. done. Qed.

Instance equiv_ext_discrete_fun_forall {A B} :
  subrelation (≡@{A -d> B}) (forall_relation (const (≡))).
Proof. done. Qed.
Instance dist_ext_discrete_fun_forall {A B n} :
  subrelation (dist n (A := A -d> B)) (forall_relation (const (dist n))).
Proof. done. Qed.

Instance equiv_ext_ofe_mor {A B} :
  subrelation (≡@{A -n> B}) (pointwise_relation A (≡)).
Proof. done. Qed.

Instance dist_ext_ofe_mor {A B n} :
  subrelation (dist n (A := A -n> B)) (pointwise_relation A (dist n)).
Proof. done. Qed.

Instance equiv_ext_ofe_mor_forall {A B} :
  subrelation (≡@{A -n> B}) (forall_relation (const (≡))).
Proof. done. Qed.

Module foo1.
Section discrete_fun.
Context {A B C: ofeT} (f g : A -d> B) (h : B -d> C).
  (* Instance: Proper (pointwise_relation _ (≡)) f := _.
  Instance: Proper (pointwise_relation _ (≡)) g := _. *)
  Context `{!Proper ((≡) ==> (≡)) h}.

  (* About forall_relation.
  About equiv_ext_ofe_mor . *)

  Lemma foo x : f ≡ g → f x ≡ g x.
  Proof. by move->. Qed.

  (* Ditto here: *)
  Lemma foo' : f ≡ g → ∀ x, f x ≡ g x.
  Proof.
    intros Heq.
    Fail rewrite Heq.
    by setoid_rewrite Heq.
  Qed.

  Lemma bar x : f ≡ g → h (f x) ≡ h (g x).
  Proof.
    intros Heq.
    by rewrite Heq.
    (* Fail setoid_rewrite Heq.
    Fail apply Heq. (* Of course *)
    (* workaround: call stdpp's f_equiv by hand. *)
    f_equiv. apply Heq. *)
  Qed.
End discrete_fun.
End foo1.

Section foo.
Context {A B C: ofeT} (f g : A -n> B) (h : B -n> C).

  Lemma foo1 x : f ≡ g → f x ≡ g x.
  Proof.
    intros Heq.
    Fail rewrite ->Heq.
    Fail rewrite Heq.
    pose proof (ofe_mor_car_proper f g Heq x x (reflexivity _)) as Heq'.
    Fail rewrite Heq'.
    rewrite ->Heq'.
    (* Undo *)
    Restart. intros Heq.
    pose proof (ofe_mor_car_proper f g Heq x x (reflexivity _)) as Heq'.
    unfold ofe_mor_car in Heq'.
    by rewrite Heq'.
  Qed.

  Global Instance ofe_mor_car_proper2 :
  Proper ((≡) ==> (≡@{A}) ==> (≡@{B})) (ofe_mor_car _ _) := ne_proper_2 _.

  Global Instance ofe_mor_car_proper3 :
  Proper ((≡) ==> (≡@{A}) ==> (≡@{B})) (fun x => ofe_mor_car _ _ x) := ne_proper_2 _.
  About ofe_mor_car_proper .

  (* About forall_relation.
  About equiv_ext_ofe_mor . *)
  Lemma foo x : f ≡ g → f x ≡ g x.
  Proof.
    intros Heq.
    pose proof ofe_mor_car_proper2 as H.
    unfold ofe_mor_car in H.
    Fail rewrite Heq.
    pose proof (ofe_mor_car_proper2 f g Heq x x (reflexivity _)) as Heq'.
    Fail rewrite Heq'.
    unfold ofe_mor_car in Heq'.
    rewrite Heq'.

    by rewrite -(ofe_mor_car_proper3 f g Heq x x (reflexivity _)).
  Qed.

  Instance: Proper (pointwise_relation _ (≡)) f := _.
  Instance: Proper (pointwise_relation _ (≡)) g := _.
  Instance: Proper (pointwise_relation _ (≡)) h := _.
  (* Ditto here: *)
  Lemma foo' : f ≡ g → ∀ x, f x ≡ g x.
  Proof.
    intros Heq.
    Fail rewrite Heq.
    Fail setoid_rewrite Heq.
    apply Heq.
  Qed.

  Lemma bar x : f ≡ g → h (f x) ≡ h (g x).
  Proof.
    intros Heq.
    Fail rewrite Heq.
    Fail setoid_rewrite Heq.
    Fail apply Heq. (* Of course *)
    (* workaround: call stdpp's f_equiv by hand. *)
    f_equiv. apply Heq.
  Qed.
End foo.
