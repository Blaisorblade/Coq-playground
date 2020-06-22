Class Functor (F : Type -> Type) : Type :=
  {
    fmap : forall {A B : Type}, (A -> B) -> F A -> F B;
  }.

Class SubFunctor (F G : Type -> Type) `{Functor F} `{Functor G} : Type :=
  {
    inj : forall {A}, F A -> G A;
    prj : forall {A}, G A -> option (F A);
  }.

Notation "A <=== B" := (SubFunctor A B) (at level 100).

Definition whatever1 {F G} `{SubFunctor F G} := forall A, F A -> G A.
(* Fails *)
(* Definition whatever2 {F G} `{ F <=== G } := forall A, F A -> G A. *)


Require Coq.Vectors.Vector.

Definition splitVec {A n} (xs : Vector.t A (S n)): A * Vector.t A n :=
  match xs with
  (* | Vector.nil _ => _ (* fun A (a: A) => a *) *)
  | Vector.cons _ x n0 xs => (x, xs)
  end.

(* Alternative version. *)
Definition splitVec2 {A n} (xs : Vector.t A (S n)): A * Vector.t A n.
Proof.
  refine (
    match xs in (Vector.t _ n0) return S n = n0 -> A * Vector.t A n with
    | Vector.nil _ => fun HeqSn => _
    | Vector.cons _ x n0 xs => _
    end eq_refl).
  - discriminate.
  - intros HeqSn. (* Type: S n = S n0 *)
    assert (n = n0) as Heqn by now injection HeqSn.
    rewrite Heqn. exact (x, xs).
Defined.


Fixpoint zip {A B n} (xs: Vector.t A n) :
  Vector.t B n -> Vector.t (A * B) n :=
  match xs in (Vector.t _ n0) return Vector.t B n0 -> Vector.t (A * B) n0 with
  | Vector.nil _ => fun ys => Vector.nil _
  | Vector.cons _ x n0 xs => fun ys =>
    let '(y, ys') := splitVec ys in
    Vector.cons _ (x, y) _ (zip xs ys')
  end.

Notation "⊤" := True : dms_scope.
Notation " {@ T1 } " := ( and T1 True ) (format "{@  T1  }"): dms_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (and T1 (and T2 .. (and Tn True)..))
  (* (format "'[v' {@  '[' T1 ']'  ;  '//' T2  ;  '//' ..  ;  '//' Tn  } ']'") *)
   : dms_scope.
Open Scope dms_scope.
Close Scope dms_scope.
Delimit Scope dms_scope with dms.
Check {@ True ; True -> False ; False } % dms.


Inductive ty := | TTop | TNat | TAnd (T1 T2 : ty).
Bind Scope ty_scope with ty.

Notation "⊤" := TTop : ty_scope.
Notation " {@ T1 } " := ( TAnd T1 TTop ) (format "{@  T1  }"): ty_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (TAnd T1 (TAnd T2 .. (TAnd Tn TTop)..))
  (format "'[v' {@  '[' T1 ']'  ;  '//' T2  ;  '//' ..  ;  '//' Tn  } ']'") : ty_scope.
Open Scope ty_scope.
Close Scope ty_scope.
Delimit Scope ty_scope with ty.
Check {@ TNat ; TNat ; TNat } % ty.

From Coq Require Export Bool.
From Coq.ssr Require Export ssreflect.

Lemma foo25 P Q b b' :
  reflect P b -> reflect Q b' ->
  reflect (P /\ Q) (b && b').
Proof. inversion 1; inversion 1; cbn; constructor; intuition. Qed.
About reflect.

Require Import stdpp.base.
Section foo2.
Context `(R: relation A) `{!Reflexive R}.
Fail Check notExists.
End foo2.
Check id.
Lemma foo {A} (a: A) : a = a. Proof. easy. Qed.
(* Require Import Omega.

Lemma foo07 (n n0 n1 n2 n3 n4: nat):
n + (n0 + n1) = 0 ->
n2 + (n3 + n4) = 0 ->
n0 + n3 + n + n2 + (n1 + n4) = 0.
Proof. omega. Qed. *)

(* Require Import Program. *)
(* Require Import stdpp.vector. *)

Require Import stdpp.base.

(* Tactic Notation "uapply" uconstr(H) "by" tactic3(tac2) :=
  lazymatch type of H with context f [forall _, ?b] => simple apply H; last 1 [idtac] || tac2 | _ => simple apply H end.
(* Tactic Notation "usplit" tactic3(tac) "then" tactic3(tac2) :=
  tac; let n := numgoals in tryif guard n = 0 then idtac else [> tac2.. |]. *)
Lemma foo00 (T: Prop) (H: T): T.
Proof. uapply H by done. Qed.
Lemma foo002 (T: nat -> Prop) (H: forall n, T n): T 0.
Proof. uapply H by done. Qed.
Lemma foo01 (T: nat → Prop) (H: forall n, True -> True -> 1 = 1 -> T n): T 0.
Proof. lazymatch type of H with context f [forall a, _] => idtac f end.
 uapply H by done. done. Qed.
lazymatch type of H with context [?A -> ?B] => apply H; last 1 [idtac] || done | _ => apply H end.
 unshelve (apply H; last shelve; done). Unshelve. Grab Existential. Qed.
 usplit apply H then done.
 Qed.
 (* (fail || [> done .. | ]). *)
(* simple apply H; (fail || [> solve [ idtac ] .. | ]). *)
usplit simple apply H then ([> done .. | ]).
usplit simple apply H then [> solve [ idtac ] .. | ].
usplit simple apply H. (fail || [> done .. | ]).
simple apply H. first [[> done .. ]].
simple apply H; [> done .. | ].
simple apply H; fail || [> solve [ done ] .. | ]. *)

From iris.algebra Require Import ofe.

From iris.heap_lang Require Import proofmode.
Program Definition bar {A} (xs: list A) (i : nat) (Hle : i < length xs): A :=
  match (xs !! i) with
  | Some x => x
  | None => _
  end.
Next Obligation.
  intros * Hle res Heqo. symmetry in Heqo. exfalso.
  move: Heqo. rewrite /res lookup_ge_None. lia.
Qed.

Compute (bar [1; 2; 3] 1).
Lemma foo3 {A} (xs: list A) (i : nat) : i < length xs → A.
Proof.
intros Hle.
destruct (xs !! i) as [x|] eqn:?. exact x.
exfalso.
Fail rewrite lookup_ge_None in Heqo.
move: Heqo. rewrite lookup_ge_None. lia.
Defined.
(* rewrite lookup_ge_None => Heqo.
lookup_lt_is_Some_2
apply lookup_lt_is_Some_2. *)
Compute ((-3) `mod` 4).
Axiom eq0: @eq Type nat nat.
Lemma cast : forall {A B}, A = B -> A -> B. now intros ?? ->. Defined.
Eval cbv in (cast eq_refl 1). (* = 1 : nat *)
Eval cbv in (cast eq0 (1%nat)). (* match ... *)
Print cast.
Print eq_sym.
Print eq_rect_r.
Print eq_rect.
Lemma foo4: nat = bool -> nat -> bool. Proof. now intros -> . Qed.
Fixpoint bad n : 0 = n. apply bad. Fail Qed. Abort.

Require Import Program.
Print foo.
About eq_rec_r.
Print LoadPath.
From iris.algebra Require Import ofe.
Search _ (?A = ?B -> ?A -> ?B).
Program Definition bar: nat = bool -> nat -> bool :=
  fun H n => _.


Inductive foo5 : Type := A | B.
Require Import Arith Program.Equality.
Goal ~(A = B). solve [inversion 1]. Qed.

Inductive le' : nat -> nat -> Prop :=
| le'_0 (n : nat) : le' 0 n
| le'_S (n m : nat) : le' n m -> le' (S n) (S m).

Fixpoint le'_irrelevant (n m : nat) (p q : le' n m) : p = q.
Proof.
  dependent destruction p; dependent destruction q.
  - reflexivity.
  - f_equal; apply le'_irrelevant.
Defined.
Require Import stdpp.base.
From iris.algebra Require Import ofe.

Module local.
Example foo : 1 = 1. let x := eval red in (1 + 1) in idtac x. auto. Qed.
Example bar : 1 = 1 := ltac:((refine (_)); auto).
(* Notation "'magic' P" := (ltac:(refine (uconstr:(P)); auto))(at level 80).
Example baz : 1 = 1 := magic _. *)

Notation "'magic' P" := (ltac:(refine ((P)); auto))(at level 80).
Tactic Notation "magic" uconstr(P) := refine P; auto.
Example baz : 1 = 1 := ltac:(magic (_)).

End local.
From iris.algebra Require Import ofe.

Module ExtReasoning.
Class BundledExtensionalSetoid (A B C : Type) (coerce : C -> A -> B) `{!Equiv B} `{!Equiv C} :=
  b_es_app f g x : f ≡ g → coerce f x ≡ coerce g x .

Instance Extensional_ofe_mor {A B : ofeT} : BundledExtensionalSetoid A B (A -n> B) (ofe_mor_car _ _).
Proof. by move => *. Qed.

Class ExtensionalSetoid (A B : Type) `{!Equiv B} (R : relation (A -> B)) :=
  es_app f g x: R f g → f x ≡ g x.
(* As usual, there's nothing OFE-specific here. *)
Instance Extensional_discrete_fun {A} {B : ofeT} : ExtensionalSetoid A B (≡@{A -d> B}).
Proof. by move => *. Qed.

(* Testcases *)
Lemma f_equiv_app_ofe_mor {A B} (f g : A -n> B) x: f ≡ g → f x ≡ g x.
Proof.
  intros. apply H. Restart.
  intros. apply b_es_app. auto. Restart.
  (* Should term side matter: *)
  intros. revert x. change (f ≡ g). by auto.
Qed.

Lemma f_equiv_app_discrete_fun {A} {B: ofeT} (f g : A -d> B) x: f ≡ g → f x ≡ g x.
Proof.
  intros. apply H. Restart.
  intros. apply es_app. auto. Restart.
  (* Should term side matter: *)
  intros. revert x. change (f ≡ g). by auto.
Qed.

  Import EqNotations.
  Locate "rew".
  About eq_rect.
  Search _ (?a = ?b -> ?b -> ?a).
  Search _ (?a = ?b -> ?b = ?a).
  (* Program Definition foo (A B C : Type) (eq : C = (A -> B)) : (A -> B) -> C.
  intro f.
  refine (rew [id] eq_sym eq in f). *)
  Class ExtensionalSetoid1 (A B C : Type) (eq : C = (A -> B)) `{!Equiv B} `{!Equiv C} := {
    es_app1 (f g : A → B) x:
    (rew eq_sym eq in f) ≡@{C} (rew [id] eq_sym eq in g) →
    f x ≡ g x
  }.
  Instance Extensional_discrete_fun45 {A} {B : ofeT} : ExtensionalSetoid1 A B (A -d> B) eq_refl.
  Proof. split. intros f g x H. apply H. Defined.
  Print Extensional_discrete_fun45.
  Eval hnf in @Extensional_discrete_fun45.
  Lemma f_equiv_app_discrete_fun3 {A} {B: ofeT} (f g : A -d> B) x: f ≡ g → f x ≡ g x.
  Proof.
    intros. apply H. Restart.
    intros.
    apply es_app1; cbn.
    (* apply (@es_app _ _ _ _ _ _ _ f g x). *)
    (* apply (@es_app _ _ _ _ _ _ Extensional_discrete_fun f g x). *)
    (* apply es_app. *)
    auto.
  Qed.

  Class ExtensionalSetoid2 (A B : Type) `{!Equiv B} (eq : Equiv (A -> B)) := {
    es_app2 f g x: f ≡ g → f x ≡ g x
  }.
  Program Definition e {A} {B: ofeT} : Equiv (A -> B).
    change (A → B) with ((A -d> B) : Type). apply _. Defined.
  Instance Extensional_discrete_fun2 {A} {B : ofeT} : ExtensionalSetoid2 A B e.
  Proof. split. intros f g x H. apply H. Qed.

  Lemma f_equiv_app_discrete_fun2 {A} {B: ofeT} (f g : A -d> B) x: f ≡ g → f x ≡ g x.
  Proof.
    intros. apply H. Restart.
    intros.
    Fail apply es_app2. cbn.
    apply es_app.
    (* apply (@es_app _ _ _ _ _ _ _ f g x). *)
    (* apply (@es_app _ _ _ _ _ _ Extensional_discrete_fun f g x). *)
    (* apply es_app. *)
    auto.
  Qed.
End ExtReasoning.

Section foo.
Context {A B C: ofeT} (f g : A -n> B) (h : B -n> C).
  Instance: Proper (pointwise_relation _ (≡)) f := _.
  Instance: Proper (pointwise_relation _ (≡)) g := _.
  Instance: Proper (pointwise_relation _ (≡)) h := _.

  Lemma foo45 x : f ≡ g → f x ≡ g x.
  Proof.
    intros Heq.
    Fail rewrite Heq.
    Fail setoid_rewrite Heq.
    apply Heq. (* this work-around doesn't work in bigger contexts. *)
  Qed.

  (* Ditto here: *)
  Lemma foo' : f ≡ g → ∀ x, f x ≡ g x.
  Proof.
    intros Heq.
    Fail rewrite Heq.
    Fail setoid_rewrite Heq.
    apply Heq.
  Qed.

  Lemma bar45 x : f ≡ g → h (f x) ≡ h (g x).
  Proof.
    intros Heq.
    Fail rewrite Heq.
    Fail setoid_rewrite Heq.
    Fail apply Heq. (* Of course *)
    (* workaround: call stdpp's f_equiv by hand. *)
    f_equiv. apply Heq.
  Qed.
End foo.

Require Import D.Dot.unary_lr.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Export environments.

(* Ltac iStartProofSbi := iStartProof;
  lazymatch goal with
  | |- @envs_entails ?b _ _ =>
    let b2 := fresh in evar (b2 : sbi);
    let b2' := eval unfold b2 in b2 in
    let t := constr:(sbi_bi b2') in (unify b t || fail "not a SBI entailment")
  end. *)
Ltac iStartProofSbi :=
  iStartProof;
  match goal with
  | |- @envs_entails ?b1 _ _ =>
    let b2  := fresh in evar (b2 : sbi);
    let b2' := eval unfold b2 in b2 in
    clear b2; tryif unify b1 (sbi_bi b2') then idtac else fail "not a SBI entailment"
  end.

  (* evar (b2: sbi); let t := eval unfold b2 in open_constr:(sbi_bi b2) in unify b t || fail "not a SBI entailment"
      let e := fresh in evar (e:id T);
      let e' := eval unfold e in e in clear e; iIntoEmpValid (t e') *)

Lemma test1 `{PROP : bi} (k : nat) (Φ : nat → PROP) :
  Φ k -∗ Φ (S k).
Proof.
Fail iStartProofSbi. Abort.

Lemma test1 `{PROP : sbi} (k : nat) (Φ : nat → PROP) :
  Φ k -∗ Φ (S k).
Proof.
iStartProofSbi. Abort.

Lemma test {Σ} (k : nat) (Φ : nat → iProp Σ) : Φ k -∗ Φ (S k).
Proof.
iStartProof.
iStartProofSbi. Abort.

From iris.proofmode Require Export coq_tactics.
Local Tactic Notation "iForallRevert" ident(y) :=
  let err x :=
    intros x;
    iMatchHyp (fun H P =>
      lazymatch P with
      | context [x] => fail 2 "iRevert:" x "is used in hypothesis" H
      end) in
  iStartProof;
  first [let A := type of y in idtac|fail "Variable" y "not in scope"];
  let A := type of y in
  lazymatch type of A with
  | Prop => revert y; first [apply tac_pure_revert|err y]
  | _ => revert y; first [apply tac_forall_revert|err y]
  end.
Lemma test1 `{PROP : bi} (k : nat) (Φ : nat → PROP) :
  Φ k -∗ Φ (S k).
Fail iForallRevert z.
iForallRevert k.
Abort.

(* Fail match goal with
| |- @envs_entails (sbi_bi _) _ _ => idtac
| |- @envs_entails _ _ _ => fail "not a SBI entailment"
end. *)


(* iLöb as "IH".
match goal with
| |- @envs_entails ?b _ _ =>
evar (b': sbi); let t := eval unfold b' in (sbi_bi b') in unify b t || fail "not a SBI entailment"
end.
| |- @envs_entails _ _ _ =>
end.
match goal with
| |- @envs_entails (sbi_bi _) _ _ => idtac
| |- @envs_entails _ _ _ => fail "not a SBI entailment"
end. *)

Section Foo.
  Context `{HdlangG: dlangG Σ}.
  Definition bar46 (u : leibnizO vl): iProp Σ := (u ≡ u ∧ True)%I.
  Definition uAu (u : leibnizO vl): iProp Σ :=
    tc_opaque
      (* (bar u). *)
      ⟦TSel (pv u) "A"⟧ ids u.

  Instance into_sep_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
    IntoSep P Q1 Q2 → IntoSep (tc_opaque P) Q1 Q2 := id.

  Goal ∀ (u : leibnizO vl), ∃ Q1 Q2, IntoSep (tc_opaque (⟦TSel (pv u) "A"⟧ ids u)) Q1 Q2.
  Proof.
    intros. eexists _, _.
    apply into_sep_tc_opaque.
    (* apply _. *)
  (* Qed. *)
  Abort.
  About interp.

  Lemma later_not_UAU v: uAu v -∗ ▷ False.
  Fail iIntros "[_ Hvav]".
  Abort.
End Foo.
