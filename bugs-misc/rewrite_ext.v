From Coq Require Import Morphisms Setoid.
From Coq.ssr Require Import ssreflect.
Section Abstract.

  Definition D (A: Type) := A -> Prop.
  Variable eqD: forall {A: Type}, (A -> Prop) -> (A -> Prop) -> Prop.

  Context {proper: forall {A}, subrelation eqD (pointwise_relation A iff)}.
  Context `{rew: forall {A: Type}, RewriteRelation (@eqD A)}.

  Infix "≡" := eqD (at level 89, no associativity).

  Goal forall {A: Type} (P Q: D A) x,
      Q ≡ P -> P x -> Q x.
  Proof.
    intros * EQ H.
    rewrite EQ.
    exact H.
  Qed.

  Variable F G: forall {A} (P: D A), D A.

  Goal
    forall (A : Type) (P : D A) x,
      F (G P) ≡ G (F P) ->
      G (F P) x ->
      F (G P) x.
  Proof.
    intros * EQ H.
    rewrite EQ.
    exact H.
  Qed.

End Abstract.

(* We are currently working with heterogeneous relations *)
Definition relation (A B : Type) := A -> B -> Prop.

(* We work with our relations up-to extensional equality *)
Definition subrel {A B} (R S : relation A B) : Prop :=
  forall (x : A) (y : B), R x y -> S x y.
Definition eq_rel {A B} (R : A -> B -> Prop) (S : A -> B -> Prop) :=
  subrel R S /\ subrel S R.
Infix "≡" := eq_rel (at level 89, no associativity).

(* My problem is quite trivial: since this notion of equivalence of relations is basically double pointwise [iff],
   I want to be able to rewrite it as such.
   So for instance consider the following idiotic goal:
 *)
Goal forall {A B: Type} (R S: relation A B) x y,
    R ≡ S -> S x y -> R x y.
Proof.
  intros A B R S x y EQ H.
  (* We want to rewrite EQ, which of course fails without help *)
  Fail rewrite -> EQ.
Abort.

(* It's a bit of a different case from my usual [Proper] instances, but the error message nicely tells me what's needed:
   [eq_rel] is indeed a subrelation of pointwise iff.
 *)
Instance eq_rel_rewrite {A B}: subrelation eq_rel (pointwise_relation A (pointwise_relation B iff)).
Proof.
  repeat intro; destruct H; split; intro; [apply H | apply H0]; auto.
Qed.
Instance rewrite_eq_rel {A B}: RewriteRelation (@eq_rel A B) := {}.

Goal forall {A B: Type} (R S: relation A B) x y,
    R ≡ S -> S x y -> R x y.
Proof.
  intros A B R S x y EQ H.
  (* And indeed things works nicely *)
  rewrite EQ.
  exact H.
Qed.

(* Now here is where I get confused. Consider the transpose operation that flips a relation *)
Definition transpose {A B: Type} (R: A -> B -> Prop): B -> A -> Prop :=
  fun b a => R a b.
Notation "† R" := (transpose R) (at level 5).

(* I have a morphism on relations that commutes with [transpose], and want to rewrite this equation *)
Goal
  forall (A B : Type) (R : relation A B) (F: forall {A B}, (A -> B -> Prop) -> (A -> B -> Prop)) x y,
    F († R) ≡ † (F R) ->
    † (F R) x y ->
    F († R) x y.
Proof.
  intros * EQ H.
  (* It is as far as I can tell, the exact same situation as previously, but with
     [R] = [F †R] and [S] = [† (F R)]
     Yet, it now fails:
   *)
  Fail setoid_rewrite EQ. (* Tactic failure: setoid rewrite failed: Nothing to rewrite. *)

  rewrite EQ.
  exact H.
Qed.
