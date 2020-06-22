From Coq.ssr Require Import ssreflect.
From Coq Require Import Utf8.

Tactic Notation "split_and" "?" := repeat match goal with | |- _ ∧ _ => split end.

Goal True.
have: 1 = 1 ∧ 2 = 2 ∧ 3 = 3 ∧ 4 = 4.
split_and?; first 1 last. (* Goal 2 becomes first *)
Restart.
have: 1 = 1 ∧ 2 = 2 ∧ 3 = 3 ∧ 4 = 4.
split_and?; first 4 last. (* No rotation happens. *)
Abort.

From stdpp Require Import base list.
Lemma foo {A B} {xs ys : list A} (f : A → B) :
  f <$> (xs ++ ys) = (f <$> xs) ++ (f <$> ys).
Proof.
  (* Works with [cut] or [have], fails with [suff], because [suff]
  generalizes the goal over arbitrary typeclass instances, unlike [have].
  In fact, [have] has the same issue as [suff] after [Set SsrHave NoTCResolution].
   *)
  cut (f <$> (xs ++ ys) = (f <$> xs) ++ (f <$> ys)).
  by apply.
  by apply fmap_app.
  Restart.

  have Hgoal: f <$> (xs ++ ys) = (f <$> xs) ++ (f <$> ys).
  by apply fmap_app.
  by apply Hgoal.
  Restart.

  suff Hgoal: f <$> (xs ++ ys) = (f <$> xs) ++ (f <$> ys).
  Show.
(*
2 subgoals

  A : Type
  B : Type
  xs, ys : list A
  f : A → B
  Hgoal : ∀ f0 f1 f2 : FMap list, f <$> xs ++ ys = (f <$> xs) ++ (f <$> ys)
  ============================
  f <$> xs ++ ys = (f <$> xs) ++ (f <$> ys)

subgoal 2 is:
 ∀ f0 f1 f2 : FMap list, f <$> xs ++ ys = (f <$> xs) ++ (f <$> ys) *)

  by apply Hgoal.
  intros. Fail apply fmap_app.
Abort.
