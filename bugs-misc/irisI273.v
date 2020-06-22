(* From iris.algebra Require Import base.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import array.

Import uPred.
Section foo.
Context `{!gen_heapG loc val Σ}.
Lemma foo r (x x1 : val):
  r ↦ x -∗ r ↦ x1.
  (* apply equiv_entails. f_equiv. *)
  iIntros "H".
  iRevert "H".
  iApply equiv_entails.
  f_equiv.

Qed.

Require Import
r ↦ (x, x0, x1, x2, x4)
"H" : r ↦ (x, x0, x1, x2, x4)
  --------------------------------------∗
  r ↦ (x, x0, x1, x2, z) *)


From iris.algebra Require Import base monoid.
From iris.algebra Require big_op.

Lemma works (n : nat) : n = n. (* Works: *)
elim: n => [^~ s].
(* elim: n => [^ s]. *)
Abort.

(* Splitting symbols. *)
Notation "'[' '^' o 'list]' k ↦ x ∈ l , P" := (big_op.big_opL o (λ k x, P) l)
  (at level 200, o at level 1, l at level 10, k, x at level 1, right associativity, format "[ ^ o  list]  k ↦ x  ∈  l ,  P") : stdpp_scope.

Lemma works (n : nat) : n = n. (* Works: *)
elim: n => [^~ s]. Restart.
elim: n => [^ s]. Abort.

(* Testcase for syntax and format. *)
Lemma big_opL_nil `{Monoid M o} {A : Type} (f : nat → A → M) :
  ([^o list] k↦y ∈ [], f k y) = monoid_unit.
Proof. done. Qed.

(* List notations. *)
Example foo : list nat := [].
Example bar : list nat := [2].
Example baz : list nat := [1; 2; 3].

(* The original notation does cause the conflict: *)
Notation "'[^' o 'list]' k ↦ x ∈ l , P" := (big_op.big_opL o (λ k x, P) l)
  (at level 200, o at level 1, l at level 10, k, x at level 1, right associativity, format "[^ o  list]  k ↦ x  ∈  l ,  P") : stdpp_scope.

Lemma big_opL_nil2 `{Monoid M o} {A : Type} (f : nat → A → M) :
  ([^o list] k↦y ∈ [], f k y) = monoid_unit.
Proof. done. Qed.

Lemma fails (n : nat) : n = n.
elim: n => [^ s].

Import big_op.
Lemma fails (n : nat) : n = n.
elim: n => [^~ s].
