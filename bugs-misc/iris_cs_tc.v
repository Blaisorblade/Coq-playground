(* From iris.proofmode Require Import notation.
Notation "" := id.

Notation "" := id (only printing).

From iris.proofmode Require Export notation.
From iris.proofmode Require Import coq_tactics environments.

Notation "" := Enil (only printing) : proof_scope.
  Notation "" := id.
(* This [Require Import] is not a no-op: it exports typeclass instances from
these files. *)
From iris.proofmode Require Import class_instances_bi class_instances_sbi frame_instances modality_instances. *)


(* Require Import stdpp.base. *)
Section foo.
Inductive foo := C : foo -> foo.
Notation "" := foo.

Fixpoint th1 (x y: foo) {struct x} : foo with th2 (x y : foo) {struct x}: foo.
Proof.
Fail Guarded.
intros x y; destruct x as [x].
Fail Guarded.
exact (th1 x x).
Fail Guarded.
intros x y; destruct x as [x].
Fail Guarded.
exact (th2 x x).
Fail Guarded.
Show Proof.
Fail Guarded.
Qed.
Print th1.

Theorem th1 : foo -> foo -> foo with th2 : foo -> foo -> foo.
Proof.
Fail Guarded.
intros x y; destruct x as [x].
Fail Guarded.
exact (th1 x x).
Fail Guarded.
intros x y; destruct x as [x].
Fail Guarded.
exact (th2 x x).
Fail Guarded.
Show Proof.
Fail Guarded.
Qed.
Print th1.

Definition th1' : foo -> foo -> foo :=
(fix th1 (x y : foo) {struct x} : foo :=
   match x with
   | C x0 => th1 x0 x0
   end
with th2 (x y : foo) {struct x} : foo :=
   match x with
   | C x0 => th2 x0 x0
   end
 for th1).

th2 : foo -> foo -> foo
(* Problem based on a failure in `namespace_map`. The goal also fails
to typecheck if we replace [set_disj coPset] by [nat]. (The goal
typechecks in branch `swasey/sets`.) *)
From iris.algebra Require Import coPset.
Module Discrete_problem.
(* Record my_prod {A : Type} := MyProd { my_l : A; my_r : set_disj coPset }. *)
Arguments my_prod : clear implicits.
Arguments MyProd {_} _ _.
Definition my_inl {A : cmraT} (a : A) : my_prod A := MyProd a ε.
Section ofe.
  Context {A : ofeT}.
  Instance my_dist : Dist (my_prod A) := λ n x y,
    my_l x ≡{n}≡ my_l y ∧ my_r x = my_r y.
  Instance my_equiv : Equiv (my_prod A) := λ x y,
    my_l x ≡ my_l y ∧ my_r x = my_r y.
  Lemma my_prod_ofe_mixin : OfeMixin (my_prod A).
  Proof. by apply (iso_ofe_mixin (λ x, (my_l x, my_r x))). Qed.
  Canonical Structure my_prodO := OfeT (my_prod A) my_prod_ofe_mixin.
End ofe.
Arguments my_prodO : clear implicits.
Fail Goal ∀ {A : cmraT} (a : A), Discrete a → Discrete (my_inl a).
Goal ∀ {A : cmraT} (a : A), @Discrete A a → @Discrete (my_prodO A) (my_inl a).
Abort.
End Discrete_problem.
