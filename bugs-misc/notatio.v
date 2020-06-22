Notation "( '⊢@{' PROP } )" := (eq (A:=PROP)) (PROP at level 200, only parsing).
Notation "( '⊢@{' PROP } P )" := (eq (A:=PROP) P) (PROP at level 200, only parsing).
Print Grammar constr.
(* Notation "(⊢@{ PROP } )" := (eq (A:=PROP)) (only parsing).
Definition test PROP := (⊢@{PROP}). *)

(* Notation "'(⊢@{' PROP } )" := (eq (A:=PROP)) (only parsing).
Notation "'(⊢@{' PROP } Q )" := (Q) (only parsing). *)
Definition test := (⊢@{Prop}).
Definition test2 := (⊢@{Prop} True).
From iris.bi Require Import interface.
Definition test3 (PROP : bi) := ( ⊢@{PROP} True)%I.
(* Definition test PROP := ( ⊢@{ PROP } ). *)
Lemma embed_emp_valid_inj (PROP2 : bi) (P : PROP2) : (⊢@{PROP2} ⎡P⎤) → ⊢ P.

(* Definition test PROP := ('⊢@{'PROP}). *)



Reserved Notation "P '⊢@{' PROP } Q" (at level 99, Q at level 200, right associativity).

(* Reserved Notation "('⊢@{' PROP } )". *)

Local Notation "⎡ P ⎤" := (P) : bi_scope.

