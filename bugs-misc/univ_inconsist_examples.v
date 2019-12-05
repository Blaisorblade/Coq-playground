
(* From iris.algebra Require Import ofe. *)

Require Import Program.
(* list, but with an index instead of a parameter. *)
Inductive list : Type -> Type :=
| nil {A} : list A | cons {A} : A -> list A -> list A.

Definition D := { X : Type & list X }.
Fail Program Definition d1 : D := existT _ D _.

Definition D1 (T : Type) (F : T -> Type): Type := { X : T & F X }.
Print D1.
Definition D2 := D1 D (fun P => {x : D & projT1 P * projT1 x})%type.
Print D2.
Print D1.
Print D.
(* Only fails with our modified list. *)
Fail Definition d2 := cons (@existT Type (fun X => list Type) (list Type) (cons D nil)) nil.
Print d2.
Print d2.
Print existT.
Print list.
Print d2.
Print list.
Fail Program Definition d3 : D := existT _ D nil.

Print Universes.
Print sigT.
Print existT.
Print nat.
Print sigT.
Print d2.
Print Universes.
Print sigT.
Program Definition d3 : D := existT _ (list nat) _.

Print list.
Print sig.
Print sigT.
Definition a : Type := {y : (list ({ x : nat & nat})) & nat}.
Print a.
Definition b : Type := {y : a & a}.
Definition c : Type := list {y : b & b}.
Print a.
Print b.
Print c.

Definition A : Type -> Type := fun X => (list ({ x : X & nat})).
Print A.
Definition B := { x : A nat & A nat }.
Definition d0 := sigT (fun d : D => Type).
Print d.
Print sigT.
Print B.
Print A.
Definition
Print Universes.
