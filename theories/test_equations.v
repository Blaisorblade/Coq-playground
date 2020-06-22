Require Import Coq.Numbers.BinNums.

(* From stdpp Require Export base. *)
From Equations Require Import Equations.

Derive EqDec for positive.

Instance positive_eqdec : EqDec positive.
Proof.
Fail apply _.
Abort.

Module Type FooType.
End FooType.
Module Foo <: FooType.
(* From iris.algebra Require Export base. *)
From Coq.ssr Require Export ssreflect.
(* Global Unset Transparent Obligations. *)
(* From stdpp Require Export base. *)
(* Set Default Proof Using "Type". *)
(* Global Open Scope general_if_scope. *)
(* Global Set SsrOldRewriteGoalsOrder. (* See Coq issue #5706 *) *)
(* Ltac done := stdpp.tactics.done. *)

From Coq Require Export Morphisms RelationClasses List Bool Utf8 Setoid Peano.
From Coq Require Import Permutation.
Set Default Proof Using "Type".
Export ListNotations.
From Coq.Program Require Export Basics Syntax.
(* Obligation Tactic := idtac. *)
(* From stdpp Require Export base. *)
Set Transparent Obligations.
(* Global Generalizable All Variables. *)
Derive NoConfusion EqDec for positive.
Fail Instance : EqDec positive := _.

(* Derive EqDec for positive. *)

Instance positive_eqdec' : EqDec positive := _.

Instance my_nat_eqdec : EqDec nat.
Proof. apply _. Qed.
Print my_nat_eqdec.
Import EqDecInstances.
About EqDecInstances.
Print nat_EqDec.
Print nat_eqdec.
About positive_EqDec.
