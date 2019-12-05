(* Require Import Reals. *)
(* Lemma tmp2: forall x, (Int_part x >= 0)%Z. *)

(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype path bigop finset.
From mathcomp Require Import fingroup. *)

(* Require Import Reals.
Print Scope Z_scope.
Lemma tmp2: forall x, (Int_part x >= 0)%Z.
Abort. *)
(* Fail Print Scope int_scope. *)

From mathcomp Require Import ssralg ssrnum ssreflect reals ssrbool ssrint Rstruct.
Lemma tmp2: forall (R : realType) (x : R), (floor x >= 0)%R.
Lemma tmp3: forall (x : Rdefinitions.R), (floor x >= 0)%R.
About floor.
From mathcomp Require Import all_algebra.
Print Scope int_scope.
Fail Lemma tmp2: forall x, (Int_part x >= 0)%Z.
Require Import Reals.
About Reals.
Lemma tmp2: forall x, (Int_part x >= 0)%Z.

From mathcomp Require Import ssreflect ssrnat.
From mathcomp Require Import fingroup.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
Lemma tmp2: forall x, (Int_part x >= 0)%Z.
From mathcomp Require Import all_algebra.
Lemma tmp2: forall x, (Int_part x >= 0)%Z.
Print Scope int_scope.
Print Scope Z_scope.
Open Scope int_scope.
Lemma tmp2: forall x, (Int_part x >= 0).
Lemma tmp2: forall x, (Int_part x >= 0)%Z.
(* Open Scope Z_scope. *)
Print Scopes.
About Int_part.
(* Print Scope Z_scope. *)
(* From mathcomp Require Import Rstruct all_algebra. *)
(* From mathcomp Require Import Rstruct all_algebra.
From mathcomp Require Import fingroup.
Local Open Scope ring_scope. *)


(* Open Scope Z_scope. *)
