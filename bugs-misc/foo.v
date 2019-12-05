Goal let f := plus in f (0 + 0) 0 = 0.
  cbv beta delta. cbv iota beta.
  intro f.
  cbv delta. (* let f := (fix add ...) in f ((fix add ...) 0 0) 0 = 0 *)
  intro f.
  cbv delta;clear f.

Require Import Lia.
From Coq Require Export ZArith NPeano.
Lemma foo2 : forall (z:Z), (z >=0)%Z -> { n : nat | Z.of_nat n = z }.
Proof. intros z. exists (Z.to_nat z). apply Z2Nat.id. lia. Qed.

From Coq.ssr Require Import ssreflect.
From Coq Require Export EqdepFacts PArith NArith ZArith NPeano.

Lemma foo : forall (z:Z), (z >=0)%Z -> exists n : nat , Z.of_nat n = z.
Proof. intros z. exists (Z.to_nat z). apply Z2Nat.id. lia. Qed.
Lemma to_nat2 : Z -> nat. intros z. Fail destruct (foo z). Abort.

Lemma to_nat2 (z : Z) (H : (z >= 0)%Z): nat. destruct (foo2 z H) as [n _]. exact n. Defined.

About Z.
From mathcomp.ssreflect Require Import ssrnat.
Search _ (forall (z:Z), (z >=0)%Z -> { n : nat | Z.to_nat z = n }).
Search _ (forall (z:Z), (z >=0)%Z -> exists n : nat , Z.to_nat z = n).
Search _ (_ >= 0 -> Z.abs _ = _).
Require Import Lia.

Inductive foo := .

Inductive bar := .

Require Import Lia.
From Coq.ssr Require Import ssreflect.
Lemma baz : 1 = 2 -> 3 = 4.
move => Hi. have {Hi} -Hi: 2 = 3 by lia. lia.
Qed.

Lemma foo (H:True) : True -> True.
Proof.
  move => {H} -H.
  exact I.
Qed.
