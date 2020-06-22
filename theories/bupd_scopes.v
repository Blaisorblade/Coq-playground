(* Many variants of the imports below give the same results *)
(* From iris.proofmode Require Import tactics. *)
From iris.base_logic Require Import iprop.

Fail Definition usetp (n : nat) {Σ} : iProp Σ :=
  □ |==> ∃ m : nat , ⌜ n = 2 ⌝.

Definition usetp1 {Σ} (n : nat) : iProp Σ :=
  (□ |==> ∃ m : nat , ⌜ n = 2 ⌝)%I.
Definition usetp2 {Σ} (n : nat) : iProp Σ :=
  □ (|==> ∃ m : nat , ⌜ n = 2 ⌝)%I.
Definition usetp3 {Σ} (n : nat) : iProp Σ :=
  □ |==> (∃ m : nat , ⌜ n = 2 ⌝)%I.
Fail Definition usetp4 (n : nat) {Σ} : iProp Σ :=
  □ |==> ∃ m : nat , (⌜ n = 2 ⌝)%I.
Definition usetp' {Σ} (n : nat) :=
  ⊢@{iPropI Σ} □ |==> ∃ m : nat , ⌜ n = 2 ⌝.

(* From iris.base_logic Require Import base_logic. *)
(* From iris.base_logic Require Import invariants. *)
(* From iris.program_logic Require Export weakestpre. *)
(* Import uPred. *)

  (* Import updates. *)


  (* Fail Definition usetp (n : nat) {Σ} : iProp Σ :=
    (□ |==> ∃ m : nat , ⌜ n = m + 2 ⌝)%I.
  Definition usetp (n : nat) {Σ} : iProp Σ :=
    (□ |==> ∃ m : nat , ⌜ 2 + m = n ⌝)%I. *)
  (* Definition usetp (n : nat) {Σ} : iProp Σ :=
    (□ |==> ∃ m : nat , ⌜ n =@{nat} (Init.Nat.add m 2) ⌝)%I. *)
