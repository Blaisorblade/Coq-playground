Require Import ssreflect.
(* Require Import Utf8. *)
From stdpp Require Import decidable tactics.

(* Provides stdpp decidable equality for naturals. *)
From stdpp Require Import numbers.
Require Import Program.
From Equations Require Import Equations.

(* Undo effects of loading stdpp. *)
Set Transparent Obligations.
Ltac eqn_simpl := program_simplify; Equations.CoreTactics.equations_simpl;
                              try program_solve_wf.
Obligation Tactic := eqn_simpl.

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Implicit Types (n : nat).

Inductive kty : nat → Type :=
  | TTop : kty 0
  | TBot : kty 0
  | kTLam {n} (T : kty n) : kty (S n)

with kind : nat → Type :=
  | kintv (L U : kty 0) : kind 0
  | kpi {n} (T : kty 0) (K : kind n) : kind (S n).
Derive Signature for kty kind.

Derive NoConfusion NoConfusionHom for kty.
Show Obligation Tactic.

Fail Derive EqDec for kty kind.
Fail Derive EqDec for kty.
Obligation Tactic := idtac.
Fail Derive EqDec for kty.
Obligation Tactic := eqn_simpl.

(* Solve All Obligations with eqn_simpl. *)
(* Derive NoConfusion NoConfusionHom for kty.
Next Obligation. eqn_simpl. simplify_eq. vm_compute. Qed.
Derive NoConfusion NoConfusionHom for kty kind. *)

(* Comment in the { and } to fix the ? *)
Equations kty_eq_dec n (T1 T2 : kty n) : Decision (T1 = T2) by struct T1 :=
(* { *)
  kty_eq_dec n TTop TTop := left _;
  kty_eq_dec n TBot TBot := left _;
  kty_eq_dec _ (kTLam T1) (kTLam T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if (decide (T1 = T2)) ;
  kty_eq_dec _ _ _ := right _
(* } *)
with
kind_eq_dec n (K1 K2 : kind n): Decision (K1 = K2) by struct K1 :=
  kind_eq_dec 0 (kintv L1 U1) (kintv L2 U2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (L1 = L2)) (decide (U1 = U2));
  kind_eq_dec n (kpi S1 K1) (kpi S2 K2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    let _ : ∀ n, EqDecision (kind n) := kind_eq_dec in
    cast_if_and (decide (S1 = S2)) (decide (K1 = K2)).
Next Obligation. eqn_simpl; simplify_eq/=. Defined.

Next Obligation. eqn_simpl. simplify_eq. Defined.

About kind_eq_dec.
