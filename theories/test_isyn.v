(**
* gDOT syntax and operational semantics.
Follows Sec. 2; implemented using de Bruijn indexes and the Autosubst 1
infrastructure.
The operational semantics implements the Iris infrastructure for languages,
using contextual small-step operational semantics.
*)
Require Import Program.
From Equations Require Import Equations.
From Autosubst Require Export Autosubst.
(* Require Import ssreflect. *)
From stdpp Require Export strings.
From iris.algebra Require Import base.

Ltac eqn_simpl := program_simplify; Equations.CoreTactics.equations_simpl;
                              try program_solve_wf.

(** * ssreflect postfix notation for the successor and predecessor functions.
SSreflect uses "pred" for the generic predicate type, and S as a local bound
variable.*)
Notation succn := Datatypes.S.
Notation predn := Peano.pred.


Definition S := S.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

(** Type of labels; we use a single type for both term labels [a] and type
labels [A]. *)
Definition label := string.
Definition stamp := positive.


(* Inductive base_lit : Set := lint (n : Z) | lbool (b : bool).
Inductive un_op : Set := unot.
Inductive bin_op : Set := bplus | bminus | btimes | bdiv | blt | ble | beq.
Inductive base_ty : Set := tint | tbool. *)
(* (B : base_ty)  *)
Implicit Types (l : label) (n : nat).

Module V0.
Inductive kty : nat → Type :=
  | TTop : kty 0
  | TBot : kty 0

  (* | TAnd (T1 T2 : kty 0) : kty 0
  | TOr (T1 T2 : kty 0): kty 0 *)
  | kTLater {n} (T : kty n) : kty n

  (* | TAll (S T : kty 0) : kty 0 *)
  (* | TMu (T : kty 0) : kty 0
  | TVMem l (T : kty 0) : kty 0 *)
  | kTTMem {n} l (K : kind n) : kty n
  (* | kTSel n (v : vl_) l : kty n *)
  (* | TPrim B : kty 0 *)
  (* | TSing (p : path) : kty 0 *)
  | kTLam {n} (T : kty n) : kty n.+1
  (* | kTApp {n} (T : kty n.+1) (v : vl_) : kty n *)

with kind : nat → Type :=
  | kintv (L U : kty 0) : kind 0
  | kpi {n} (S : kty 0) (K : kind n) : kind n.+1.

Set Transparent Obligations.



(* Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true. *)
Derive Signature for kty kind.
Derive NoConfusion NoConfusionHom for kty.
Show Obligation Tactic.
(* Obligation Tactic := idtac. *)

(* Print dec_eq.
About dec_eq.
Print EqDec.
About EqDec. *)
(* Derive EqDec for kty kind.
Derive EqDec for kty.

Next Obligation.
have : ∀ n, EqDec (kty n). intros. apply _.
:= !!(_).
hnf.
Derive EqDec for kty.
Instance foo n: EqDec (kty n) := _. *)

(* Solve All Obligations with eqn_simpl. *)
(* Derive NoConfusion NoConfusionHom for kty.
Next Obligation. eqn_simpl. simplify_eq. vm_compute. Qed.
Derive NoConfusion NoConfusionHom for kty kind. *)

Unset Transparent Obligations.

Equations kty_eq_dec n (T1 T2 : kty n) : Decision (T1 = T2) by struct T1 := {
  kty_eq_dec n TTop TTop := left _;
  kty_eq_dec n TBot TBot := left _;
  kty_eq_dec _ (kTLater T1) (kTLater T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if (decide (T1 = T2)) ;
  kty_eq_dec _ (kTLam T1) (kTLam T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if (decide (T1 = T2)) ;
  kty_eq_dec _ (kTTMem l1 K1) (kTTMem l2 K2) :=
    let _ : ∀ n, EqDecision (kind n) := kind_eq_dec in
    cast_if_and (decide (l1 = l2)) (decide (K1 = K2));
  kty_eq_dec _ _ _ := right _
} with kind_eq_dec n (K1 K2 : kind n): Decision (K1 = K2) by struct K1 := {
  kind_eq_dec 0 (kintv L1 U1) (kintv L2 U2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (L1 = L2)) (decide (U1 = U2));
  kind_eq_dec n (kpi S1 K1) (kpi S2 K2) :=
    let _ : ∀ n, EqDecision (kind n) := kind_eq_dec in
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (S1 = S2)) (decide (K1 = K2))
}.

Solve All Obligations with eqn_simpl; simplify_eq.

Existing Instances kty_eq_dec kind_eq_dec.

Solve All Obligations with eqn_simpl; simplify_eq.
Next Obligation. eqn_simpl; simplify_eq. Defined.
Next Obligation. eqn_simpl; simplify_eq. Defined.
Next Obligation. eqn_simpl; simplify_eq. Defined.
Next Obligation. eqn_simpl. Defined.
Next Obligation. eqn_simpl. Qed.
Next Obligation. eqn_simpl. Qed.
Next Obligation. eqn_simpl. Qed.
Next Obligation. eqn_simpl. Qed.
  (* Next Obligation. right; congruence. Qed.
  Next Obligation. right; congruence. Qed. *)
Solve All Obligations with try eqn_simpl; simplify_eq.
Existing Instance kty_eq_dec.

Solve All Obligations with eqn_simpl; simplify_eq.
Eval cbv in kty_eq_dec _ TTop TTop.
Eval vm_compute in kty_eq_dec _ TTop TTop.
(* Eval in kty_eq_dec. *)

Fail Next Obligation.
  (* Next Obligation. right. inversion T1. Qed. *)


match T1 as T3 return T1 = T3 -> Decision (T1 = T2) with
| TTop => _
| _ => _
end eq_refl.


Definition disable_tc_search {T : Type} (x : id T) : T := x.
Notation notc_hole := (disable_tc_search _).
Unset Program Cases.
Program Definition kty_eq_dec n (T1 T2 : kty n): Decision (T1 = T2) :=
match T1 as T3 return T1 = T3 -> Decision (T1 = T2) with
| TTop => _
| _ => _
end eq_refl.
Next Obligation.
Admitted.
Next Obligation.
Next Obligation.
Admitted.


Instance kty_eq_dec n : EqDecision (kty n).
revert n.
refine
(fix go {n} (T1 T2 : kty n) {struct T1} : Decision (T1 = T2) :=
match T1 as T3 in kty n0 return Decision (T1 = T2) with
(* match T1 in kty n0, T2 in kty n0 return Decision (T1 = T2) with *)
| TTop => notc_hole
| _ => notc_hole
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end); rewrite /id.

refine
(fix go {n} (T1 T2 : kty n) {struct T1} : Decision (T1 = T2) :=
match T1 as T3 in kty n0, T2 as T4 in kty n0 return Decision (T3 = T4) with
(* match T1 in kty n0, T2 in kty n0 return Decision (T1 = T2) with *)
| TTop, TTop => left _
(* | TBot, TBot => left _ *)
| _, _ => right _
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end).

refine
(fix go {n} (T1 T2 : kty n) {struct T1} : Decision (T1 = T2) :=
match T1 as T3 in kty n0, T2 as T4 in kty n0 return Decision (T3 = T4) with
(* match T1 in kty n0, T2 in kty n0 return Decision (T1 = T2) with *)
| TTop, TTop => left _
(* | TBot, TBot => left _ *)
| _, _ => right _
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end).

as T1o, T2o

clear go; try abstract intuition congruence.
simplify_eq.


Program Fixpoint kty_eq_dec n (T1 T2 : kty n): Decision (T1 = T2) := _.

Next Obligation.
move: n T1 T2; fix f 2 => n T1 T2.
destruct T1.
admit.
admit.
admit.
case: n T1 T2 => [|n] [] []; intros.
clear f.

match T1 with
| TTop => left _
| _ => right _
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end.

match T1, T2 with
| TTop, TTop => left _
| _, _ => right _
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end.

Program Fixpoint kty_eq_dec n : EqDecision (kty n) :=
fix go n (T1 T2 : kty n) {struct T1} : Decision (T1 = T2) :=
match T1, T2 with
| TTop, TTop => left _
| TBot, TBot => left _
| _, _ => right _
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end.


Program Instance kty_eq_dec n : EqDecision (kty n) :=
fix go {n} (T1 T2 : kty n) {struct T1} : Decision (T1 = T2) :=
match T1, T2 with
| TTop, TTop => left _
| _, _ => right _
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end.

revert n.
refine
(fix go {n} (T1 T2 : kty n) {struct T1} : Decision (T1 = T2) :=
match T1, T2 with
| TTop, TTop => left _
| _, _ => right _
(* | TAll S1 T1, TAll S2 T2 => cast_if_and (decide (S1 = S2)) (decide (T1 = T2)) *)
(* | _, _ => _ *)
end).





Inductive tm : Type :=
  | tv : vl_ → tm
  | tapp : tm → tm → tm
(*
  | tproj : tm → label → tm
  | tskip : tm → tm

  | tun : un_op → tm → tm
  | tbin : bin_op → tm → tm → tm
  | tif : tm → tm → tm → tm

  a *)


 with vl_ : Type :=
  | vvar : var → vl_
  (* | vlit : base_lit → vl_ *)
  | vabs : tm → vl_
  (* | vobj : list (label * dm) → vl_

 with dm : Type :=
  | kdtysyn {n} : kty n → dm
  | dtysem : list vl_ → stamp → dm *)
  (* | dvl : vl_ → dm *).



 (* with path : Type :=
  | pv : vl_ → path
  | pself : path → label → path *)

 with kty : nat → Type :=
  (* | TTop : kty 0
  | TBot : kty 0 *)
  (* | TAnd (T1 T2 : kty 0) : kty 0
  | TOr (T1 T2 : kty 0): kty 0
  | kTLater {n} (T : kty n) : kty n *)
  | TAll (S T : kty 0) : kty 0
  (* | TMu (T : kty 0) : kty 0
  | TVMem l (T : kty 0) : kty 0 *)
  | kTTMem {n} l (K : kind n) : kty n
  | kTSel n (v : vl_) l : kty n
  (* | TPrim B : kty 0 *)
  (* | TSing (p : path) : kty 0 *)
  | kTLam {n} (T : kty n) : kty n.+1
  | kTApp {n} (T : kty n.+1) (v : vl_) : kty n
with kind : nat → Type :=
  | kintv (L U : kty 0) : kind 0
  | kpi {n} (S : kty 0) (K : kind n) : kind n.+1.

Instance expr_eq_dec n : EqDecision (kty n).


