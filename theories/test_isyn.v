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


Inductive base_lit : Set := lint (n : Z) | lbool (b : bool).
Inductive un_op : Set := unot.
Inductive bin_op : Set := bplus | bminus | btimes | bdiv | blt | ble | beq.
Inductive base_ty : Set := tint | tbool.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.

Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.

Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.

Instance base_ty_eq_dec : EqDecision base_ty.
Proof. solve_decision. Defined.

Implicit Types (l : label) (B : base_ty) (n : nat).

Inductive tm : Type :=
  | tv : vl_ → tm
  | tapp : tm → tm → tm

  | tproj : tm → label → tm
  | tskip : tm → tm

  | tun : un_op → tm → tm
  | tbin : bin_op → tm → tm → tm
  | tif : tm → tm → tm → tm
 with vl_ : Type :=
  | vvar : var → vl_
  | vlit : base_lit → vl_
  | vabs : tm → vl_
  | vobj : list (label * dm) → vl_

 with dm : Type :=
  | kdtysyn {n} : kty n → dm
  | dtysem : list vl_ → stamp → dm
  | dvl : vl_ → dm



 with path : Type :=
  | pv : vl_ → path
  | pself : path → label → path

 with kty : nat → Type :=
  | TTop : kty 0
  | TBot : kty 0

  | TAnd (T1 T2 : kty 0) : kty 0
  | TOr (T1 T2 : kty 0): kty 0
  | kTLater {n} (T : kty n) : kty n

  | TAll (S T : kty 0) : kty 0
  | TMu (T : kty 0) : kty 0
  | TVMem l (T : kty 0) : kty 0
  | kTTMem {n} l (K : kind n) : kty n
  | kTSel n (v : vl_) l : kty n
  | TPrim B : kty 0
  | TSing (p : path) : kty 0
  | kTLam {n} (T : kty n) : kty n.+1
  | kTApp {n} (T : kty n.+1) (v : vl_) : kty n
with kind : nat → Type :=
  | kintv (L U : kty 0) : kind 0
  | kpi {n} (S : kty 0) (K : kind n) : kind n.+1.

Definition vl := vl_.
Implicit Types
         (v : vl) (t : tm) (d : dm) (p : path).
         (*  (ds : dms) .
         (Γ : ctx). *)

Derive Signature for kty kind.
Set Transparent Obligations.
(* Both commands rely on transparent obligations. *)
Derive NoConfusion for kty kind.
Derive NoConfusionHom for kty kind.
Unset Transparent Obligations.

Equations(noeqns noind) vl_eq_dec v1 v2   : Decision (v1 = v2) by struct v1 := {
  vl_eq_dec v1 v2 :=
    let _ : EqDecision dm := dm_eq_dec in (* Objects *)
    let _ : EqDecision tm := tm_eq_dec in (* Lambdas *)
    ltac:(rewrite /Decision; decide equality; solve_decision)
}
with  tm_eq_dec t1 t2   : Decision (t1 = t2) by struct t1 := {
  tm_eq_dec t1 t2 :=
    let _ : EqDecision vl := vl_eq_dec in
    ltac:(rewrite /Decision; decide equality; solve_decision)
}
with  path_eq_dec p1 p2   : Decision (p1 = p2) by struct p1 := {
  path_eq_dec p1 p2 :=
    let _ : EqDecision vl := vl_eq_dec in
    ltac:(rewrite /Decision; decide equality; solve_decision)
}
with
kty_eq_dec n (T1 T2 : kty n) : Decision (T1 = T2) by struct T1 := {
  kty_eq_dec n TTop TTop := left _;
  kty_eq_dec n TBot TBot := left _;
  kty_eq_dec _ (TAnd T11 T12) (TAnd T21 T22) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (T11 = T21)) (decide (T12 = T22));
  kty_eq_dec _ (TOr T11 T12) (TOr T21 T22) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (T11 = T21)) (decide (T12 = T22));
  kty_eq_dec _ (kTLater T1) (kTLater T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if (decide (T1 = T2));
  kty_eq_dec _ (TAll S1 T1) (TAll S2 T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (S1 = S2)) (decide (T1 = T2));
  kty_eq_dec _ (TMu T1) (TMu T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if (decide (T1 = T2));
  kty_eq_dec _ (TVMem l1 T1) (TVMem l2 T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (l1 = l2)) (decide (T1 = T2));
  kty_eq_dec _ (kTTMem l1 K1) (kTTMem l2 K2) :=
    let _ : ∀ n, EqDecision (kind n) := kind_eq_dec in
    cast_if_and (decide (l1 = l2)) (decide (K1 = K2));
  kty_eq_dec _ (kTSel _ v1 l1) (kTSel _ v2 l2) :=
    let _ : EqDecision vl := vl_eq_dec in
    cast_if_and (decide (v1 = v2)) (decide (l1 = l2)) ;
  kty_eq_dec _ (TPrim B1) (TPrim B2) :=
    cast_if (decide (B1 = B2));
  kty_eq_dec _ (TSing p1) (TSing p2) :=
    let _ : EqDecision path := path_eq_dec in
    cast_if (decide (p1 = p2));
  kty_eq_dec _ (kTLam T1) (kTLam T2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if (decide (T1 = T2)) ;
  kty_eq_dec _ (kTApp T1 v1) (kTApp T2 v2) :=
    let _ : EqDecision vl := vl_eq_dec in
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (T1 = T2)) (decide (v1 = v2));
  kty_eq_dec _ _ _ := right _
} with kind_eq_dec n (K1 K2 : kind n): Decision (K1 = K2) by struct K1 := {
  kind_eq_dec 0 (kintv L1 U1) (kintv L2 U2) :=
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (L1 = L2)) (decide (U1 = U2));
  kind_eq_dec n (kpi S1 K1) (kpi S2 K2) :=
    let _ : ∀ n, EqDecision (kind n) := kind_eq_dec in
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if_and (decide (S1 = S2)) (decide (K1 = K2))
}
with dm_eq_dec (d1 d2 : dm) : Decision (d1 = d2) by struct d1 := {
  dm_eq_dec (dtysem σ1 s1) (dtysem σ2 s2) :=
    let _ : EqDecision vl := vl_eq_dec in
    cast_if_and (decide (σ1 = σ2)) (decide (s1 = s2));
  dm_eq_dec (dvl v1) (dvl v2) :=
    let _ : EqDecision vl := vl_eq_dec in
    cast_if (decide (v1 = v2));
  dm_eq_dec (kdtysyn (n := n1) T1) (kdtysyn (n := n2) T2) with decide (n1 = n2) => {
    | left eq_refl =>
    let _ : ∀ n, EqDecision (kty n) := kty_eq_dec in
    cast_if (decide (T1 = T2));
    | in_right => right _
  };
  dm_eq_dec _ _ := right _
}.

Solve All Obligations with program_simplify; try reflexivity.
Solve All Obligations with program_simplify; try (intro; simplify_eq).
(* These obligations are for equations! *)
(* Next Obligation. by elim. Defined.
Next Obligation. by elim. Defined. *)

Existing Instances kty_eq_dec kind_eq_dec dm_eq_dec vl_eq_dec tm_eq_dec path_eq_dec.



Goal ∃ x, kty_eq_dec _ TTop TTop = left x.
Proof. by eexists. Qed.
Goal ∃ x, kty_eq_dec _ (kTLam TTop) (kTLam TTop) = left x.
Proof. by eexists. Qed.
