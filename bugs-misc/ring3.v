From mathcomp Require Import ssreflect ssrnat eqtype ssrbool ssrnum ssralg.
Require Import Ring.

Import GRing.Theory.
Open Scope ring_scope.

Section foo.
(* Variant of the same problem. *)
(* Variable R: numFieldType. *)

Variable R: comRingType.
Locate "+".

Lemma check_defeq: GRing.Zmodule.sort R = GRing.ComRing.sort R. done. Qed.

Locate "+%R".
Check +%R.

(* Definition addT : R -> R -> R := +%R.
Local Infix "+" := addT. *)

Definition rt :
  (* @ring_theory (GRing.ComRing.sort R) 0%:R 1%:R addT *%R (fun a b => a - b) -%R eq. *)
  @ring_theory (GRing.Zmodule.sort R) 0%:R 1%:R +%R *%R (fun a b => a - b) -%R eq.
  (* Doesn't work.*)
  (* @ring_theory R 0%:R 1%:R +%R *%R (fun a b => a - b) -%R eq. *)
  (* Works. *)
  (* @ring_theory R 0%:R 1%:R addT *%R (fun a b => a - b) -%R eq. *)
Proof.
  apply mk_rt.
  - apply add0r.
  - apply addrC.
  - apply addrA.
  - apply mul1r.
  - apply mulrC.
  - apply mulrA.
  - apply mulrDl.
  - by [].
  - apply subrr.
Qed.
Add Ring Ringgg : rt.

Lemma tmp2:
    forall x y: R, x + y = y + x * 1.
Proof. move => x y. ring. Qed.
End foo.


(* About rt. *)


(*
Goal T = (GRing.Zmodule.sort  R).
done.
Qed.
Goal T = GRing.Ring.sort R.
done.
Qed. *)

Definition rt :
    @ring_theory T 0%:R 1%:R +%R *%R (fun a b => a - b) -%R eq.
Proof.
  apply mk_rt.
  - apply add0r.
  - apply addrC.
  - apply addrA.
  - apply mul1r.
  - apply mulrC.
  - apply mulrA.
  - apply mulrDl.
  - by [].
  - apply subrr.
Qed.
About rt.

Add Ring Ringgg : rt.

Lemma tmp2:
    forall x y:T, @eq T (x + y) (y + x).
Proof. move => x y. ring. Qed.



(* Require Import ZArith.
About Zth.
Lemma tmp2:
    forall x y:BinNums.Z, eq (x + y)%Z (y + x)%Z.
Proof. move => x y. ring. Qed. *)

Section foo.
Variable R: numFieldType.
Open Scope ring_scope.
(*
Definition addT : T -> T -> T :=
    fun x y => (x + y)%R.
Notation "x ++ y":= (addT x y).
Definition mulT : T -> T -> T :=
    fun x y => (x * y)%R.
Local Notation "x * y":= (mulT x y). *)

Definition T:=
  R.
  (* GRing.Ring.sort R. *)
  (* (GRing.Zmodule.sort (GRing.Ring.zmodType R)). *)
  (* (GRing.Zmodule.sort (GRing.Ring.zmodType (Num.NumField.ringType R))). *)
Definition subT : T -> T -> T :=
    fun x y => (x - y)%R.
Local Notation "x - y":= (subT x y).


Definition oppT : T -> T :=
    fun x => (-x)%R.
Local Notation "- x":= (oppT x).

Definition addT : T -> T -> T := +%R.
Local Infix "+" := addT.

Definition rt :
    @ring_theory T 0%R 1%R addT *%R subT oppT eq.
Proof.
  apply mk_rt.
  - apply add0r.
  - apply addrC.
  - apply addrA.
  - apply mul1r.
  - apply mulrC.
  - apply mulrA.
  - apply mulrDl.
  - by [].
  - apply subrr.
Qed.
(* About rt. *)

Locate "-".


(*
Goal T = (GRing.Zmodule.sort  R).
done.
Qed.
Goal T = GRing.Ring.sort R.
done.
Qed. *)
(*
Definition rt :
    @ring_theory T 0%:R 1%:R +%R *%R (fun a b => a - b) -%R eq.
Proof.
  apply mk_rt.
  - apply add0r.
  - apply addrC.
  - apply addrA.
  - apply mul1r.
  - apply mulrC.
  - apply mulrA.
  - apply mulrDl.
  - by [].
  - apply subrr.
Qed.
About rt. *)

Add Ring Ringgg : rt.

Lemma tmp2:
    forall x y:T, @eq T (x + y) (y + x).
Proof. move => x y. ring. Qed.
