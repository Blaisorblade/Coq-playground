Definition p := true.
Obligation Tactic := idtac.
Require Import Program.
Unset Program Cases.
Time Program Fixpoint f (n : nat) {struct n} : nat :=
  match p with false => n | _ =>
    match p with false => n | _ =>
      match p with false => n | _ =>
        match p with false => n | _ =>
          match p with false => n | _ =>
            match p with false => n | _ =>
              match p with false => n | _ =>
                match p with false => n | _ =>
                  match p with false => n | _ =>
                    match n with
                    | 0 => 0
                    | S n => S (f n)
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  end.

Require Import Lia.
Require Import Omega.
Require Import ssreflect.
Inductive limitedNat {n} : Type :=
| lim i : i < n -> limitedNat.
Definition test i j (H: (i < j) /\ True) : @limitedNat (S j).
Proof.
  refine (lim (S i) _). omega.
Defined.

    ltac:(lazymatch goal with H : ?i < ?j |- _ => idtac H end)
    end)).
  refine (lim (S i) (match H with conj IJ _ =>
    ltac:(lazymatch goal with H : ?i < ?j |- _ => idtac H end)
    end)).
  lia.
  (match H with conj IJ _ => ltac:(lia) end).
 :=
  lim (S i) _.
  (match H with conj IJ _ => ltac:(lia) end).
  Lemma test (n: nat) : nat. Proof.
  Fail idtac n.
  destruct n eqn:B.
  Fail idtac B.
  Fail idtac n.
match goal with
| H : _ = _ |- _ => idtac H
end.
destruct n eqn:B. idtac B. exact 0. Defined.
exact 0. Defined.
From Coq Require Import String.
From Coq Require Import List.

Import ListNotations.
Inductive Expression : Type :=
| EEmptyList
| EVar (s : string)
| EMap (l : list (Expression * Expression)).

Fixpoint variables (e : Expression) : list string :=
  match e with
  | EEmptyList => []
  | EVar x => [x]
  | EMap l => fold_right (fun '(a, b) r => app (app (variables a) (variables b)) r) [] l
  end.
Lemma equiv l :
  fold_right (fun '(a, b) r => app (app (variables a) (variables b)) r) [] l =
  (fix fp l :=
    match l with
    | [] => []
    | (a,b)::xs => app (app (variables a) (variables b)) (fp xs)
    end) l.
Proof. now induction l; [|destruct a; rewrite <-IHl]. Qed.

Require Import iris.algebra.base.
Lemma foo : ∀ {A : Set} {P : A → Prop} (a : A), (∀ x, ¬ (P x)) → ¬ (∀ x, P x).
intros * a H Hn.
eapply (H a), Hn.
intros.
firstorder.
intuition.
tauto.



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
