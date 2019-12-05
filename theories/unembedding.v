(*
  Translating https://bentnib.org/unembedding.html in Coq. With some care for the partial bits.
*)
(* Required opam packages: coq-stdpp and coq-autosubst. *)
From Coq.Program Require Import Program.
From Coq Require Import ssr.ssreflect Lia.
From stdpp Require Import base tactics.
From Autosubst Require Import Autosubst.

Set Primitive Projections.
Unset Program Cases.

Inductive DBTerm :=
| Var (n : nat)
| Lam (b : DBTerm)
| App (f : DBTerm) (a : DBTerm).

Definition Env t := var → t.
(* Equals Env DBTerm, but that's accidental. *)
Definition DB := var → DBTerm.

(* We reuse a tiny bit of Autosubst here. *)
Instance idsDBT: Ids DBTerm := Var.

Instance idsDB: Ids DB := λ x, (* [x]: input to the substitution. *)
  (* Resulting [DB] term. *)
  λ i, Var (x + i).

Definition hLam (f : DB → DB) : DB := λ i,
  let i' := S i in
  let v := λ j, Var (j - i') in
  Lam (f v i').

Definition lift2 (con : DBTerm → DBTerm → DBTerm) : DB → DB → DB := λ a1 a2 i,
  con (a1 i) (a2 i).

(* Inline [lift2] to avoid complicating proofs. *)
Definition hApp := Eval cbv in lift2 App.
Definition hApp' (f a : DB) : DB := λ i, App (f i) (a i).
Goal hApp = hApp'. done. Qed.

Module UnembeddingGeneral.

Class UntypedLambda (exp : Type) := {
  lam : (exp → exp) → exp;
  app : exp → exp → exp;
}.
Definition Hoas := ∀ exp, UntypedLambda exp → exp.
Example ex1 : Hoas := λ exp hU,
  lam (λ x, lam (λ y, app x y)).
Example ex1DB : DBTerm := Lam (Lam (App (Var 1) (Var 0))).

Definition numeral (n : nat): Hoas := λ exp hU,
  let body := fix body s z n :=
    match n with
    | 0 => z
    | S n => app s (body s z n)
    end
  in lam (λ s, lam (λ z, body s z n)).

Instance untypedSize : UntypedLambda nat := {
  lam f := S (f 1);
  app x y := S (x + y);
}.
Definition size (t : Hoas) : nat := t nat untypedSize.

(* i and j are de Bruijn levels! *)
Instance untypedDB : UntypedLambda DB := {
  lam := hLam;
  app := hApp;
}.

Definition toTerm (t : Hoas) : DBTerm :=
  t _ untypedDB 0.
Goal toTerm ex1 = ex1DB. done. Qed.

(* Now we're getting to the real deal. *)
(* Type of open Hoas terms.
The paper uses finite environments ([list exp]), but the resulting code is potentially partial *and* uses infinite lists.
Since we can't tolerate partiality, we follow the alternative design the authors suggest, and use infinite substitutions. *)
Definition Hoas' :=
  ∀ exp, UntypedLambda exp → (var → exp) → exp.
Definition ex1' : Hoas' := λ exp hU s, ex1 exp hU.

Definition toTerm' (t : Hoas') : DBTerm :=
  t _ untypedDB ids 0.

Definition testToTerm'Ex1' := toTerm' ex1'.
Goal testToTerm'Ex1' = ex1DB. done. Qed.

Program Definition fromTermGo `{UntypedLambda exp} : DBTerm → (var → exp) → exp := fix F t env :=
  match t with
  | Var i => env i
  | App f a => app (F f env) (F a env)
  | Lam t => lam (λ x, F t (x .: env))
  end.

(* Simply rearrange parameters of [fromTermGo]. *)
Definition fromTerm' (t : DBTerm) : Hoas' :=
  λ exp hU, fromTermGo t.

Eval cbv in fromTerm' testToTerm'Ex1'.
Example roundTripEx1 : ex1' = fromTerm' testToTerm'Ex1'. done. Qed.

Definition isUnshiftP i s := ∀ m n, s m n = Var (m + n - i).
Lemma matching s1 s2 i1 i2
  (Hu1: isUnshiftP i1 s1) (Hu2 : isUnshiftP i2 s2) n:
  s1 n i1 = s2 n i2.
Proof. by rewrite Hu1 Hu2 !PeanoNat.Nat.add_sub. Qed.

Lemma fromTermGo_respects_unshifts t s1 s2 i1 i2
  (Hu1: isUnshiftP i1 s1) (Hu2 : isUnshiftP i2 s2):
  fromTermGo t s1 i1 = fromTermGo t s2 i2.
Proof.
  elim: t s1 s2 i1 i2 Hu1 Hu2 => /= [n | b IHb |f ? a ?] s1 s2 i1 i2 Hu1 Hu2;
    first exact: matching; lazy [hLam hApp]; f_equal; [| by eauto 2 ..].
  apply IHb => ??; rewrite /scons; case_match; subst => //=.
Qed.

Lemma fromTermGo_respects_unshift1 t :
  fromTermGo t ((λ j : nat, Var (j - 1)) .: ids) 1 = fromTermGo t ids 0.
Proof.
  apply fromTermGo_respects_unshifts => m n;
    rewrite /ids /idsDB /scons //; try (case_match; subst);
    rewrite /= ?PeanoNat.Nat.sub_0_r //.
    (* rewrite ?(plusnO, plusnS, PeanoNat.Nat.sub_0_r) //. *)
Qed.

Lemma fromTermGoId t : fromTermGo t ids 0 = t.
Proof.
  elim: t => /= [^~t]; lazy [hLam hApp]; f_equal => //.
  - (* lazy [ids idsDB]. *)
    by rewrite -[in Var _](plusnO nt).
  - by rewrite fromTermGo_respects_unshift1.
Qed.

Lemma roundTrip (t : DBTerm) : toTerm' (fromTerm' t) = t.
Proof. rewrite /toTerm' /fromTerm'. apply fromTermGoId. Qed.

End UnembeddingGeneral.

Module specialized.

Definition Hoas := Env DB → DB.
Goal Hoas = ((var → var → DBTerm) → var → DBTerm). done. Qed.

Definition hoasToDB (t : Hoas): DBTerm := t ids 0.

(* To produce Hoas terms, we must adapt/specialize this. *)
(* Program Definition fromTermGo `{UntypedLambda exp} : DBTerm → (var → exp) → exp := fix F t env :=
  match t with
  | Var i => env i
  | App f a => app (F f env) (F a env)
  | Lam t => lam (λ x, F t (x .: env))
  end. *)
Definition hhVar i : Hoas := λ env, env i.
Definition hhApp (f a : Hoas) : Hoas := λ env, hApp (f env) (a env).
(* This starts from a de Bruijn representation. *)
(* Definition hhLam (b : Hoas) : Hoas := λ env, hLam (λ x, b (x .: env)). *)
Definition hhLam (b : DB → Hoas) : Hoas := λ env, hLam (λ x, b x (x .: env)).
(* Hm, not sure this is a good idea. *)

End specialized.


(* Definition validSubst (s : var → DB) := ∀ i j, s i j = s (i + j) 0.
Definition isUnshift i s := ∀ n, s n 0 = Var (n - i).

Lemma wanted t s1 s2 i1 i2
  (* (Hs: ∀ j, s1 (j + i1) = s2 (j + i2)): *)
  (Hs : ∀ n, s1 n i1 = s2 n i2)
  (Hs1 : validSubst s1) (Hs2: validSubst s2)
  (Hu1: isUnshift i1 s1) (Hu2 : isUnshift i2 s2):
  fromTermGo t s1 i1 = fromTermGo t s2 i2.
Proof.
  revert s1 s2 i1 i2 Hs Hs1 Hs2 Hu1 Hu2.
  induction t; simpl; intros.
  apply Hs.
  all: f_equal => //.
  all: eauto 2.
  apply IHt.
  intros.
  rewrite /scons. case: n => [//|n].
  { f_equal; lia. }
  { have := Hs (S n).
  rewrite Hs1 Hs2 /= => ?.
  by rewrite Hs1 Hs2 !plusnS.
  }
  1-2: intros ??; asimpl; rewrite /scons; repeat case_match; simplify_eq/= => //.
  all: intros ?; asimpl; rewrite /scons; repeat case_match; simplify_eq/= => //.
Qed.
  (* - case: n => [//|n /=].
    cbv. by rewrite -/plus plusnS.
  - f_equal. apply wanted => j. autosubst. *)

Lemma go2 t : fromTermGo t ((λ j : nat, Var (j - 1)) .: ids) 1 = fromTermGo t ids 0.
Proof.
  apply wanted; repeat intro; asimpl;
    rewrite /ids /idsDB /scons;
    repeat case_match; simplify_eq/=;
    rewrite ?(plusnO, plusnS, PeanoNat.Nat.sub_0_r) //.
Qed.

(* Search _ (?n - 0 = ?n).
  {
  rewrite /scons. case: j => [//|n].
    lazy. by rewrite -/plus plusnS.
  }
    lazy. rewrite -/plus -/minus.
    4: lazy; rewrite -/plus -/minus; f_equal; lia.
  (* induction t; simpl; last by f_equal.
  - case: n => [//|n /=].
    cbv. by rewrite -/plus plusnS.
  - f_equal. apply wanted => j. autosubst. *)
Qed. *)

Lemma fromTermGoId t : fromTermGo t ids 0 = t.
Proof.
  induction t; simpl; cbn; f_equal => //.
  - lazy; f_equal; rewrite -/plus. apply plusnO.
  - f_equal. rewrite -{2}IHt.
  apply go2.
    (* apply wanted => j. autosubst. *)
(*
  apply (wanted t _ ids _ 0).  intros. autosubst.
    (* fromTermGo t ((λ j : nat, Var (j - 1)) .: ids) 1 = t *)
    by rewrite go2. *)
Qed.

Lemma roundTrip (t : DBTerm) : toTerm' (fromTerm' t) = t.
Proof. rewrite /toTerm' /fromTerm'. apply fromTermGoId. Qed. *)
