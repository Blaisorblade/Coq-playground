From iris.heap_lang Require Import proofmode.

(** * Superseded by stdpp master. *)
Instance set_unfold_copset_top x : SetUnfoldElemOf x (⊤ : coPset) True.
Proof. by constructor. Qed.

(** * More reusable building blocks *)
(** Support writing external hints for lemmas that must not be applied twice for a goal. *)
(* The usedLemma and un_usedLemma marker is taken from Crush.v (where they were called done and un_done). *)

(** Devious marker predicate to use for encoding state within proof goals *)
Definition usedLemma {T : Type} (x : T) := True.

(** After a round of application with the above, we will have a lot of junk [usedLemma] markers to clean up; hence this tactic. *)
Ltac un_usedLemma :=
  repeat match goal with
           | [ H : usedLemma _ |- _ ] => clear H
         end.
Ltac markUsed H := assert (usedLemma H) by constructor.

Ltac try_once lm :=
    match goal with
    | H : usedLemma lm |- _ => fail 1
    | _ => markUsed lm; eapply lm
    end.
Tactic Notation "try_once_tac" constr(T) tactic(tac) :=
  match goal with
  | H : usedLemma T |- _ => fail 1
  | _ => markUsed T; tac
  end.

(** * Specialized automation. *)

Ltac split_elemof :=
  match goal with
    | H : context [?x ∈ ?e] |- _ =>
    try_once_tac (x ∈ e) destruct (decide (x ∈ e))
    (* | H : context [?x ∉ ?e] |- _ => destruct (decide (x ∈ e)) *)
    | |- context [?x ∈ ?e] =>
    try_once_tac (x ∈ e) destruct (decide (x ∈ e))
    (* destruct (decide (x ∈ e)); markUsed (x ∈ e) *)
    (* | |- context [?x ∉ ?e] => destruct (decide (x ∈ e)) *)
  end.
Ltac set_solver_split :=
  set_solver by (repeat (split_elemof; eauto)).

(** * Debugging help. *)

Ltac print_goal := match goal with |- ?H => idtac H end.
Ltac print_hyps := idtac "<<Hyps>>"; repeat match goal with H : ?T |- _ => idtac H T; fail end.

(** * All 2 testcases that [set_solver_split] has withstood. Buyer beware. *)

Definition thisNameSpace : namespace := nroot .@ "par".
Definition thatNameSpace : namespace := nroot .@ "baz".

Goal (⊤ ∖ ↑thisNameSpace) ∪ (∅ ∪ ↑thisNameSpace) ∖ ∅ ≡@{coPset} ⊤.
Proof.
  Fail set_solver.
  set_solver_split.
  (* Alternative special-case one-line solutions. *)
  (* by rewrite left_id difference_empty difference_union; set_solver. *)
  (* by set_unfold => x; split_elemof; intuition. *)
  (* by set_unfold => x; destruct (decide (x ∈@{coPset} ↑thisNameSpace)); intuition. *)
Qed.

Goal (⊤ ∖ ↑thisNameSpace ∖ ↑thatNameSpace) ∪ (∅ ∪ ↑thisNameSpace ∪ ↑thatNameSpace) ∖ ∅ ≡@{coPset} ⊤.
Proof.
  Fail set_solver.
  by set_solver_split.
  (* by set_solver by (repeat (print_hyps; split_elemof; eauto)). *)
  (* by set_unfold => x; repeat (split_elemof; intuition). *)
Qed.
