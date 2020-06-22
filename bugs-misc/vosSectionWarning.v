From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
Inductive stuckness : Set :=  NotStuck : stuckness | MaybeStuck : stuckness.
Set Default Proof Using "Type".
Import uPred.
Set Suggest Proof Using.


(* The following development is that of a *Plain* weakest
precondition. In the sense that it does not require any  *)

Class irisG (Λ : language) (Σ : gFunctors) := IrisG {
}.

Definition wp_pre `{irisG Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => Φ v
  | None => ∀ σ1 κ κs n,
     state_interp σ1 (κ ++ κs) n -∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
          ▷ (state_interp σ2 κs (length efs + n) ∗
         wp E e2 Φ ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post)
  end%I.

Local Instance wp_pre_contractive `{irisG Λ Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{irisG Λ Σ} (s : stuckness) :
  coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := fixpoint (wp_pre s).
Definition wp_aux `{irisG Λ Σ} : seal (@wp_def Λ Σ _). by eexists. Qed.
