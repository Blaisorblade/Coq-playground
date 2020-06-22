From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "Type*".

Definition lockNode : val :=
  rec: "lockN" "y" :=
    if: CAS "y" #false #true
    then #()
    else "lockN" "y".

Definition unlockNode : val :=
  λ: "y",
  "y" <- #false.

Definition prog : val :=
  λ: "x" "y" "v",
  lockNode "y";;
  "x" <- "v";;
  unlockNode "y";; "v".

Section Toy_Template.
  Context `{!heapG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* We should be able to prove the following specs: *)

  Lemma lock_spec (y: loc) :
    <<< ∀ (b: bool), y ↦ #b >>>
        lockNode #y @ ⊤
    <<< y ↦ #true ∗ if b then False else True, RET #() >>>.
  Proof.
    iIntros (Φ) "HP". iLöb as "IH".
    rewrite /lockNode.
    wp_pures.
    wp_apply (aacc_aupd_commit with "IH"). first done.
    awp_apply "IH".
    awp_apply "HP".
    iPoseProof (aupd_aacc with "HP") as "AC".
    wp_cmpxchg as H1 | H2.
    wp_cmpxchg.
    wp_apply . *)
  Admitted.

  Lemma unlock_spec (y: loc) :
    <<< y ↦ #true >>>
        unlockNode #y @ ⊤
    <<< y ↦ #false, RET #() >>>.
  Proof. Admitted.

  Definition is_locked_ref x y v : iProp :=
    (∃ (b: bool), y ↦ #b ∗ if b then True else x ↦ v)%I.

  Lemma prog_spec (x y: loc) (v: val) :
    <<< ∀ (u: val), is_locked_ref x y u >>>
        prog #x #y v @ ⊤
    <<< is_locked_ref x y v, RET #() >>>.
  Proof.
    unfold is_locked_ref.
    iIntros (Φ) "HP". iLöb as "IH".
    wp_lam. wp_pures. wp_bind (lockNode _)%E.
    wp_apply lock_spec.
    About atomic_update.
    SearchAbout atomic_update. (AU << _ >> @ _, _ << _ COMM >>).
