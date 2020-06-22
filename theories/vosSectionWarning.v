Set Default Proof Using "Type".
Set Suggest Proof Using.

Class irisG  := IrisG { }.
Inductive val :=.

Definition wp_pre `{irisG} : val -> (val -> Prop) -> Prop := fun v Φ => Φ v.

Definition wp_def `{irisG} : val -> (val -> Prop) -> Prop := wp_pre.
Definition wp_aux `{irisG} : Prop. exact True. Qed.

Section wp.
Context `{irisG}.
Implicit Types Φ : val -> Prop.
Implicit Types e : val.

(* Weakest pre *)
Lemma wp_unfold e Φ :
  wp_def e Φ <-> wp_pre e Φ.
Proof. easy. Qed.
End wp.
