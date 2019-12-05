Require Import List.
Import ListNotations.

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P []
| ForallT_cons (x : A) (l : list A) : P x -> ForallT P l -> ForallT P (x :: l).
Hint Constructors ForallT : core.

Definition fold_ForallT {A R : Type} {P: A -> Type}
    (hnil : R) (hcons : forall (a : A), P a -> R -> R)
    xs (pxs : ForallT P xs): R :=
  ForallT_rect A P (fun _ _ => R) hnil (fun x xs px _ => hcons x px) xs pxs.

Definition fold_ForallT_manual {A R : Type} {P: A -> Type}
  (hnil : R) (hcons : forall (a : A), P a -> R -> R) :
  forall xs, ForallT P xs -> R :=
    fix F xs pxs :=
      match pxs return _ with
      | ForallT_nil _ => hnil
      | ForallT_cons _ x xs px pxs => hcons x px (F xs pxs)
      end.

(** To be able to reuse lemmas on Forall, show that ForallT is equivalent to Forall for predicates in Prop.
    The proof is a bit subtler than you'd think because it can't look into Prop
    to produce proof-relevant part of the result (and that's why I can't inversion until very late.
 *)
Lemma ForallT_Forall {X} (P: X -> Prop) xs: (ForallT P xs -> Forall P xs) * (Forall P xs -> ForallT P xs).
Proof.
  split; (induction xs; intro H; constructor; [|apply IHxs]); inversion H; trivial.
Qed.
