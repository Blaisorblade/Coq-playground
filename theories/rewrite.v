From stdpp Require Import tactics.

Section flip_proper.
  Context `{R : relation A} `{S : relation B} `{T : relation C} `{U : relation D}.
  Global Instance flip_proper_2 `(!Proper (R ==> S) f) :
    Proper (flip R ==> flip S) f.
  Proof. solve_proper. Qed.
  Global Instance flip_proper_3 `(!Proper (R ==> S ==> T) f) :
    Proper (flip R ==> flip S ==> flip T) f.
  Proof. solve_proper. Qed.
  Global Instance flip_proper_4 `(!Proper (R ==> S ==> T ==> U) f) :
    Proper (flip R ==> flip S ==> flip T ==> flip U) f.
  Proof. solve_proper. Qed.
End flip_proper.
