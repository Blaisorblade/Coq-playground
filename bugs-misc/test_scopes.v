Definition T := True.
Notation TT := T.
Notation "'TTT'" := T.

Goal TTT.
simpl "TTT". (* Uh? I'd want `simpl TTT` instead. *)
cbn ["TTT"]. (* Uh? I'd want `cbn [TTT]` instead. *)
unfold TT.
unfold "TTT". (* Uh? I'd want `unfold TTT` instead. *)


Require Import NArith ZArith.
Check 0.
Check (0%nat).
Check 0%N.

Open Scope Z_scope.
