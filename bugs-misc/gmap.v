From stdpp Require Import gmap pmap numbers.

Eval cbv in <[xH := 2]> ∅ : Pmap nat.
Eval vm_compute in (<[1 := 2]> ∅ : gmap nat nat).
