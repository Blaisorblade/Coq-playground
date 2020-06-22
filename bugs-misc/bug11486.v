Declare Scope sc.
Delimit Scope sc with S.
Definition f (_ _ : bool) : bool := false.
Definition g (x : bool) := false.
Notation "1" := false : sc.
Bind Scope sc with bool.
Notation "a + b" := (f a b) : sc.

Check (g (1 + 1)).
