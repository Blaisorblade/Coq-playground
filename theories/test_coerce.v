(* Class Cl (a : Type).
Parameter A : Type.
Instance cl_a : Cl A.

Parameter Foo Bar : Type -> Type.

Parameter conv : forall {k} `{Cl k}, Foo k -> Bar k.
Parameter func : Bar A -> bool.

Coercion conv : Foo >-> Bar.

Fail Definition test (b : Foo A) : bool := func b. *)

Class Cl (a : Type).
Parameter A : Type.
Declare Instance cl_a : Cl A.

Parameter Foo Bar : Type -> Type.

Parameter conv : forall {k} `{Cl k}, Foo k -> Bar k.
Parameter func : forall {a}, Bar a -> bool.

SubClass FooA := Foo A.
SubClass BarA := Bar A.
Coercion conv_A := conv : FooA -> BarA.
(* Not used, doesn't help *)
(* Coercion bar_a_back := @id _ : BarA -> Bar A.
Coercion foo_a_back := @id _ : FooA -> Foo A. *)

(* Not usable, it violates uniform inheritance *)
(* Coercion conv_A' := conv : Foo A -> Bar A. *)

Definition test1 (b : FooA) : bool := func b.
Fail Definition test2 (b : Foo A) : bool := func b.
(* Print Coercion Paths Foo BarA. *)

Definition func_A : Bar A -> bool := func.

Definition test_3 (b : FooA) : bool := func_A b.
Fail Definition test_4 (b : Foo A) : bool := func_A b.

Definition func_A_1 : BarA -> bool := func.

Definition test_5 (b : FooA) : bool := func_A_1 b.
Fail Definition test_6 (b : Foo A) : bool := func_A_1 b.
