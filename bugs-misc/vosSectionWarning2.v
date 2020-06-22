Set Suggest Proof Using.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Definition check : forall i, forall (U : Type@{i+1}) (Q : Type@{i}), Type@{i+1} := forall P : U, Q.

Definition check2@{i} (U : Type@{i+1}) (Q : U -> Type@{i}) : Type@{i+1} := forall P : U, Q P.
(* Definition check U Q := forall P : U, Q. *)
About check.
Definition TypePred@{i} := check Type@{i+1} Type@{i}.
Definition TypePred@{i} := check Type@{i} Type. @{i + 1}.

(* From https://github.com/coq/coq/issues/11342. *)
Section foo.
  Context {H:True}.
  Theorem test1 : True.
  Proof.
    (* this gets printed with -vos because there's no annotation *)
    idtac "without using".
    exact I.
  Qed.
End foo.

Section foo.
  Context {H:True}.
  Set Default Proof Using "Type".
  Theorem test2 : True.
  Proof.
    (* BUG: this gets printed when compiling with -vos *)
    idtac "proof with default using".
    exact I.
  Qed.

  Theorem test3 : True.
  Proof using Type.
    (* this isn't printed with -vos *)
    idtac "using".
    exact I.
  Qed.
End foo.
