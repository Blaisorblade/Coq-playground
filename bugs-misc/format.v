Notation "⊤" := True : dms_scope.
Notation " {@ T1 } " := ( and T1 True ) (format "{@  T1  }"): dms_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (and T1 (and T2 .. (and Tn True)..))
  (format "'[v' {@  '[' T1 ']'  ;  '//' '[' T2 ']'  ;  '//' ..  ;  '//' '[' Tn ']'  } ']'") : dms_scope.
Open Scope dms_scope.
Close Scope dms_scope.
Delimit Scope dms_scope with dms.
Check {@ True ; True -> False ; False } % dms.
