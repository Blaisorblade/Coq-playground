Definition var := nat.
Class Rename (term : Type) := rename : (var -> var) -> term -> term.
