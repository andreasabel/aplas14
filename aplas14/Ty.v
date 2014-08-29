Inductive Ty (A : Type) : Type :=
| arr : Ty A -> Ty A -> Ty A
| later : A -> Ty A.

Implicit Arguments arr [A].
Implicit Arguments later [A].

CoInductive Ty' : Type :=
| delay : Ty Ty' -> Ty'.

CoFixpoint top : Ty' := 
  delay (later top).

