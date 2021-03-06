From Hammer Require Import Hammer.













Declare ML Module "r_syntax_plugin".
Require Export ZArith_base.

Parameter R : Set.


Delimit Scope R_scope with R.


Bind Scope R_scope with R.

Local Open Scope R_scope.

Parameter R0 : R.
Parameter R1 : R.
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.
Parameter Rlt : R -> R -> Prop.
Parameter up : R -> Z.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

Infix "<" := Rlt : R_scope.




Definition Rgt (r1 r2:R) : Prop := r2 < r1.


Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.


Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.


Definition Rminus (r1 r2:R) : R := r1 + - r2.


Definition Rdiv (r1 r2:R) : R := r1 * / r2.



Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv   : R_scope.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">"  := Rgt : R_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope.






Fixpoint IPR_2 (p:positive) : R :=
match p with
| xH => R1 + R1
| xO p => (R1 + R1) * IPR_2 p
| xI p => (R1 + R1) * (R1 + IPR_2 p)
end.

Definition IPR (p:positive) : R :=
match p with
| xH => R1
| xO p => IPR_2 p
| xI p => R1 + IPR_2 p
end.
Arguments IPR p%positive : simpl never.


Definition IZR (z:Z) : R :=
match z with
| Z0 => R0
| Zpos n => IPR n
| Zneg n => - IPR n
end.
Arguments IZR z%Z : simpl never.
