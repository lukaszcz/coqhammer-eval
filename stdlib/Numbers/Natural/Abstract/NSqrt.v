From Hammer Require Import Hammer.











Require Import NAxioms NSub NZSqrt.

Module NSqrtProp (Import A : NAxiomsSig')(Import B : NSubProp A).

Module Import Private_NZSqrt := Nop <+ NZSqrtProp A A B.

Ltac auto' := trivial; try rewrite <- neq_0_lt_0; auto using le_0_l.
Ltac wrap l := intros; apply l; auto'.



Lemma sqrt_spec' : forall a, √a*√a <= a < S (√a) * S (√a).
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_spec'".   wrap sqrt_spec. Qed.

Definition sqrt_unique : forall a b, b*b<=a<(S b)*(S b) -> √a == b
:= sqrt_unique.

Lemma sqrt_square : forall a, √(a*a) == a.
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_square".   wrap sqrt_square. Qed.

Definition sqrt_le_mono : forall a b, a<=b -> √a <= √b
:= sqrt_le_mono.

Definition sqrt_lt_cancel : forall a b, √a < √b -> a < b
:= sqrt_lt_cancel.

Lemma sqrt_le_square : forall a b, b*b<=a <-> b <= √a.
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_le_square".   wrap sqrt_le_square. Qed.

Lemma sqrt_lt_square : forall a b, a<b*b <-> √a < b.
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_lt_square".   wrap sqrt_lt_square. Qed.

Definition sqrt_0 := sqrt_0.
Definition sqrt_1 := sqrt_1.
Definition sqrt_2 := sqrt_2.

Definition sqrt_lt_lin : forall a, 1<a -> √a<a
:= sqrt_lt_lin.

Lemma sqrt_le_lin : forall a, √a<=a.
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_le_lin".   wrap sqrt_le_lin. Qed.

Definition sqrt_mul_below : forall a b, √a * √b <= √(a*b)
:= sqrt_mul_below.

Lemma sqrt_mul_above : forall a b, √(a*b) < S (√a) * S (√b).
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_mul_above".   wrap sqrt_mul_above. Qed.

Lemma sqrt_succ_le : forall a, √(S a) <= S (√a).
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_succ_le".   wrap sqrt_succ_le. Qed.

Lemma sqrt_succ_or : forall a, √(S a) == S (√a) \/ √(S a) == √a.
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.sqrt_succ_or".   wrap sqrt_succ_or. Qed.

Definition sqrt_add_le : forall a b, √(a+b) <= √a + √b
:= sqrt_add_le.

Lemma add_sqrt_le : forall a b, √a + √b <= √(2*(a+b)).
Proof. hammer_hook "NSqrt" "NSqrt.NSqrtProp.add_sqrt_le".   wrap add_sqrt_le. Qed.



Include NZSqrtUpProp A A B Private_NZSqrt.

End NSqrtProp.
