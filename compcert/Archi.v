From Hammer Require Import Hammer.



















Require Import ZArith.
Require Import List.

From compcert Require Import Binary.
From compcert Require Import Bits.

Definition ptr64 := false.

Definition big_endian := false.

Definition align_int64 := 4%Z.
Definition align_float64 := 4%Z.

Definition splitlong := negb ptr64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof. hammer_hook "Archi" "Archi.splitlong_ptr32".
unfold splitlong. destruct ptr64; simpl; congruence.
Qed.

Definition default_nan_64 := (true, iter_nat 51 _ xO xH).
Definition default_nan_32 := (true, iter_nat 22 _ xO xH).



Definition choose_nan_64 (l: list (bool * positive)) : bool * positive :=
match l with nil => default_nan_64 | n :: _ => n end.

Definition choose_nan_32 (l: list (bool * positive)) : bool * positive :=
match l with nil => default_nan_32 | n :: _ => n end.

Lemma choose_nan_64_idem: forall n,
choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil).
Proof. hammer_hook "Archi" "Archi.choose_nan_64_idem". auto. Qed.

Lemma choose_nan_32_idem: forall n,
choose_nan_32 (n :: n :: nil) = choose_nan_32 (n :: nil).
Proof. hammer_hook "Archi" "Archi.choose_nan_32_idem". auto. Qed.

Definition fma_order {A: Type} (x y z: A) := (x, y, z).

Definition fma_invalid_mul_is_nan := false.

Definition float_of_single_preserves_sNaN := false.

Global Opaque ptr64 big_endian splitlong
default_nan_64 choose_nan_64
default_nan_32 choose_nan_32
fma_order fma_invalid_mul_is_nan
float_of_single_preserves_sNaN.
