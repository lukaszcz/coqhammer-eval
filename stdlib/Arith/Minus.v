From Hammer Require Import Hammer.











Require Import PeanoNat Lt Le.

Local Open Scope nat_scope.



Lemma minus_n_O n : n = n - 0.
Proof. hammer_hook "Minus" "Minus.minus_n_O".  
symmetry. apply Nat.sub_0_r.
Qed.



Lemma minus_Sn_m n m : m <= n -> S (n - m) = S n - m.
Proof. hammer_hook "Minus" "Minus.minus_Sn_m".  
intros. symmetry. now apply Nat.sub_succ_l.
Qed.

Theorem pred_of_minus n : pred n = n - 1.
Proof. hammer_hook "Minus" "Minus.pred_of_minus".  
symmetry. apply Nat.sub_1_r.
Qed.



Notation minus_diag := Nat.sub_diag (compat "8.4").

Lemma minus_diag_reverse n : 0 = n - n.
Proof. hammer_hook "Minus" "Minus.minus_diag_reverse".  
symmetry. apply Nat.sub_diag.
Qed.

Notation minus_n_n := minus_diag_reverse.



Lemma minus_plus_simpl_l_reverse n m p : n - m = p + n - (p + m).
Proof. hammer_hook "Minus" "Minus.minus_plus_simpl_l_reverse".  
now rewrite Nat.sub_add_distr, Nat.add_comm, Nat.add_sub.
Qed.



Lemma plus_minus n m p : n = m + p -> p = n - m.
Proof. hammer_hook "Minus" "Minus.plus_minus".  
symmetry. now apply Nat.add_sub_eq_l.
Qed.

Lemma minus_plus n m : n + m - n = m.
Proof. hammer_hook "Minus" "Minus.minus_plus".  
rewrite Nat.add_comm. apply Nat.add_sub.
Qed.

Lemma le_plus_minus_r n m : n <= m -> n + (m - n) = m.
Proof. hammer_hook "Minus" "Minus.le_plus_minus_r".  
rewrite Nat.add_comm. apply Nat.sub_add.
Qed.

Lemma le_plus_minus n m : n <= m -> m = n + (m - n).
Proof. hammer_hook "Minus" "Minus.le_plus_minus".  
intros. symmetry. rewrite Nat.add_comm. now apply Nat.sub_add.
Qed.



Notation minus_le_compat_r :=
Nat.sub_le_mono_r (compat "8.4").

Notation minus_le_compat_l :=
Nat.sub_le_mono_l (compat "8.4").

Notation le_minus := Nat.le_sub_l (compat "8.4").
Notation lt_minus := Nat.sub_lt (compat "8.4").

Lemma lt_O_minus_lt n m : 0 < n - m -> m < n.
Proof. hammer_hook "Minus" "Minus.lt_O_minus_lt".  
apply Nat.lt_add_lt_sub_r.
Qed.

Theorem not_le_minus_0 n m : ~ m <= n -> n - m = 0.
Proof. hammer_hook "Minus" "Minus.not_le_minus_0".  
intros. now apply Nat.sub_0_le, Nat.lt_le_incl, Nat.lt_nge.
Qed.



Hint Resolve minus_n_O: arith.
Hint Resolve minus_Sn_m: arith.
Hint Resolve minus_diag_reverse: arith.
Hint Resolve minus_plus_simpl_l_reverse: arith.
Hint Immediate plus_minus: arith.
Hint Resolve minus_plus: arith.
Hint Resolve le_plus_minus: arith.
Hint Resolve le_plus_minus_r: arith.
Hint Resolve lt_minus: arith.
Hint Immediate lt_O_minus_lt: arith.
