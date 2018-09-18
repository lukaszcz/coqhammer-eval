From Hammer Require Import Hammer.












Require Export Arith_base.
Require Import BinInt.
Require Import Zorder.
Require Import Decidable.
Require Import Peano_dec.
Require Export Compare_dec.

Local Open Scope Z_scope.




Theorem Zne_left n m : Zne n m -> Zne (n + - m) 0.
Proof. hammer_hook "auxiliary" "auxiliary.Zne_left".  
unfold Zne. now rewrite <- Z.sub_move_0_r.
Qed.

Theorem Zegal_left n m : n = m -> n + - m = 0.
Proof. hammer_hook "auxiliary" "auxiliary.Zegal_left".  
apply Z.sub_move_0_r.
Qed.

Theorem Zle_left n m : n <= m -> 0 <= m + - n.
Proof. hammer_hook "auxiliary" "auxiliary.Zle_left".  
apply Z.le_0_sub.
Qed.

Theorem Zle_left_rev n m : 0 <= m + - n -> n <= m.
Proof. hammer_hook "auxiliary" "auxiliary.Zle_left_rev".  
apply Z.le_0_sub.
Qed.

Theorem Zlt_left_rev n m : 0 < m + - n -> n < m.
Proof. hammer_hook "auxiliary" "auxiliary.Zlt_left_rev".  
apply Z.lt_0_sub.
Qed.

Theorem Zlt_left_lt n m : n < m -> 0 < m + - n.
Proof. hammer_hook "auxiliary" "auxiliary.Zlt_left_lt".  
apply Z.lt_0_sub.
Qed.

Theorem Zlt_left n m : n < m -> 0 <= m + -1 + - n.
Proof. hammer_hook "auxiliary" "auxiliary.Zlt_left".  
intros. rewrite Z.add_shuffle0. change (-1) with (- Z.succ 0).
now apply Z.le_0_sub, Z.le_succ_l, Z.lt_0_sub.
Qed.

Theorem Zge_left n m : n >= m -> 0 <= n + - m.
Proof. hammer_hook "auxiliary" "auxiliary.Zge_left".  
Z.swap_greater. apply Z.le_0_sub.
Qed.

Theorem Zgt_left n m : n > m -> 0 <= n + -1 + - m.
Proof. hammer_hook "auxiliary" "auxiliary.Zgt_left".  
Z.swap_greater. apply Zlt_left.
Qed.

Theorem Zgt_left_gt n m : n > m -> n + - m > 0.
Proof. hammer_hook "auxiliary" "auxiliary.Zgt_left_gt".  
Z.swap_greater. apply Z.lt_0_sub.
Qed.

Theorem Zgt_left_rev n m : n + - m > 0 -> n > m.
Proof. hammer_hook "auxiliary" "auxiliary.Zgt_left_rev".  
Z.swap_greater. apply Z.lt_0_sub.
Qed.

Theorem Zle_mult_approx n m p :
n > 0 -> p > 0 -> 0 <= m -> 0 <= m * n + p.
Proof. hammer_hook "auxiliary" "auxiliary.Zle_mult_approx".  
Z.swap_greater. intros. Z.order_pos.
Qed.

Theorem Zmult_le_approx n m p :
n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m.
Proof. hammer_hook "auxiliary" "auxiliary.Zmult_le_approx".  
Z.swap_greater. intros. apply Z.lt_succ_r.
apply Z.mul_pos_cancel_r with n; trivial. Z.nzsimpl.
apply Z.le_lt_trans with (m*n+p); trivial.
now apply Z.add_lt_mono_l.
Qed.

