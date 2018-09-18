From Hammer Require Import Hammer.











Require Export ZLt.

Module ZAddOrderProp (Import Z : ZAxiomsMiniSig').
Include ZOrderProp Z.



Theorem add_neg_neg : forall n m, n < 0 -> m < 0 -> n + m < 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.add_neg_neg".  
intros. rewrite <- (add_0_l 0). now apply add_lt_mono.
Qed.

Theorem add_neg_nonpos : forall n m, n < 0 -> m <= 0 -> n + m < 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.add_neg_nonpos".  
intros. rewrite <- (add_0_l 0). now apply add_lt_le_mono.
Qed.

Theorem add_nonpos_neg : forall n m, n <= 0 -> m < 0 -> n + m < 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.add_nonpos_neg".  
intros. rewrite <- (add_0_l 0). now apply add_le_lt_mono.
Qed.

Theorem add_nonpos_nonpos : forall n m, n <= 0 -> m <= 0 -> n + m <= 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.add_nonpos_nonpos".  
intros. rewrite <- (add_0_l 0). now apply add_le_mono.
Qed.



Theorem lt_0_sub : forall n m, 0 < m - n <-> n < m.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_0_sub".  
intros n m. now rewrite (add_lt_mono_r _ _ n), add_0_l, sub_simpl_r.
Qed.

Notation sub_pos := lt_0_sub (only parsing).

Theorem le_0_sub : forall n m, 0 <= m - n <-> n <= m.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_0_sub".  
intros n m. now rewrite (add_le_mono_r _ _ n), add_0_l, sub_simpl_r.
Qed.

Notation sub_nonneg := le_0_sub (only parsing).

Theorem lt_sub_0 : forall n m, n - m < 0 <-> n < m.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_sub_0".  
intros n m. now rewrite (add_lt_mono_r _ _ m), add_0_l, sub_simpl_r.
Qed.

Notation sub_neg := lt_sub_0 (only parsing).

Theorem le_sub_0 : forall n m, n - m <= 0 <-> n <= m.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_sub_0".  
intros n m. now rewrite (add_le_mono_r _ _ m), add_0_l, sub_simpl_r.
Qed.

Notation sub_nonpos := le_sub_0 (only parsing).

Theorem opp_lt_mono : forall n m, n < m <-> - m < - n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.opp_lt_mono".  
intros n m. now rewrite <- lt_0_sub, <- add_opp_l, <- sub_opp_r, lt_0_sub.
Qed.

Theorem opp_le_mono : forall n m, n <= m <-> - m <= - n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.opp_le_mono".  
intros n m. now rewrite <- le_0_sub, <- add_opp_l, <- sub_opp_r, le_0_sub.
Qed.

Theorem opp_pos_neg : forall n, 0 < - n <-> n < 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.opp_pos_neg".  
intro n; now rewrite (opp_lt_mono n 0), opp_0.
Qed.

Theorem opp_neg_pos : forall n, - n < 0 <-> 0 < n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.opp_neg_pos".  
intro n. now rewrite (opp_lt_mono 0 n), opp_0.
Qed.

Theorem opp_nonneg_nonpos : forall n, 0 <= - n <-> n <= 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.opp_nonneg_nonpos".  
intro n; now rewrite (opp_le_mono n 0), opp_0.
Qed.

Theorem opp_nonpos_nonneg : forall n, - n <= 0 <-> 0 <= n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.opp_nonpos_nonneg".  
intro n. now rewrite (opp_le_mono 0 n), opp_0.
Qed.

Theorem lt_m1_0 : -1 < 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_m1_0".  
apply opp_neg_pos, lt_0_1.
Qed.

Theorem sub_lt_mono_l : forall n m p, n < m <-> p - m < p - n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_lt_mono_l".  
intros. now rewrite <- 2 add_opp_r, <- add_lt_mono_l, opp_lt_mono.
Qed.

Theorem sub_lt_mono_r : forall n m p, n < m <-> n - p < m - p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_lt_mono_r".  
intros. now rewrite <- 2 add_opp_r, add_lt_mono_r.
Qed.

Theorem sub_lt_mono : forall n m p q, n < m -> q < p -> n - p < m - q.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_lt_mono".  
intros n m p q H1 H2.
apply lt_trans with (m - p);
[now apply sub_lt_mono_r | now apply sub_lt_mono_l].
Qed.

Theorem sub_le_mono_l : forall n m p, n <= m <-> p - m <= p - n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_le_mono_l".  
intros. now rewrite <- 2 add_opp_r, <- add_le_mono_l, opp_le_mono.
Qed.

Theorem sub_le_mono_r : forall n m p, n <= m <-> n - p <= m - p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_le_mono_r".  
intros. now rewrite <- 2 add_opp_r, add_le_mono_r.
Qed.

Theorem sub_le_mono : forall n m p q, n <= m -> q <= p -> n - p <= m - q.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_le_mono".  
intros n m p q H1 H2.
apply le_trans with (m - p);
[now apply sub_le_mono_r | now apply sub_le_mono_l].
Qed.

Theorem sub_lt_le_mono : forall n m p q, n < m -> q <= p -> n - p < m - q.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_lt_le_mono".  
intros n m p q H1 H2.
apply lt_le_trans with (m - p);
[now apply sub_lt_mono_r | now apply sub_le_mono_l].
Qed.

Theorem sub_le_lt_mono : forall n m p q, n <= m -> q < p -> n - p < m - q.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_le_lt_mono".  
intros n m p q H1 H2.
apply le_lt_trans with (m - p);
[now apply sub_le_mono_r | now apply sub_lt_mono_l].
Qed.

Theorem le_lt_sub_lt : forall n m p q, n <= m -> p - n < q - m -> p < q.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_lt_sub_lt".  
intros n m p q H1 H2. apply (le_lt_add_lt (- m) (- n));
[now apply -> opp_le_mono | now rewrite 2 add_opp_r].
Qed.

Theorem lt_le_sub_lt : forall n m p q, n < m -> p - n <= q - m -> p < q.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_le_sub_lt".  
intros n m p q H1 H2. apply (lt_le_add_lt (- m) (- n));
[now apply -> opp_lt_mono | now rewrite 2 add_opp_r].
Qed.

Theorem le_le_sub_lt : forall n m p q, n <= m -> p - n <= q - m -> p <= q.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_le_sub_lt".  
intros n m p q H1 H2. apply (le_le_add_le (- m) (- n));
[now apply -> opp_le_mono | now rewrite 2 add_opp_r].
Qed.

Theorem lt_add_lt_sub_r : forall n m p, n + p < m <-> n < m - p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_add_lt_sub_r".  
intros n m p. now rewrite (sub_lt_mono_r _ _ p), add_simpl_r.
Qed.

Theorem le_add_le_sub_r : forall n m p, n + p <= m <-> n <= m - p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_add_le_sub_r".  
intros n m p. now rewrite (sub_le_mono_r _ _ p), add_simpl_r.
Qed.

Theorem lt_add_lt_sub_l : forall n m p, n + p < m <-> p < m - n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_add_lt_sub_l".  
intros n m p. rewrite add_comm; apply lt_add_lt_sub_r.
Qed.

Theorem le_add_le_sub_l : forall n m p, n + p <= m <-> p <= m - n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_add_le_sub_l".  
intros n m p. rewrite add_comm; apply le_add_le_sub_r.
Qed.

Theorem lt_sub_lt_add_r : forall n m p, n - p < m <-> n < m + p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_sub_lt_add_r".  
intros n m p. now rewrite (add_lt_mono_r _ _ p), sub_simpl_r.
Qed.

Theorem le_sub_le_add_r : forall n m p, n - p <= m <-> n <= m + p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_sub_le_add_r".  
intros n m p. now rewrite (add_le_mono_r _ _ p), sub_simpl_r.
Qed.

Theorem lt_sub_lt_add_l : forall n m p, n - m < p <-> n < m + p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_sub_lt_add_l".  
intros n m p. rewrite add_comm; apply lt_sub_lt_add_r.
Qed.

Theorem le_sub_le_add_l : forall n m p, n - m <= p <-> n <= m + p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_sub_le_add_l".  
intros n m p. rewrite add_comm; apply le_sub_le_add_r.
Qed.

Theorem lt_sub_lt_add : forall n m p q, n - m < p - q <-> n + q < m + p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_sub_lt_add".  
intros n m p q. now rewrite lt_sub_lt_add_l, add_sub_assoc, <- lt_add_lt_sub_r.
Qed.

Theorem le_sub_le_add : forall n m p q, n - m <= p - q <-> n + q <= m + p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_sub_le_add".  
intros n m p q. now rewrite le_sub_le_add_l, add_sub_assoc, <- le_add_le_sub_r.
Qed.

Theorem lt_sub_pos : forall n m, 0 < m <-> n - m < n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.lt_sub_pos".  
intros n m. now rewrite (sub_lt_mono_l _ _ n), sub_0_r.
Qed.

Theorem le_sub_nonneg : forall n m, 0 <= m <-> n - m <= n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.le_sub_nonneg".  
intros n m. now rewrite (sub_le_mono_l _ _ n), sub_0_r.
Qed.

Theorem sub_lt_cases : forall n m p q, n - m < p - q -> n < m \/ q < p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_lt_cases".  
intros. now apply add_lt_cases, lt_sub_lt_add.
Qed.

Theorem sub_le_cases : forall n m p q, n - m <= p - q -> n <= m \/ q <= p.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_le_cases".  
intros. now apply add_le_cases, le_sub_le_add.
Qed.

Theorem sub_neg_cases : forall n m, n - m < 0 -> n < 0 \/ 0 < m.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_neg_cases".  
intros.
rewrite <- (opp_neg_pos m). apply add_neg_cases. now rewrite add_opp_r.
Qed.

Theorem sub_pos_cases : forall n m, 0 < n - m -> 0 < n \/ m < 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_pos_cases".  
intros.
rewrite <- (opp_pos_neg m). apply add_pos_cases. now rewrite add_opp_r.
Qed.

Theorem sub_nonpos_cases : forall n m, n - m <= 0 -> n <= 0 \/ 0 <= m.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_nonpos_cases".  
intros.
rewrite <- (opp_nonpos_nonneg m). apply add_nonpos_cases. now rewrite add_opp_r.
Qed.

Theorem sub_nonneg_cases : forall n m, 0 <= n - m -> 0 <= n \/ m <= 0.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.sub_nonneg_cases".  
intros.
rewrite <- (opp_nonneg_nonpos m). apply add_nonneg_cases. now rewrite add_opp_r.
Qed.

Section PosNeg.

Variable P : Z.t -> Prop.
Hypothesis P_wd : Proper (eq ==> iff) P.

Theorem zero_pos_neg :
P 0 -> (forall n, 0 < n -> P n /\ P (- n)) -> forall n, P n.
Proof. hammer_hook "ZAddOrder" "ZAddOrder.ZAddOrderProp.zero_pos_neg".  
intros H1 H2 n. destruct (lt_trichotomy n 0) as [H3 | [H3 | H3]].
apply opp_pos_neg, H2 in H3. destruct H3 as [_ H3].
now rewrite opp_involutive in H3.
now rewrite H3.
apply H2 in H3; now destruct H3.
Qed.

End PosNeg.

Ltac zero_pos_neg n := induction_maker n ltac:(apply zero_pos_neg).

End ZAddOrderProp.


