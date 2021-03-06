From Hammer Require Import Hammer.









Require Import
Bool ZAxioms ZMulOrder ZPow ZDivFloor ZSgnAbs ZParity NZLog.



Module Type ZBitsProp
(Import A : ZAxiomsSig')
(Import B : ZMulOrderProp A)
(Import C : ZParityProp A B)
(Import D : ZSgnAbsProp A B)
(Import E : ZPowProp A B C D)
(Import F : ZDivProp A B D)
(Import G : NZLog2Prop A A A B E).

Include BoolEqualityFacts A.

Ltac order_nz := try apply pow_nonzero; order'.
Ltac order_pos' := try apply abs_nonneg; order_pos.
Hint Rewrite div_0_l mod_0_l div_1_r mod_1_r : nz.



Lemma pow_sub_r : forall a b c, a~=0 -> 0<=c<=b -> a^(b-c) == a^b / a^c.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.pow_sub_r".  
intros a b c Ha (H,H'). rewrite <- (sub_simpl_r b c) at 2.
rewrite pow_add_r; trivial.
rewrite div_mul. reflexivity.
now apply pow_nonzero.
now apply le_0_sub.
Qed.

Lemma pow_div_l : forall a b c, b~=0 -> 0<=c -> a mod b == 0 ->
(a/b)^c == a^c / b^c.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.pow_div_l".  
intros a b c Hb Hc H. rewrite (div_mod a b Hb) at 2.
rewrite H, add_0_r, pow_mul_l, mul_comm, div_mul. reflexivity.
now apply pow_nonzero.
Qed.



Definition b2z (b:bool) := if b then 1 else 0.
Local Coercion b2z : bool >-> t.

Instance b2z_wd : Proper (Logic.eq ==> eq) b2z := _.

Lemma exists_div2 a : exists a' (b:bool), a == 2*a' + b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.exists_div2".  
elim (Even_or_Odd a); [intros (a',H)| intros (a',H)].
exists a'. exists false. now nzsimpl.
exists a'. exists true. now simpl.
Qed.



Lemma testbit_0_r a (b:bool) : testbit (2*a+b) 0 = b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_0_r".  
destruct b; simpl; rewrite ?add_0_r.
apply testbit_odd_0.
apply testbit_even_0.
Qed.

Lemma testbit_succ_r a (b:bool) n : 0<=n ->
testbit (2*a+b) (succ n) = testbit a n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_succ_r".  
destruct b; simpl; rewrite ?add_0_r.
now apply testbit_odd_succ.
now apply testbit_even_succ.
Qed.





Lemma testbit_spec' a n : 0<=n -> a.[n] == (a / 2^n) mod 2.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_spec'".  
intro Hn. revert a. apply le_ind with (4:=Hn).
solve_proper.
intros a. nzsimpl.
destruct (exists_div2 a) as (a' & b & H). rewrite H at 1.
rewrite testbit_0_r. apply mod_unique with a'; trivial.
left. destruct b; split; simpl; order'.
clear n Hn. intros n Hn IH a.
destruct (exists_div2 a) as (a' & b & H). rewrite H at 1.
rewrite testbit_succ_r, IH by trivial. f_equiv.
rewrite pow_succ_r, <- div_div by order_pos. f_equiv.
apply div_unique with b; trivial.
left. destruct b; split; simpl; order'.
Qed.



Lemma testbit_spec a n : 0<=n ->
exists l h, 0<=l<2^n /\ a == l + (a.[n] + 2*h)*2^n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_spec".  
intro Hn. exists (a mod 2^n). exists (a / 2^n / 2). split.
apply mod_pos_bound; order_pos.
rewrite add_comm, mul_comm, (add_comm a.[n]).
rewrite (div_mod a (2^n)) at 1 by order_nz. do 2 f_equiv.
rewrite testbit_spec' by trivial. apply div_mod. order'.
Qed.

Lemma testbit_true : forall a n, 0<=n ->
(a.[n] = true <-> (a / 2^n) mod 2 == 1).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_true".  
intros a n Hn.
rewrite <- testbit_spec' by trivial.
destruct a.[n]; split; simpl; now try order'.
Qed.

Lemma testbit_false : forall a n, 0<=n ->
(a.[n] = false <-> (a / 2^n) mod 2 == 0).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_false".  
intros a n Hn.
rewrite <- testbit_spec' by trivial.
destruct a.[n]; split; simpl; now try order'.
Qed.

Lemma testbit_eqb : forall a n, 0<=n ->
a.[n] = eqb ((a / 2^n) mod 2) 1.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_eqb".  
intros a n Hn.
apply eq_true_iff_eq. now rewrite testbit_true, eqb_eq.
Qed.



Lemma b2z_inj : forall (a0 b0:bool), a0 == b0 -> a0 = b0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.b2z_inj".  
intros [|] [|]; simpl; trivial; order'.
Qed.

Lemma add_b2z_double_div2 : forall (a0:bool) a, (a0+2*a)/2 == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_b2z_double_div2".  
intros a0 a. rewrite mul_comm, div_add by order'.
now rewrite div_small, add_0_l by (destruct a0; split; simpl; order').
Qed.

Lemma add_b2z_double_bit0 : forall (a0:bool) a, (a0+2*a).[0] = a0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_b2z_double_bit0".  
intros a0 a. apply b2z_inj.
rewrite testbit_spec' by order.
nzsimpl. rewrite mul_comm, mod_add by order'.
now rewrite mod_small by (destruct a0; split; simpl; order').
Qed.

Lemma b2z_div2 : forall (a0:bool), a0/2 == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.b2z_div2".  
intros a0. rewrite <- (add_b2z_double_div2 a0 0). now nzsimpl.
Qed.

Lemma b2z_bit0 : forall (a0:bool), a0.[0] = a0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.b2z_bit0".  
intros a0. rewrite <- (add_b2z_double_bit0 a0 0) at 2. now nzsimpl.
Qed.



Lemma testbit_unique : forall a n (a0:bool) l h,
0<=l<2^n -> a == l + (a0 + 2*h)*2^n -> a.[n] = a0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_unique".  
intros a n a0 l h Hl EQ.
assert (0<=n).
destruct (le_gt_cases 0 n) as [Hn|Hn]; trivial.
rewrite pow_neg_r in Hl by trivial. destruct Hl; order.
apply b2z_inj. rewrite testbit_spec' by trivial.
symmetry. apply mod_unique with h.
left; destruct a0; simpl; split; order'.
symmetry. apply div_unique with l.
now left.
now rewrite add_comm, (add_comm _ a0), mul_comm.
Qed.



Lemma bits_0 : forall n, 0.[n] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_0".  
intros n.
destruct (le_gt_cases 0 n).
apply testbit_false; trivial. nzsimpl; order_nz.
now apply testbit_neg_r.
Qed.



Lemma bits_opp : forall a n, 0<=n -> (-a).[n] = negb (P a).[n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_opp".  
intros a n Hn.
destruct (testbit_spec (-a) n Hn) as (l & h & Hl & EQ).
fold (b2z (-a).[n]) in EQ.
apply negb_sym.
apply testbit_unique with (2^n-l-1) (-h-1).
split.
apply lt_succ_r. rewrite sub_1_r, succ_pred. now apply lt_0_sub.
apply le_succ_l. rewrite sub_1_r, succ_pred. apply le_sub_le_add_r.
rewrite <- (add_0_r (2^n)) at 1. now apply add_le_mono_l.
rewrite <- add_sub_swap, sub_1_r. f_equiv.
apply opp_inj. rewrite opp_add_distr, opp_sub_distr.
rewrite (add_comm _ l), <- add_assoc.
rewrite EQ at 1. apply add_cancel_l.
rewrite <- opp_add_distr.
rewrite <- (mul_1_l (2^n)) at 2. rewrite <- mul_add_distr_r.
rewrite <- mul_opp_l.
f_equiv.
rewrite !opp_add_distr.
rewrite <- mul_opp_r.
rewrite opp_sub_distr, opp_involutive.
rewrite (add_comm h).
rewrite mul_add_distr_l.
rewrite !add_assoc.
apply add_cancel_r.
rewrite mul_1_r.
rewrite add_comm, add_assoc, !add_opp_r, sub_1_r, two_succ, pred_succ.
destruct (-a).[n]; simpl. now rewrite sub_0_r. now nzsimpl'.
Qed.



Lemma bits_m1 : forall n, 0<=n -> (-1).[n] = true.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_m1".  
intros. now rewrite bits_opp, one_succ, pred_succ, bits_0.
Qed.



Lemma bit0_odd : forall a, a.[0] = odd a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bit0_odd".  
intros. symmetry.
destruct (exists_div2 a) as (a' & b & EQ).
rewrite EQ, testbit_0_r, add_comm, odd_add_mul_2.
destruct b; simpl; apply odd_1 || apply odd_0.
Qed.

Lemma bit0_eqb : forall a, a.[0] = eqb (a mod 2) 1.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bit0_eqb".  
intros a. rewrite testbit_eqb by order. now nzsimpl.
Qed.

Lemma bit0_mod : forall a, a.[0] == a mod 2.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bit0_mod".  
intros a. rewrite testbit_spec' by order. now nzsimpl.
Qed.



Lemma testbit_odd : forall a n, a.[n] = odd (a>>n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_odd".  
intros. now rewrite <- bit0_odd, shiftr_spec, add_0_l.
Qed.



Lemma bit_log2 : forall a, 0<a -> a.[log2 a] = true.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bit_log2".  
intros a Ha.
assert (Ha' := log2_nonneg a).
destruct (log2_spec_alt a Ha) as (r & EQ & Hr).
rewrite EQ at 1.
rewrite testbit_true, add_comm by trivial.
rewrite <- (mul_1_l (2^log2 a)) at 1.
rewrite div_add by order_nz.
rewrite div_small; trivial.
rewrite add_0_l. apply mod_small. split; order'.
Qed.

Lemma bits_above_log2 : forall a n, 0<=a -> log2 a < n ->
a.[n] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_above_log2".  
intros a n Ha H.
assert (Hn : 0<=n).
transitivity (log2 a). apply log2_nonneg. order'.
rewrite testbit_false by trivial.
rewrite div_small. nzsimpl; order'.
split. order. apply log2_lt_cancel. now rewrite log2_pow2.
Qed.





Lemma bit_log2_neg : forall a, a < -1 -> a.[log2 (P (-a))] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bit_log2_neg".  
intros a Ha.
rewrite <- (opp_involutive a) at 1.
rewrite bits_opp.
apply negb_false_iff.
apply bit_log2.
apply opp_lt_mono in Ha. rewrite opp_involutive in Ha.
apply lt_succ_lt_pred. now rewrite <- one_succ.
apply log2_nonneg.
Qed.

Lemma bits_above_log2_neg : forall a n, a < 0 -> log2 (P (-a)) < n ->
a.[n] = true.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_above_log2_neg".  
intros a n Ha H.
assert (Hn : 0<=n).
transitivity (log2 (P (-a))). apply log2_nonneg. order'.
rewrite <- (opp_involutive a), bits_opp, negb_true_iff by trivial.
apply bits_above_log2; trivial.
now rewrite <- opp_succ, opp_nonneg_nonpos, le_succ_l.
Qed.



Lemma bits_iff_nonneg : forall a n, log2 (abs a) < n ->
(0<=a <-> a.[n] = false).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_iff_nonneg".  
intros a n Hn. split; intros H.
rewrite abs_eq in Hn; trivial. now apply bits_above_log2.
destruct (le_gt_cases 0 a); trivial.
rewrite abs_neq in Hn by order.
rewrite bits_above_log2_neg in H; try easy.
apply le_lt_trans with (log2 (-a)); trivial.
apply log2_le_mono. apply le_pred_l.
Qed.

Lemma bits_iff_nonneg' : forall a,
0<=a <-> a.[S (log2 (abs a))] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_iff_nonneg'".  
intros. apply bits_iff_nonneg. apply lt_succ_diag_r.
Qed.

Lemma bits_iff_nonneg_ex : forall a,
0<=a <-> (exists k, forall m, k<m -> a.[m] = false).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_iff_nonneg_ex".  
intros a. split.
intros Ha. exists (log2 a). intros m Hm. now apply bits_above_log2.
intros (k,Hk). destruct (le_gt_cases k (log2 (abs a))).
now apply bits_iff_nonneg', Hk, lt_succ_r.
apply (bits_iff_nonneg a (S k)).
now apply lt_succ_r, lt_le_incl.
apply Hk. apply lt_succ_diag_r.
Qed.

Lemma bits_iff_neg : forall a n, log2 (abs a) < n ->
(a<0 <-> a.[n] = true).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_iff_neg".  
intros a n Hn.
now rewrite lt_nge, <- not_false_iff_true, (bits_iff_nonneg a n).
Qed.

Lemma bits_iff_neg' : forall a, a<0 <-> a.[S (log2 (abs a))] = true.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_iff_neg'".  
intros. apply bits_iff_neg. apply lt_succ_diag_r.
Qed.

Lemma bits_iff_neg_ex : forall a,
a<0 <-> (exists k, forall m, k<m -> a.[m] = true).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_iff_neg_ex".  
intros a. split.
intros Ha. exists (log2 (P (-a))). intros m Hm. now apply bits_above_log2_neg.
intros (k,Hk). destruct (le_gt_cases k (log2 (abs a))).
now apply bits_iff_neg', Hk, lt_succ_r.
apply (bits_iff_neg a (S k)).
now apply lt_succ_r, lt_le_incl.
apply Hk. apply lt_succ_diag_r.
Qed.



Lemma div2_bits : forall a n, 0<=n -> (a/2).[n] = a.[S n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.div2_bits".  
intros a n Hn.
apply eq_true_iff_eq. rewrite 2 testbit_true by order_pos.
rewrite pow_succ_r by trivial.
now rewrite div_div by order_pos.
Qed.

Lemma div_pow2_bits : forall a n m, 0<=n -> 0<=m -> (a/2^n).[m] = a.[m+n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.div_pow2_bits".  
intros a n m Hn. revert a m. apply le_ind with (4:=Hn).
solve_proper.
intros a m Hm. now nzsimpl.
clear n Hn. intros n Hn IH a m Hm. nzsimpl; trivial.
rewrite <- div_div by order_pos.
now rewrite IH, div2_bits by order_pos.
Qed.

Lemma double_bits_succ : forall a n, (2*a).[S n] = a.[n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.double_bits_succ".  
intros a n.
destruct (le_gt_cases 0 n) as [Hn|Hn].
now rewrite <- div2_bits, mul_comm, div_mul by order'.
rewrite (testbit_neg_r a n Hn).
apply le_succ_l in Hn. le_elim Hn.
now rewrite testbit_neg_r.
now rewrite Hn, bit0_odd, odd_mul, odd_2.
Qed.

Lemma double_bits : forall a n, (2*a).[n] = a.[P n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.double_bits".  
intros a n. rewrite <- (succ_pred n) at 1. apply double_bits_succ.
Qed.

Lemma mul_pow2_bits_add : forall a n m, 0<=n -> (a*2^n).[n+m] = a.[m].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.mul_pow2_bits_add".  
intros a n m Hn. revert a m. apply le_ind with (4:=Hn).
solve_proper.
intros a m. now nzsimpl.
clear n Hn. intros n Hn IH a m. nzsimpl; trivial.
rewrite mul_assoc, (mul_comm _ 2), <- mul_assoc.
now rewrite double_bits_succ.
Qed.

Lemma mul_pow2_bits : forall a n m, 0<=n -> (a*2^n).[m] = a.[m-n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.mul_pow2_bits".  
intros.
rewrite <- (add_simpl_r m n) at 1. rewrite add_sub_swap, add_comm.
now apply mul_pow2_bits_add.
Qed.

Lemma mul_pow2_bits_low : forall a n m, m<n -> (a*2^n).[m] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.mul_pow2_bits_low".  
intros.
destruct (le_gt_cases 0 n).
rewrite mul_pow2_bits by trivial.
apply testbit_neg_r. now apply lt_sub_0.
now rewrite pow_neg_r, mul_0_r, bits_0.
Qed.



Lemma mod_pow2_bits_high : forall a n m, 0<=n<=m ->
(a mod 2^n).[m] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.mod_pow2_bits_high".  
intros a n m (Hn,H).
destruct (mod_pos_bound a (2^n)) as [LE LT]. order_pos.
le_elim LE.
apply bits_above_log2; try order.
apply lt_le_trans with n; trivial.
apply log2_lt_pow2; trivial.
now rewrite <- LE, bits_0.
Qed.

Lemma mod_pow2_bits_low : forall a n m, m<n ->
(a mod 2^n).[m] = a.[m].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.mod_pow2_bits_low".  
intros a n m H.
destruct (le_gt_cases 0 m) as [Hm|Hm]; [|now rewrite !testbit_neg_r].
rewrite testbit_eqb; trivial.
rewrite <- (mod_add _ (2^(P (n-m))*(a/2^n))) by order'.
rewrite <- div_add by order_nz.
rewrite (mul_comm _ 2), mul_assoc, <- pow_succ_r, succ_pred.
rewrite mul_comm, mul_assoc, <- pow_add_r, (add_comm m), sub_add; trivial.
rewrite add_comm, <- div_mod by order_nz.
symmetry. apply testbit_eqb; trivial.
apply le_0_sub; order.
now apply lt_le_pred, lt_0_sub.
Qed.



Definition eqf (f g:t -> bool) := forall n:t, f n = g n.

Instance eqf_equiv : Equivalence eqf.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.eqf_equiv".  
split; congruence.
Qed.

Local Infix "===" := eqf (at level 70, no associativity).

Instance testbit_eqf : Proper (eq==>eqf) testbit.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.testbit_eqf".  
intros a a' Ha n. now rewrite Ha.
Qed.



Lemma bits_inj_0 :
forall a, (forall n, a.[n] = false) -> a == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_inj_0".  
intros a H. destruct (lt_trichotomy a 0) as [Ha|[Ha|Ha]]; trivial.
apply (bits_above_log2_neg a (S (log2 (P (-a))))) in Ha.
now rewrite H in Ha.
apply lt_succ_diag_r.
apply bit_log2 in Ha. now rewrite H in Ha.
Qed.



Lemma bits_inj : forall a b, testbit a === testbit b -> a == b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_inj".  
assert (AUX : forall n, 0<=n -> forall a b,
0<=a<2^n -> testbit a === testbit b -> a == b).
intros n Hn. apply le_ind with (4:=Hn).
solve_proper.
intros a b Ha H. rewrite pow_0_r, one_succ, lt_succ_r in Ha.
assert (Ha' : a == 0) by (destruct Ha; order).
rewrite Ha' in *.
symmetry. apply bits_inj_0.
intros m. now rewrite <- H, bits_0.
clear n Hn. intros n Hn IH a b (Ha,Ha') H.
rewrite (div_mod a 2), (div_mod b 2) by order'.
f_equiv; [ | now rewrite <- 2 bit0_mod, H].
f_equiv.
apply IH.
split. apply div_pos; order'.
apply div_lt_upper_bound. order'. now rewrite <- pow_succ_r.
intros m.
destruct (le_gt_cases 0 m).
rewrite 2 div2_bits by trivial. apply H.
now rewrite 2 testbit_neg_r.
intros a b H.
destruct (le_gt_cases 0 a) as [Ha|Ha].
apply (AUX a); trivial. split; trivial.
apply pow_gt_lin_r; order'.
apply succ_inj, opp_inj.
assert (0 <= - S a).
apply opp_le_mono. now rewrite opp_involutive, opp_0, le_succ_l.
apply (AUX (-(S a))); trivial. split; trivial.
apply pow_gt_lin_r; order'.
intros m. destruct (le_gt_cases 0 m).
now rewrite 2 bits_opp, 2 pred_succ, H.
now rewrite 2 testbit_neg_r.
Qed.

Lemma bits_inj_iff : forall a b, testbit a === testbit b <-> a == b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_inj_iff".  
split. apply bits_inj. intros EQ; now rewrite EQ.
Qed.



Lemma bits_inj' : forall a b,
(forall n, 0<=n -> a.[n] = b.[n]) -> a == b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_inj'".  
intros a b H. apply bits_inj.
intros n. destruct (le_gt_cases 0 n).
now apply H.
now rewrite 2 testbit_neg_r.
Qed.

Lemma bits_inj_iff' : forall a b, (forall n, 0<=n -> a.[n] = b.[n]) <-> a == b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.bits_inj_iff'".  
split. apply bits_inj'. intros EQ n Hn; now rewrite EQ.
Qed.

Ltac bitwise := apply bits_inj'; intros ?m ?Hm; autorewrite with bitwise.

Hint Rewrite lxor_spec lor_spec land_spec ldiff_spec bits_0 : bitwise.



Lemma are_bits : forall (f:t->bool), Proper (eq==>Logic.eq) f ->
((exists n, forall m, 0<=m -> f m = n.[m]) <->
(exists k, forall m, k<=m -> f m = f k)).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.are_bits".  
intros f Hf. split.
intros (a,H).
destruct (le_gt_cases 0 a).
exists (S (log2 a)). intros m Hm. apply le_succ_l in Hm.
rewrite 2 H, 2 bits_above_log2; trivial using lt_succ_diag_r.
order_pos. apply le_trans with (log2 a); order_pos.
exists (S (log2 (P (-a)))). intros m Hm. apply le_succ_l in Hm.
rewrite 2 H, 2 bits_above_log2_neg; trivial using lt_succ_diag_r.
order_pos. apply le_trans with (log2 (P (-a))); order_pos.
intros (k,Hk).
destruct (lt_ge_cases k 0) as [LT|LE].
case_eq (f 0); intros H0.
exists (-1). intros m Hm. rewrite bits_m1, Hk by order.
symmetry; rewrite <- H0. apply Hk; order.
exists 0. intros m Hm. rewrite bits_0, Hk by order.
symmetry; rewrite <- H0. apply Hk; order.
revert f Hf Hk. apply le_ind with (4:=LE).

apply proper_sym_impl_iff. exact eq_sym.
clear k LE. intros k k' Hk IH f Hf H. apply IH; trivial.
now setoid_rewrite Hk.

intros f Hf H0. destruct (f 0).
exists (-1). intros m Hm. now rewrite bits_m1, H0.
exists 0. intros m Hm. now rewrite bits_0, H0.
clear k LE. intros k LE IH f Hf Hk.
destruct (IH (fun m => f (S m))) as (n, Hn).
solve_proper.
intros m Hm. apply Hk. now rewrite <- succ_le_mono.
exists (f 0 + 2*n). intros m Hm.
le_elim Hm.
rewrite <- (succ_pred m), Hn, <- div2_bits.
rewrite mul_comm, div_add, b2z_div2, add_0_l; trivial. order'.
now rewrite <- lt_succ_r, succ_pred.
now rewrite <- lt_succ_r, succ_pred.
rewrite <- Hm.
symmetry. apply add_b2z_double_bit0.
Qed.





Lemma shiftl_spec : forall a n m, 0<=m -> (a << n).[m] = a.[m-n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_spec".  
intros.
destruct (le_gt_cases n m).
now apply shiftl_spec_high.
rewrite shiftl_spec_low, testbit_neg_r; trivial. now apply lt_sub_0.
Qed.



Lemma shiftr_opp_r : forall a n, a >> (-n) == a << n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_opp_r".  
intros. bitwise. now rewrite shiftr_spec, shiftl_spec, add_opp_r.
Qed.

Lemma shiftl_opp_r : forall a n, a << (-n) == a >> n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_opp_r".  
intros. bitwise. now rewrite shiftr_spec, shiftl_spec, sub_opp_r.
Qed.



Lemma shiftr_div_pow2 : forall a n, 0<=n -> a >> n == a / 2^n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_div_pow2".  
intros. bitwise. now rewrite shiftr_spec, div_pow2_bits.
Qed.

Lemma shiftr_mul_pow2 : forall a n, n<=0 -> a >> n == a * 2^(-n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_mul_pow2".  
intros. bitwise. rewrite shiftr_spec, mul_pow2_bits; trivial.
now rewrite sub_opp_r.
now apply opp_nonneg_nonpos.
Qed.

Lemma shiftl_mul_pow2 : forall a n, 0<=n -> a << n == a * 2^n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_mul_pow2".  
intros. bitwise. now rewrite shiftl_spec, mul_pow2_bits.
Qed.

Lemma shiftl_div_pow2 : forall a n, n<=0 -> a << n == a / 2^(-n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_div_pow2".  
intros. bitwise. rewrite shiftl_spec, div_pow2_bits; trivial.
now rewrite add_opp_r.
now apply opp_nonneg_nonpos.
Qed.



Instance shiftr_wd : Proper (eq==>eq==>eq) shiftr.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_wd".  
intros a a' Ha n n' Hn.
destruct (le_ge_cases n 0) as [H|H]; assert (H':=H); rewrite Hn in H'.
now rewrite 2 shiftr_mul_pow2, Ha, Hn.
now rewrite 2 shiftr_div_pow2, Ha, Hn.
Qed.

Instance shiftl_wd : Proper (eq==>eq==>eq) shiftl.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_wd".  
intros a a' Ha n n' Hn. now rewrite <- 2 shiftr_opp_r, Ha, Hn.
Qed.



Lemma shiftl_spec_alt : forall a n m, 0<=n -> (a << n).[m+n] = a.[m].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_spec_alt".  
intros. now rewrite shiftl_mul_pow2, mul_pow2_bits, add_simpl_r.
Qed.



Lemma shiftl_shiftl : forall a n m, 0<=n ->
(a << n) << m == a << (n+m).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_shiftl".  
intros a n p Hn. bitwise.
rewrite 2 (shiftl_spec _ _ m) by trivial.
rewrite add_comm, sub_add_distr.
destruct (le_gt_cases 0 (m-p)) as [H|H].
now rewrite shiftl_spec.
rewrite 2 testbit_neg_r; trivial.
apply lt_sub_0. now apply lt_le_trans with 0.
Qed.

Lemma shiftr_shiftl_l : forall a n m, 0<=n ->
(a << n) >> m == a << (n-m).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_shiftl_l".  
intros. now rewrite <- shiftl_opp_r, shiftl_shiftl, add_opp_r.
Qed.

Lemma shiftr_shiftl_r : forall a n m, 0<=n ->
(a << n) >> m == a >> (m-n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_shiftl_r".  
intros. now rewrite <- 2 shiftl_opp_r, shiftl_shiftl, opp_sub_distr, add_comm.
Qed.

Lemma shiftr_shiftr : forall a n m, 0<=m ->
(a >> n) >> m == a >> (n+m).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_shiftr".  
intros a n p Hn. bitwise.
rewrite 3 shiftr_spec; trivial.
now rewrite (add_comm n p), add_assoc.
now apply add_nonneg_nonneg.
Qed.



Lemma shiftl_1_l : forall n, 1 << n == 2^n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_1_l".  
intros n. destruct (le_gt_cases 0 n).
now rewrite shiftl_mul_pow2, mul_1_l.
rewrite shiftl_div_pow2, div_1_l, pow_neg_r; try order.
apply pow_gt_1. order'. now apply opp_pos_neg.
Qed.

Lemma shiftl_0_r : forall a, a << 0 == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_0_r".  
intros. rewrite shiftl_mul_pow2 by order. now nzsimpl.
Qed.

Lemma shiftr_0_r : forall a, a >> 0 == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_0_r".  
intros. now rewrite <- shiftl_opp_r, opp_0, shiftl_0_r.
Qed.

Lemma shiftl_0_l : forall n, 0 << n == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_0_l".  
intros.
destruct (le_ge_cases 0 n).
rewrite shiftl_mul_pow2 by trivial. now nzsimpl.
rewrite shiftl_div_pow2 by trivial.
rewrite <- opp_nonneg_nonpos in H. nzsimpl; order_nz.
Qed.

Lemma shiftr_0_l : forall n, 0 >> n == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_0_l".  
intros. now rewrite <- shiftl_opp_r, shiftl_0_l.
Qed.

Lemma shiftl_eq_0_iff : forall a n, 0<=n -> (a << n == 0 <-> a == 0).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_eq_0_iff".  
intros a n Hn.
rewrite shiftl_mul_pow2 by trivial. rewrite eq_mul_0. split.
intros [H | H]; trivial. contradict H; order_nz.
intros H. now left.
Qed.

Lemma shiftr_eq_0_iff : forall a n,
a >> n == 0 <-> a==0 \/ (0<a /\ log2 a < n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_eq_0_iff".  
intros a n.
destruct (le_gt_cases 0 n) as [Hn|Hn].
rewrite shiftr_div_pow2, div_small_iff by order_nz.
destruct (lt_trichotomy a 0) as [LT|[EQ|LT]].
split.
intros [(H,_)|(H,H')]. order. generalize (pow_nonneg 2 n le_0_2); order.
intros [H|(H,H')]; order.
rewrite EQ. split. now left. intros _; left. split; order_pos.
split. intros [(H,H')|(H,H')]; right. split; trivial.
apply log2_lt_pow2; trivial.
generalize (pow_nonneg 2 n le_0_2); order.
intros [H|(H,H')]. order. left.
split. order. now apply log2_lt_pow2.
rewrite shiftr_mul_pow2 by order. rewrite eq_mul_0.
split; intros [H|H].
now left.
elim (pow_nonzero 2 (-n)); try apply opp_nonneg_nonpos; order'.
now left.
destruct H. generalize (log2_nonneg a); order.
Qed.

Lemma shiftr_eq_0 : forall a n, 0<=a -> log2 a < n -> a >> n == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_eq_0".  
intros a n Ha H. apply shiftr_eq_0_iff.
le_elim Ha. right. now split. now left.
Qed.



Lemma div2_div : forall a, div2 a == a/2.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.div2_div".  
intros. rewrite div2_spec, shiftr_div_pow2. now nzsimpl. order'.
Qed.

Instance div2_wd : Proper (eq==>eq) div2.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.div2_wd".  
intros a a' Ha. now rewrite 2 div2_div, Ha.
Qed.

Lemma div2_odd : forall a, a == 2*(div2 a) + odd a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.div2_odd".  
intros a. rewrite div2_div, <- bit0_odd, bit0_mod.
apply div_mod. order'.
Qed.



Instance lxor_wd : Proper (eq ==> eq ==> eq) lxor.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_wd".  
intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Instance land_wd : Proper (eq ==> eq ==> eq) land.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_wd".  
intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Instance lor_wd : Proper (eq ==> eq ==> eq) lor.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_wd".  
intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Instance ldiff_wd : Proper (eq ==> eq ==> eq) ldiff.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_wd".  
intros a a' Ha b b' Hb. bitwise. now rewrite Ha, Hb.
Qed.

Lemma lxor_eq : forall a a', lxor a a' == 0 -> a == a'.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_eq".  
intros a a' H. bitwise. apply xorb_eq.
now rewrite <- lxor_spec, H, bits_0.
Qed.

Lemma lxor_nilpotent : forall a, lxor a a == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_nilpotent".  
intros. bitwise. apply xorb_nilpotent.
Qed.

Lemma lxor_eq_0_iff : forall a a', lxor a a' == 0 <-> a == a'.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_eq_0_iff".  
split. apply lxor_eq. intros EQ; rewrite EQ; apply lxor_nilpotent.
Qed.

Lemma lxor_0_l : forall a, lxor 0 a == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_0_l".  
intros. bitwise. apply xorb_false_l.
Qed.

Lemma lxor_0_r : forall a, lxor a 0 == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_0_r".  
intros. bitwise. apply xorb_false_r.
Qed.

Lemma lxor_comm : forall a b, lxor a b == lxor b a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_comm".  
intros. bitwise. apply xorb_comm.
Qed.

Lemma lxor_assoc :
forall a b c, lxor (lxor a b) c == lxor a (lxor b c).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_assoc".  
intros. bitwise. apply xorb_assoc.
Qed.

Lemma lor_0_l : forall a, lor 0 a == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_0_l".  
intros. bitwise. trivial.
Qed.

Lemma lor_0_r : forall a, lor a 0 == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_0_r".  
intros. bitwise. apply orb_false_r.
Qed.

Lemma lor_comm : forall a b, lor a b == lor b a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_comm".  
intros. bitwise. apply orb_comm.
Qed.

Lemma lor_assoc :
forall a b c, lor a (lor b c) == lor (lor a b) c.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_assoc".  
intros. bitwise. apply orb_assoc.
Qed.

Lemma lor_diag : forall a, lor a a == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_diag".  
intros. bitwise. apply orb_diag.
Qed.

Lemma lor_eq_0_l : forall a b, lor a b == 0 -> a == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_eq_0_l".  
intros a b H. bitwise.
apply (orb_false_iff a.[m] b.[m]).
now rewrite <- lor_spec, H, bits_0.
Qed.

Lemma lor_eq_0_iff : forall a b, lor a b == 0 <-> a == 0 /\ b == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_eq_0_iff".  
intros a b. split.
split. now apply lor_eq_0_l in H.
rewrite lor_comm in H. now apply lor_eq_0_l in H.
intros (EQ,EQ'). now rewrite EQ, lor_0_l.
Qed.

Lemma land_0_l : forall a, land 0 a == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_0_l".  
intros. bitwise. trivial.
Qed.

Lemma land_0_r : forall a, land a 0 == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_0_r".  
intros. bitwise. apply andb_false_r.
Qed.

Lemma land_comm : forall a b, land a b == land b a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_comm".  
intros. bitwise. apply andb_comm.
Qed.

Lemma land_assoc :
forall a b c, land a (land b c) == land (land a b) c.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_assoc".  
intros. bitwise. apply andb_assoc.
Qed.

Lemma land_diag : forall a, land a a == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_diag".  
intros. bitwise. apply andb_diag.
Qed.

Lemma ldiff_0_l : forall a, ldiff 0 a == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_0_l".  
intros. bitwise. trivial.
Qed.

Lemma ldiff_0_r : forall a, ldiff a 0 == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_0_r".  
intros. bitwise. now rewrite andb_true_r.
Qed.

Lemma ldiff_diag : forall a, ldiff a a == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_diag".  
intros. bitwise. apply andb_negb_r.
Qed.

Lemma lor_land_distr_l : forall a b c,
lor (land a b) c == land (lor a c) (lor b c).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_land_distr_l".  
intros. bitwise. apply orb_andb_distrib_l.
Qed.

Lemma lor_land_distr_r : forall a b c,
lor a (land b c) == land (lor a b) (lor a c).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_land_distr_r".  
intros. bitwise. apply orb_andb_distrib_r.
Qed.

Lemma land_lor_distr_l : forall a b c,
land (lor a b) c == lor (land a c) (land b c).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_lor_distr_l".  
intros. bitwise. apply andb_orb_distrib_l.
Qed.

Lemma land_lor_distr_r : forall a b c,
land a (lor b c) == lor (land a b) (land a c).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_lor_distr_r".  
intros. bitwise. apply andb_orb_distrib_r.
Qed.

Lemma ldiff_ldiff_l : forall a b c,
ldiff (ldiff a b) c == ldiff a (lor b c).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_ldiff_l".  
intros. bitwise. now rewrite negb_orb, andb_assoc.
Qed.

Lemma lor_ldiff_and : forall a b,
lor (ldiff a b) (land a b) == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_ldiff_and".  
intros. bitwise.
now rewrite <- andb_orb_distrib_r, orb_comm, orb_negb_r, andb_true_r.
Qed.

Lemma land_ldiff : forall a b,
land (ldiff a b) b == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_ldiff".  
intros. bitwise.
now rewrite <-andb_assoc, (andb_comm (negb _)), andb_negb_r, andb_false_r.
Qed.



Definition setbit a n := lor a (1 << n).
Definition clearbit a n := ldiff a (1 << n).

Lemma setbit_spec' : forall a n, setbit a n == lor a (2^n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.setbit_spec'".  
intros. unfold setbit. now rewrite shiftl_1_l.
Qed.

Lemma clearbit_spec' : forall a n, clearbit a n == ldiff a (2^n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.clearbit_spec'".  
intros. unfold clearbit. now rewrite shiftl_1_l.
Qed.

Instance setbit_wd : Proper (eq==>eq==>eq) setbit.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.setbit_wd".   unfold setbit. solve_proper. Qed.

Instance clearbit_wd : Proper (eq==>eq==>eq) clearbit.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.clearbit_wd".   unfold clearbit. solve_proper. Qed.

Lemma pow2_bits_true : forall n, 0<=n -> (2^n).[n] = true.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.pow2_bits_true".  
intros. rewrite <- (mul_1_l (2^n)).
now rewrite mul_pow2_bits, sub_diag, bit0_odd, odd_1.
Qed.

Lemma pow2_bits_false : forall n m, n~=m -> (2^n).[m] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.pow2_bits_false".  
intros.
destruct (le_gt_cases 0 n); [|now rewrite pow_neg_r, bits_0].
destruct (le_gt_cases n m).
rewrite <- (mul_1_l (2^n)), mul_pow2_bits; trivial.
rewrite <- (succ_pred (m-n)), <- div2_bits.
now rewrite div_small, bits_0 by (split; order').
rewrite <- lt_succ_r, succ_pred, lt_0_sub. order.
rewrite <- (mul_1_l (2^n)), mul_pow2_bits_low; trivial.
Qed.

Lemma pow2_bits_eqb : forall n m, 0<=n -> (2^n).[m] = eqb n m.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.pow2_bits_eqb".  
intros n m Hn. apply eq_true_iff_eq. rewrite eqb_eq. split.
destruct (eq_decidable n m) as [H|H]. trivial.
now rewrite (pow2_bits_false _ _ H).
intros EQ. rewrite EQ. apply pow2_bits_true; order.
Qed.

Lemma setbit_eqb : forall a n m, 0<=n ->
(setbit a n).[m] = eqb n m || a.[m].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.setbit_eqb".  
intros. now rewrite setbit_spec', lor_spec, pow2_bits_eqb, orb_comm.
Qed.

Lemma setbit_iff : forall a n m, 0<=n ->
((setbit a n).[m] = true <-> n==m \/ a.[m] = true).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.setbit_iff".  
intros. now rewrite setbit_eqb, orb_true_iff, eqb_eq.
Qed.

Lemma setbit_eq : forall a n, 0<=n -> (setbit a n).[n] = true.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.setbit_eq".  
intros. apply setbit_iff; trivial. now left.
Qed.

Lemma setbit_neq : forall a n m, 0<=n -> n~=m ->
(setbit a n).[m] = a.[m].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.setbit_neq".  
intros a n m Hn H. rewrite setbit_eqb; trivial.
rewrite <- eqb_eq in H. apply not_true_is_false in H. now rewrite H.
Qed.

Lemma clearbit_eqb : forall a n m,
(clearbit a n).[m] = a.[m] && negb (eqb n m).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.clearbit_eqb".  
intros.
destruct (le_gt_cases 0 m); [| now rewrite 2 testbit_neg_r].
rewrite clearbit_spec', ldiff_spec. f_equal. f_equal.
destruct (le_gt_cases 0 n) as [Hn|Hn].
now apply pow2_bits_eqb.
symmetry. rewrite pow_neg_r, bits_0, <- not_true_iff_false, eqb_eq; order.
Qed.

Lemma clearbit_iff : forall a n m,
(clearbit a n).[m] = true <-> a.[m] = true /\ n~=m.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.clearbit_iff".  
intros. rewrite clearbit_eqb, andb_true_iff, <- eqb_eq.
now rewrite negb_true_iff, not_true_iff_false.
Qed.

Lemma clearbit_eq : forall a n, (clearbit a n).[n] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.clearbit_eq".  
intros. rewrite clearbit_eqb, (proj2 (eqb_eq _ _) (eq_refl n)).
apply andb_false_r.
Qed.

Lemma clearbit_neq : forall a n m, n~=m ->
(clearbit a n).[m] = a.[m].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.clearbit_neq".  
intros a n m H. rewrite clearbit_eqb.
rewrite <- eqb_eq in H. apply not_true_is_false in H. rewrite H.
apply andb_true_r.
Qed.



Lemma shiftl_lxor : forall a b n,
(lxor a b) << n == lxor (a << n) (b << n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_lxor".  
intros. bitwise. now rewrite !shiftl_spec, lxor_spec.
Qed.

Lemma shiftr_lxor : forall a b n,
(lxor a b) >> n == lxor (a >> n) (b >> n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_lxor".  
intros. bitwise. now rewrite !shiftr_spec, lxor_spec.
Qed.

Lemma shiftl_land : forall a b n,
(land a b) << n == land (a << n) (b << n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_land".  
intros. bitwise. now rewrite !shiftl_spec, land_spec.
Qed.

Lemma shiftr_land : forall a b n,
(land a b) >> n == land (a >> n) (b >> n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_land".  
intros. bitwise. now rewrite !shiftr_spec, land_spec.
Qed.

Lemma shiftl_lor : forall a b n,
(lor a b) << n == lor (a << n) (b << n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_lor".  
intros. bitwise. now rewrite !shiftl_spec, lor_spec.
Qed.

Lemma shiftr_lor : forall a b n,
(lor a b) >> n == lor (a >> n) (b >> n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_lor".  
intros. bitwise. now rewrite !shiftr_spec, lor_spec.
Qed.

Lemma shiftl_ldiff : forall a b n,
(ldiff a b) << n == ldiff (a << n) (b << n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_ldiff".  
intros. bitwise. now rewrite !shiftl_spec, ldiff_spec.
Qed.

Lemma shiftr_ldiff : forall a b n,
(ldiff a b) >> n == ldiff (a >> n) (b >> n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_ldiff".  
intros. bitwise. now rewrite !shiftr_spec, ldiff_spec.
Qed.



Definition lnot a := P (-a).

Instance lnot_wd : Proper (eq==>eq) lnot.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_wd".   unfold lnot. solve_proper. Qed.

Lemma lnot_spec : forall a n, 0<=n -> (lnot a).[n] = negb a.[n].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_spec".  
intros. unfold lnot. rewrite <- (opp_involutive a) at 2.
rewrite bits_opp, negb_involutive; trivial.
Qed.

Lemma lnot_involutive : forall a, lnot (lnot a) == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_involutive".  
intros a. bitwise. now rewrite 2 lnot_spec, negb_involutive.
Qed.

Lemma lnot_0 : lnot 0 == -1.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_0".  
unfold lnot. now rewrite opp_0, <- sub_1_r, sub_0_l.
Qed.

Lemma lnot_m1 : lnot (-1) == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_m1".  
unfold lnot. now rewrite opp_involutive, one_succ, pred_succ.
Qed.



Lemma lor_m1_r : forall a, lor a (-1) == -1.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_m1_r".  
intros. bitwise. now rewrite bits_m1, orb_true_r.
Qed.

Lemma lor_m1_l : forall a, lor (-1) a == -1.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_m1_l".  
intros. now rewrite lor_comm, lor_m1_r.
Qed.

Lemma land_m1_r : forall a, land a (-1) == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_m1_r".  
intros. bitwise. now rewrite bits_m1, andb_true_r.
Qed.

Lemma land_m1_l : forall a, land (-1) a == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_m1_l".  
intros. now rewrite land_comm, land_m1_r.
Qed.

Lemma ldiff_m1_r : forall a, ldiff a (-1) == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_m1_r".  
intros. bitwise. now rewrite bits_m1, andb_false_r.
Qed.

Lemma ldiff_m1_l : forall a, ldiff (-1) a == lnot a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_m1_l".  
intros. bitwise. now rewrite lnot_spec, bits_m1.
Qed.

Lemma lor_lnot_diag : forall a, lor a (lnot a) == -1.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_lnot_diag".  
intros a. bitwise. rewrite lnot_spec, bits_m1; trivial.
now destruct a.[m].
Qed.

Lemma add_lnot_diag : forall a, a + lnot a == -1.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_lnot_diag".  
intros a. unfold lnot.
now rewrite add_pred_r, add_opp_r, sub_diag, one_succ, opp_succ, opp_0.
Qed.

Lemma ldiff_land : forall a b, ldiff a b == land a (lnot b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_land".  
intros. bitwise. now rewrite lnot_spec.
Qed.

Lemma land_lnot_diag : forall a, land a (lnot a) == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_lnot_diag".  
intros. now rewrite <- ldiff_land, ldiff_diag.
Qed.

Lemma lnot_lor : forall a b, lnot (lor a b) == land (lnot a) (lnot b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_lor".  
intros a b. bitwise. now rewrite !lnot_spec, lor_spec, negb_orb.
Qed.

Lemma lnot_land : forall a b, lnot (land a b) == lor (lnot a) (lnot b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_land".  
intros a b. bitwise. now rewrite !lnot_spec, land_spec, negb_andb.
Qed.

Lemma lnot_ldiff : forall a b, lnot (ldiff a b) == lor (lnot a) b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_ldiff".  
intros a b. bitwise.
now rewrite !lnot_spec, ldiff_spec, negb_andb, negb_involutive.
Qed.

Lemma lxor_lnot_lnot : forall a b, lxor (lnot a) (lnot b) == lxor a b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_lnot_lnot".  
intros a b. bitwise. now rewrite !lnot_spec, xorb_negb_negb.
Qed.

Lemma lnot_lxor_l : forall a b, lnot (lxor a b) == lxor (lnot a) b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_lxor_l".  
intros a b. bitwise. now rewrite !lnot_spec, !lxor_spec, negb_xorb_l.
Qed.

Lemma lnot_lxor_r : forall a b, lnot (lxor a b) == lxor a (lnot b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_lxor_r".  
intros a b. bitwise. now rewrite !lnot_spec, !lxor_spec, negb_xorb_r.
Qed.

Lemma lxor_m1_r : forall a, lxor a (-1) == lnot a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_m1_r".  
intros. now rewrite <- (lxor_0_r (lnot a)), <- lnot_m1, lxor_lnot_lnot.
Qed.

Lemma lxor_m1_l : forall a, lxor (-1) a == lnot a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_m1_l".  
intros. now rewrite lxor_comm, lxor_m1_r.
Qed.

Lemma lxor_lor : forall a b, land a b == 0 ->
lxor a b == lor a b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_lor".  
intros a b H. bitwise.
assert (a.[m] && b.[m] = false)
by now rewrite <- land_spec, H, bits_0.
now destruct a.[m], b.[m].
Qed.

Lemma lnot_shiftr : forall a n, 0<=n -> lnot (a >> n) == (lnot a) >> n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_shiftr".  
intros a n Hn. bitwise.
now rewrite lnot_spec, 2 shiftr_spec, lnot_spec by order_pos.
Qed.



Definition ones n := P (1<<n).

Instance ones_wd : Proper (eq==>eq) ones.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_wd".   unfold ones. solve_proper. Qed.

Lemma ones_equiv : forall n, ones n == P (2^n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_equiv".  
intros. unfold ones.
destruct (le_gt_cases 0 n).
now rewrite shiftl_mul_pow2, mul_1_l.
f_equiv. rewrite pow_neg_r; trivial.
rewrite <- shiftr_opp_r. apply shiftr_eq_0_iff. right; split.
order'. rewrite log2_1. now apply opp_pos_neg.
Qed.

Lemma ones_add : forall n m, 0<=n -> 0<=m ->
ones (m+n) == 2^m * ones n + ones m.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_add".  
intros n m Hn Hm. rewrite !ones_equiv.
rewrite <- !sub_1_r, mul_sub_distr_l, mul_1_r, <- pow_add_r by trivial.
rewrite add_sub_assoc, sub_add. reflexivity.
Qed.

Lemma ones_div_pow2 : forall n m, 0<=m<=n -> ones n / 2^m == ones (n-m).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_div_pow2".  
intros n m (Hm,H). symmetry. apply div_unique with (ones m).
left. rewrite ones_equiv. split.
rewrite <- lt_succ_r, succ_pred. order_pos.
now rewrite <- le_succ_l, succ_pred.
rewrite <- (sub_add m n) at 1. rewrite (add_comm _ m).
apply ones_add; trivial. now apply le_0_sub.
Qed.

Lemma ones_mod_pow2 : forall n m, 0<=m<=n -> (ones n) mod (2^m) == ones m.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_mod_pow2".  
intros n m (Hm,H). symmetry. apply mod_unique with (ones (n-m)).
left. rewrite ones_equiv. split.
rewrite <- lt_succ_r, succ_pred. order_pos.
now rewrite <- le_succ_l, succ_pred.
rewrite <- (sub_add m n) at 1. rewrite (add_comm _ m).
apply ones_add; trivial. now apply le_0_sub.
Qed.

Lemma ones_spec_low : forall n m, 0<=m<n -> (ones n).[m] = true.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_spec_low".  
intros n m (Hm,H). apply testbit_true; trivial.
rewrite ones_div_pow2 by (split; order).
rewrite <- (pow_1_r 2). rewrite ones_mod_pow2.
rewrite ones_equiv. now nzsimpl'.
split. order'. apply le_add_le_sub_r. nzsimpl. now apply le_succ_l.
Qed.

Lemma ones_spec_high : forall n m, 0<=n<=m -> (ones n).[m] = false.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_spec_high".  
intros n m (Hn,H). le_elim Hn.
apply bits_above_log2; rewrite ones_equiv.
rewrite <-lt_succ_r, succ_pred; order_pos.
rewrite log2_pred_pow2; trivial. now rewrite <-le_succ_l, succ_pred.
rewrite ones_equiv. now rewrite <- Hn, pow_0_r, one_succ, pred_succ, bits_0.
Qed.

Lemma ones_spec_iff : forall n m, 0<=n ->
((ones n).[m] = true <-> 0<=m<n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ones_spec_iff".  
intros n m Hn. split. intros H.
destruct (lt_ge_cases m 0) as [Hm|Hm].
now rewrite testbit_neg_r in H.
split; trivial. apply lt_nge. intro H'. rewrite ones_spec_high in H.
discriminate. now split.
apply ones_spec_low.
Qed.

Lemma lor_ones_low : forall a n, 0<=a -> log2 a < n ->
lor a (ones n) == ones n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_ones_low".  
intros a n Ha H. bitwise. destruct (le_gt_cases n m).
rewrite ones_spec_high, bits_above_log2; try split; trivial.
now apply lt_le_trans with n.
apply le_trans with (log2 a); order_pos.
rewrite ones_spec_low, orb_true_r; try split; trivial.
Qed.

Lemma land_ones : forall a n, 0<=n -> land a (ones n) == a mod 2^n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_ones".  
intros a n Hn. bitwise. destruct (le_gt_cases n m).
rewrite ones_spec_high, mod_pow2_bits_high, andb_false_r;
try split; trivial.
rewrite ones_spec_low, mod_pow2_bits_low, andb_true_r;
try split; trivial.
Qed.

Lemma land_ones_low : forall a n, 0<=a -> log2 a < n ->
land a (ones n) == a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_ones_low".  
intros a n Ha H.
assert (Hn : 0<=n) by (generalize (log2_nonneg a); order).
rewrite land_ones; trivial. apply mod_small.
split; trivial.
apply log2_lt_cancel. now rewrite log2_pow2.
Qed.

Lemma ldiff_ones_r : forall a n, 0<=n ->
ldiff a (ones n) == (a >> n) << n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_ones_r".  
intros a n Hn. bitwise. destruct (le_gt_cases n m).
rewrite ones_spec_high, shiftl_spec_high, shiftr_spec; trivial.
rewrite sub_add; trivial. apply andb_true_r.
now apply le_0_sub.
now split.
rewrite ones_spec_low, shiftl_spec_low, andb_false_r;
try split; trivial.
Qed.

Lemma ldiff_ones_r_low : forall a n, 0<=a -> log2 a < n ->
ldiff a (ones n) == 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_ones_r_low".  
intros a n Ha H. bitwise. destruct (le_gt_cases n m).
rewrite ones_spec_high, bits_above_log2; trivial.
now apply lt_le_trans with n.
split; trivial. now apply le_trans with (log2 a); order_pos.
rewrite ones_spec_low, andb_false_r; try split; trivial.
Qed.

Lemma ldiff_ones_l_low : forall a n, 0<=a -> log2 a < n ->
ldiff (ones n) a == lxor a (ones n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_ones_l_low".  
intros a n Ha H. bitwise. destruct (le_gt_cases n m).
rewrite ones_spec_high, bits_above_log2; trivial.
now apply lt_le_trans with n.
split; trivial. now apply le_trans with (log2 a); order_pos.
rewrite ones_spec_low, xorb_true_r; try split; trivial.
Qed.



Lemma shiftl_nonneg : forall a n, 0 <= (a << n) <-> 0 <= a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_nonneg".  
intros a n.
destruct (le_ge_cases 0 n) as [Hn|Hn].

rewrite 2 bits_iff_nonneg_ex. split; intros (k,Hk).
exists (k-n). intros m Hm.
destruct (le_gt_cases 0 m); [|now rewrite testbit_neg_r].
rewrite <- (add_simpl_r m n), <- (shiftl_spec a n) by order_pos.
apply Hk. now apply lt_sub_lt_add_r.
exists (k+n). intros m Hm.
destruct (le_gt_cases 0 m); [|now rewrite testbit_neg_r].
rewrite shiftl_spec by trivial. apply Hk. now apply lt_add_lt_sub_r.

rewrite <- shiftr_opp_r, 2 bits_iff_nonneg_ex. split; intros (k,Hk).
destruct (le_gt_cases 0 k).
exists (k-n). intros m Hm. apply lt_sub_lt_add_r in Hm.
rewrite <- (add_simpl_r m n), <- add_opp_r, <- (shiftr_spec a (-n)).
now apply Hk. order.
assert (EQ : a >> (-n) == 0).
apply bits_inj'. intros m Hm. rewrite bits_0. apply Hk; order.
apply shiftr_eq_0_iff in EQ.
rewrite <- bits_iff_nonneg_ex. destruct EQ as [EQ|[LT _]]; order.
exists (k+n). intros m Hm.
destruct (le_gt_cases 0 m); [|now rewrite testbit_neg_r].
rewrite shiftr_spec by trivial. apply Hk.
rewrite add_opp_r. now apply lt_add_lt_sub_r.
Qed.

Lemma shiftl_neg : forall a n, (a << n) < 0 <-> a < 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftl_neg".  
intros a n. now rewrite 2 lt_nge, shiftl_nonneg.
Qed.

Lemma shiftr_nonneg : forall a n, 0 <= (a >> n) <-> 0 <= a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_nonneg".  
intros. rewrite <- shiftl_opp_r. apply shiftl_nonneg.
Qed.

Lemma shiftr_neg : forall a n, (a >> n) < 0 <-> a < 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.shiftr_neg".  
intros a n. now rewrite 2 lt_nge, shiftr_nonneg.
Qed.

Lemma div2_nonneg : forall a, 0 <= div2 a <-> 0 <= a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.div2_nonneg".  
intros. rewrite div2_spec. apply shiftr_nonneg.
Qed.

Lemma div2_neg : forall a, div2 a < 0 <-> a < 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.div2_neg".  
intros a. now rewrite 2 lt_nge, div2_nonneg.
Qed.

Lemma lor_nonneg : forall a b, 0 <= lor a b <-> 0<=a /\ 0<=b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_nonneg".  
intros a b.
rewrite 3 bits_iff_nonneg_ex. split. intros (k,Hk).
split; exists k; intros m Hm; apply (orb_false_elim a.[m] b.[m]);
rewrite <- lor_spec; now apply Hk.
intros ((k,Hk),(k',Hk')).
destruct (le_ge_cases k k'); [ exists k' | exists k ];
intros m Hm; rewrite lor_spec, Hk, Hk'; trivial; order.
Qed.

Lemma lor_neg : forall a b, lor a b < 0 <-> a < 0 \/ b < 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lor_neg".  
intros a b. rewrite 3 lt_nge, lor_nonneg. split.
apply not_and. apply le_decidable.
now intros [H|H] (H',H'').
Qed.

Lemma lnot_nonneg : forall a, 0 <= lnot a <-> a < 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_nonneg".  
intros a; unfold lnot.
now rewrite <- opp_succ, opp_nonneg_nonpos, le_succ_l.
Qed.

Lemma lnot_neg : forall a, lnot a < 0 <-> 0 <= a.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lnot_neg".  
intros a. now rewrite le_ngt, lt_nge, lnot_nonneg.
Qed.

Lemma land_nonneg : forall a b, 0 <= land a b <-> 0<=a \/ 0<=b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_nonneg".  
intros a b.
now rewrite <- (lnot_involutive (land a b)), lnot_land, lnot_nonneg,
lor_neg, !lnot_neg.
Qed.

Lemma land_neg : forall a b, land a b < 0 <-> a < 0 /\ b < 0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.land_neg".  
intros a b.
now rewrite <- (lnot_involutive (land a b)), lnot_land, lnot_neg,
lor_nonneg, !lnot_nonneg.
Qed.

Lemma ldiff_nonneg : forall a b, 0 <= ldiff a b <-> 0<=a \/ b<0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_nonneg".  
intros. now rewrite ldiff_land, land_nonneg, lnot_nonneg.
Qed.

Lemma ldiff_neg : forall a b, ldiff a b < 0 <-> a<0 /\ 0<=b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_neg".  
intros. now rewrite ldiff_land, land_neg, lnot_neg.
Qed.

Lemma lxor_nonneg : forall a b, 0 <= lxor a b <-> (0<=a <-> 0<=b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.lxor_nonneg".  
assert (H : forall a b, 0<=a -> 0<=b -> 0<=lxor a b).
intros a b. rewrite 3 bits_iff_nonneg_ex. intros (k,Hk) (k', Hk').
destruct (le_ge_cases k k'); [ exists k' | exists k];
intros m Hm; rewrite lxor_spec, Hk, Hk'; trivial; order.
assert (H' : forall a b, 0<=a -> b<0 -> lxor a b<0).
intros a b. rewrite bits_iff_nonneg_ex, 2 bits_iff_neg_ex.
intros (k,Hk) (k', Hk').
destruct (le_ge_cases k k'); [ exists k' | exists k];
intros m Hm; rewrite lxor_spec, Hk, Hk'; trivial; order.
intros a b.
split.
intros Hab. split.
intros Ha. destruct (le_gt_cases 0 b) as [Hb|Hb]; trivial.
generalize (H' _ _ Ha Hb). order.
intros Hb. destruct (le_gt_cases 0 a) as [Ha|Ha]; trivial.
generalize (H' _ _ Hb Ha). rewrite lxor_comm. order.
intros E.
destruct (le_gt_cases 0 a) as [Ha|Ha]. apply H; trivial. apply E; trivial.
destruct (le_gt_cases 0 b) as [Hb|Hb]. apply H; trivial. apply E; trivial.
rewrite <- lxor_lnot_lnot. apply H; now apply lnot_nonneg.
Qed.



Lemma log2_bits_unique : forall a n,
a.[n] = true ->
(forall m, n<m -> a.[m] = false) ->
log2 a == n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.log2_bits_unique".  
intros a n H H'.
destruct (lt_trichotomy a 0) as [Ha|[Ha|Ha]].

destruct (proj1 (bits_iff_neg_ex a) Ha) as (k,Hk).
destruct (le_gt_cases n k).
specialize (Hk (S k) (lt_succ_diag_r _)).
rewrite H' in Hk. discriminate. apply lt_succ_r; order.
specialize (H' (S n) (lt_succ_diag_r _)).
rewrite Hk in H'. discriminate. apply lt_succ_r; order.

now rewrite Ha, bits_0 in H.

apply le_antisymm; apply le_ngt; intros LT.
specialize (H' _ LT). now rewrite bit_log2 in H'.
now rewrite bits_above_log2 in H by order.
Qed.

Lemma log2_shiftr : forall a n, 0<a -> log2 (a >> n) == max 0 (log2 a - n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.log2_shiftr".  
intros a n Ha.
destruct (le_gt_cases 0 (log2 a - n));
[rewrite max_r | rewrite max_l]; try order.
apply log2_bits_unique.
now rewrite shiftr_spec, sub_add, bit_log2.
intros m Hm.
destruct (le_gt_cases 0 m); [|now rewrite testbit_neg_r].
rewrite shiftr_spec; trivial. apply bits_above_log2; try order.
now apply lt_sub_lt_add_r.
rewrite lt_sub_lt_add_r, add_0_l in H.
apply log2_nonpos. apply le_lteq; right.
apply shiftr_eq_0_iff. right. now split.
Qed.

Lemma log2_shiftl : forall a n, 0<a -> 0<=n -> log2 (a << n) == log2 a + n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.log2_shiftl".  
intros a n Ha Hn.
rewrite shiftl_mul_pow2, add_comm by trivial.
now apply log2_mul_pow2.
Qed.

Lemma log2_shiftl' : forall a n, 0<a -> log2 (a << n) == max 0 (log2 a + n).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.log2_shiftl'".  
intros a n Ha.
rewrite <- shiftr_opp_r, log2_shiftr by trivial.
destruct (le_gt_cases 0 (log2 a + n));
[rewrite 2 max_r | rewrite 2 max_l]; rewrite ?sub_opp_r; try order.
Qed.

Lemma log2_lor : forall a b, 0<=a -> 0<=b ->
log2 (lor a b) == max (log2 a) (log2 b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.log2_lor".  
assert (AUX : forall a b, 0<=a -> a<=b -> log2 (lor a b) == log2 b).
intros a b Ha H.
le_elim Ha; [|now rewrite <- Ha, lor_0_l].
apply log2_bits_unique.
now rewrite lor_spec, bit_log2, orb_true_r by order.
intros m Hm. assert (H' := log2_le_mono _ _ H).
now rewrite lor_spec, 2 bits_above_log2 by order.

intros a b Ha Hb. destruct (le_ge_cases a b) as [H|H].
rewrite max_r by now apply log2_le_mono.
now apply AUX.
rewrite max_l by now apply log2_le_mono.
rewrite lor_comm. now apply AUX.
Qed.

Lemma log2_land : forall a b, 0<=a -> 0<=b ->
log2 (land a b) <= min (log2 a) (log2 b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.log2_land".  
assert (AUX : forall a b, 0<=a -> a<=b -> log2 (land a b) <= log2 a).
intros a b Ha Hb.
apply le_ngt. intros LT.
assert (H : 0 <= land a b) by (apply land_nonneg; now left).
le_elim H.
generalize (bit_log2 (land a b) H).
now rewrite land_spec, bits_above_log2.
rewrite <- H in LT. apply log2_lt_cancel in LT; order.

intros a b Ha Hb.
destruct (le_ge_cases a b) as [H|H].
rewrite min_l by now apply log2_le_mono. now apply AUX.
rewrite min_r by now apply log2_le_mono. rewrite land_comm. now apply AUX.
Qed.

Lemma log2_lxor : forall a b, 0<=a -> 0<=b ->
log2 (lxor a b) <= max (log2 a) (log2 b).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.log2_lxor".  
assert (AUX : forall a b, 0<=a -> a<=b -> log2 (lxor a b) <= log2 b).
intros a b Ha Hb.
apply le_ngt. intros LT.
assert (H : 0 <= lxor a b) by (apply lxor_nonneg; split; order).
le_elim H.
generalize (bit_log2 (lxor a b) H).
rewrite lxor_spec, 2 bits_above_log2; try order. discriminate.
apply le_lt_trans with (log2 b); trivial. now apply log2_le_mono.
rewrite <- H in LT. apply log2_lt_cancel in LT; order.

intros a b Ha Hb.
destruct (le_ge_cases a b) as [H|H].
rewrite max_r by now apply log2_le_mono. now apply AUX.
rewrite max_l by now apply log2_le_mono. rewrite lxor_comm. now apply AUX.
Qed.



Local Notation xor3 a b c := (xorb (xorb a b) c).
Local Notation lxor3 a b c := (lxor (lxor a b) c).
Local Notation nextcarry a b c := ((a&&b) || (c && (a||b))).
Local Notation lnextcarry a b c := (lor (land a b) (land c (lor a b))).

Lemma add_bit0 : forall a b, (a+b).[0] = xorb a.[0] b.[0].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_bit0".  
intros. now rewrite !bit0_odd, odd_add.
Qed.

Lemma add3_bit0 : forall a b c,
(a+b+c).[0] = xor3 a.[0] b.[0] c.[0].
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add3_bit0".  
intros. now rewrite !add_bit0.
Qed.

Lemma add3_bits_div2 : forall (a0 b0 c0 : bool),
(a0 + b0 + c0)/2 == nextcarry a0 b0 c0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add3_bits_div2".  
assert (H : 1+1 == 2) by now nzsimpl'.
intros [|] [|] [|]; simpl; rewrite ?add_0_l, ?add_0_r, ?H;
(apply div_same; order') || (apply div_small; split; order') || idtac.
symmetry. apply div_unique with 1. left; split; order'. now nzsimpl'.
Qed.

Lemma add_carry_div2 : forall a b (c0:bool),
(a + b + c0)/2 == a/2 + b/2 + nextcarry a.[0] b.[0] c0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_carry_div2".  
intros.
rewrite <- add3_bits_div2.
rewrite (add_comm ((a/2)+_)).
rewrite <- div_add by order'.
f_equiv.
rewrite <- !div2_div, mul_comm, mul_add_distr_l.
rewrite (div2_odd a), <- bit0_odd at 1.
rewrite (div2_odd b), <- bit0_odd at 1.
rewrite add_shuffle1.
rewrite <-(add_assoc _ _ c0). apply add_comm.
Qed.



Lemma add_carry_bits_aux : forall n, 0<=n ->
forall a b (c0:bool), -(2^n) <= a < 2^n -> -(2^n) <= b < 2^n ->
exists c,
a+b+c0 == lxor3 a b c /\ c/2 == lnextcarry a b c /\ c.[0] = c0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_carry_bits_aux".  
intros n Hn. apply le_ind with (4:=Hn).
solve_proper.

intros a b c0. rewrite !pow_0_r, !one_succ, !lt_succ_r, <- !one_succ.
intros (Ha1,Ha2) (Hb1,Hb2).
le_elim Ha1; rewrite <- ?le_succ_l, ?succ_m1 in Ha1;
le_elim Hb1; rewrite <- ?le_succ_l, ?succ_m1 in Hb1.

exists c0.
rewrite (le_antisymm _ _ Ha2 Ha1), (le_antisymm _ _ Hb2 Hb1).
rewrite !add_0_l, !lxor_0_l, !lor_0_r, !land_0_r, !lor_0_r.
rewrite b2z_div2, b2z_bit0; now repeat split.

exists (-c0). rewrite <- Hb1, (le_antisymm _ _ Ha2 Ha1). repeat split.
rewrite add_0_l, lxor_0_l, lxor_m1_l.
unfold lnot. now rewrite opp_involutive, add_comm, add_opp_r, sub_1_r.
rewrite land_0_l, !lor_0_l, land_m1_r.
symmetry. apply div_unique with c0. left; destruct c0; simpl; split; order'.
now rewrite two_succ, mul_succ_l, mul_1_l, add_opp_r, sub_add.
rewrite bit0_odd, odd_opp; destruct c0; simpl; apply odd_1 || apply odd_0.

exists (-c0). rewrite <- Ha1, (le_antisymm _ _ Hb2 Hb1). repeat split.
rewrite add_0_r, lxor_0_r, lxor_m1_l.
unfold lnot. now rewrite opp_involutive, add_comm, add_opp_r, sub_1_r.
rewrite land_0_r, lor_0_r, lor_0_l, land_m1_r.
symmetry. apply div_unique with c0. left; destruct c0; simpl; split; order'.
now rewrite two_succ, mul_succ_l, mul_1_l, add_opp_r, sub_add.
rewrite bit0_odd, odd_opp; destruct c0; simpl; apply odd_1 || apply odd_0.

exists (c0 + 2*(-1)). rewrite <- Ha1, <- Hb1. repeat split.
rewrite lxor_m1_l, lnot_m1, lxor_0_l.
now rewrite two_succ, mul_succ_l, mul_1_l, add_comm, add_assoc.
rewrite land_m1_l, lor_m1_l.
apply add_b2z_double_div2.
apply add_b2z_double_bit0.

clear n Hn. intros n Hn IH a b c0 Ha Hb.
set (c1:=nextcarry a.[0] b.[0] c0).
destruct (IH (a/2) (b/2) c1) as (c & IH1 & IH2 & Hc); clear IH.
split.
apply div_le_lower_bound. order'. now rewrite mul_opp_r, <- pow_succ_r.
apply div_lt_upper_bound. order'. now rewrite <- pow_succ_r.
split.
apply div_le_lower_bound. order'. now rewrite mul_opp_r, <- pow_succ_r.
apply div_lt_upper_bound. order'. now rewrite <- pow_succ_r.
exists (c0 + 2*c). repeat split.

bitwise.
le_elim Hm.
rewrite <- (succ_pred m), lt_succ_r in Hm.
rewrite <- (succ_pred m), <- !div2_bits, <- 2 lxor_spec by trivial.
f_equiv.
rewrite add_b2z_double_div2, <- IH1. apply add_carry_div2.
rewrite <- Hm.
now rewrite add_b2z_double_bit0, add3_bit0, b2z_bit0.

rewrite add_b2z_double_div2.
bitwise.
le_elim Hm.
rewrite <- (succ_pred m), lt_succ_r in Hm.
rewrite <- (succ_pred m), <- !div2_bits, IH2 by trivial.
autorewrite with bitwise. now rewrite add_b2z_double_div2.
rewrite <- Hm.
now rewrite add_b2z_double_bit0.

apply add_b2z_double_bit0.
Qed.

Lemma add_carry_bits : forall a b (c0:bool), exists c,
a+b+c0 == lxor3 a b c /\ c/2 == lnextcarry a b c /\ c.[0] = c0.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_carry_bits".  
intros a b c0.
set (n := max (abs a) (abs b)).
apply (add_carry_bits_aux n).

unfold n.
destruct (le_ge_cases (abs a) (abs b));
[rewrite max_r|rewrite max_l]; order_pos'.

assert (Ha : abs a < 2^n).
apply lt_le_trans with (2^(abs a)). apply pow_gt_lin_r; order_pos'.
apply pow_le_mono_r. order'. unfold n.
destruct (le_ge_cases (abs a) (abs b));
[rewrite max_r|rewrite max_l]; try order.
apply abs_lt in Ha. destruct Ha; split; order.

assert (Hb : abs b < 2^n).
apply lt_le_trans with (2^(abs b)). apply pow_gt_lin_r; order_pos'.
apply pow_le_mono_r. order'. unfold n.
destruct (le_ge_cases (abs a) (abs b));
[rewrite max_r|rewrite max_l]; try order.
apply abs_lt in Hb. destruct Hb; split; order.
Qed.



Lemma add_bit1 : forall a b,
(a+b).[1] = xor3 a.[1] b.[1] (a.[0] && b.[0]).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_bit1".  
intros a b.
destruct (add_carry_bits a b false) as (c & EQ1 & EQ2 & Hc).
simpl in EQ1; rewrite add_0_r in EQ1. rewrite EQ1.
autorewrite with bitwise. f_equal.
rewrite one_succ, <- div2_bits, EQ2 by order.
autorewrite with bitwise.
rewrite Hc. simpl. apply orb_false_r.
Qed.



Lemma nocarry_equiv : forall a b c,
c/2 == lnextcarry a b c -> c.[0] = false ->
(c == 0 <-> land a b == 0).
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.nocarry_equiv".  
intros a b c H H'.
split. intros EQ; rewrite EQ in *.
rewrite div_0_l in H by order'.
symmetry in H. now apply lor_eq_0_l in H.
intros EQ. rewrite EQ, lor_0_l in H.
apply bits_inj'. intros n Hn. rewrite bits_0.
apply le_ind with (4:=Hn).
solve_proper.
trivial.
clear n Hn. intros n Hn IH.
rewrite <- div2_bits, H; trivial.
autorewrite with bitwise.
now rewrite IH.
Qed.



Lemma add_nocarry_lxor : forall a b, land a b == 0 ->
a+b == lxor a b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_nocarry_lxor".  
intros a b H.
destruct (add_carry_bits a b false) as (c & EQ1 & EQ2 & Hc).
simpl in EQ1; rewrite add_0_r in EQ1. rewrite EQ1.
apply (nocarry_equiv a b c) in H; trivial.
rewrite H. now rewrite lxor_0_r.
Qed.



Lemma ldiff_le : forall a b, 0<=b -> ldiff a b == 0 -> 0 <= a <= b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.ldiff_le".  
assert (AUX : forall n, 0<=n ->
forall a b, 0 <= a < 2^n -> 0<=b -> ldiff a b == 0 -> a <= b).
intros n Hn. apply le_ind with (4:=Hn); clear n Hn.
solve_proper.
intros a b Ha Hb _. rewrite pow_0_r, one_succ, lt_succ_r in Ha.
setoid_replace a with 0 by (destruct Ha; order'); trivial.
intros n Hn IH a b (Ha,Ha') Hb H.
assert (NEQ : 2 ~= 0) by order'.
rewrite (div_mod a 2 NEQ), (div_mod b 2 NEQ).
apply add_le_mono.
apply mul_le_mono_pos_l; try order'.
apply IH.
split. apply div_pos; order'.
apply div_lt_upper_bound; try order'. now rewrite <- pow_succ_r.
apply div_pos; order'.
rewrite <- (pow_1_r 2), <- 2 shiftr_div_pow2 by order'.
rewrite <- shiftr_ldiff, H, shiftr_div_pow2, pow_1_r, div_0_l; order'.
rewrite <- 2 bit0_mod.
apply bits_inj_iff in H. specialize (H 0).
rewrite ldiff_spec, bits_0 in H.
destruct a.[0], b.[0]; try discriminate; simpl; order'.

intros a b Hb Hd.
assert (Ha : 0<=a).
apply le_ngt; intros Ha'. apply (lt_irrefl 0). rewrite <- Hd at 1.
apply ldiff_neg. now split.
split; trivial. apply (AUX a); try split; trivial. apply pow_gt_lin_r; order'.
Qed.



Lemma sub_nocarry_ldiff : forall a b, ldiff b a == 0 ->
a-b == ldiff a b.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.sub_nocarry_ldiff".  
intros a b H.
apply add_cancel_r with b.
rewrite sub_add.
symmetry.
rewrite add_nocarry_lxor; trivial.
bitwise.
apply bits_inj_iff in H. specialize (H m).
rewrite ldiff_spec, bits_0 in H.
now destruct a.[m], b.[m].
apply land_ldiff.
Qed.



Lemma add_nocarry_lt_pow2 : forall a b n, land a b == 0 ->
a < 2^n -> b < 2^n -> a+b < 2^n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_nocarry_lt_pow2".  
intros a b n H Ha Hb.
destruct (le_gt_cases a 0) as [Ha'|Ha'].
apply le_lt_trans with (0+b). now apply add_le_mono_r. now nzsimpl.
destruct (le_gt_cases b 0) as [Hb'|Hb'].
apply le_lt_trans with (a+0). now apply add_le_mono_l. now nzsimpl.
rewrite add_nocarry_lxor by order.
destruct (lt_ge_cases 0 (lxor a b)); [|apply le_lt_trans with 0; order_pos].
apply log2_lt_pow2; trivial.
apply log2_lt_pow2 in Ha; trivial.
apply log2_lt_pow2 in Hb; trivial.
apply le_lt_trans with (max (log2 a) (log2 b)).
apply log2_lxor; order.
destruct (le_ge_cases (log2 a) (log2 b));
[rewrite max_r|rewrite max_l]; order.
Qed.

Lemma add_nocarry_mod_lt_pow2 : forall a b n, 0<=n -> land a b == 0 ->
a mod 2^n + b mod 2^n < 2^n.
Proof. hammer_hook "ZBits" "ZBits.ZBitsProp.add_nocarry_mod_lt_pow2".  
intros a b n Hn H.
apply add_nocarry_lt_pow2.
bitwise.
destruct (le_gt_cases n m).
rewrite mod_pow2_bits_high; now split.
now rewrite !mod_pow2_bits_low, <- land_spec, H, bits_0.
apply mod_pos_bound; order_pos.
apply mod_pos_bound; order_pos.
Qed.

End ZBitsProp.
