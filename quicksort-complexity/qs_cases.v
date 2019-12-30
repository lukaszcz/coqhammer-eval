From Hammer Require Import Hammer.

Set Implicit Arguments.

From QuicksortComplexity Require Import util.
Require Import Le.
Require Import Plus.
Require Import Minus.
Require Import Lt.
Require Import Arith.
Require Import Recdef.
Require Import Bool_nat.
Require Import List.
From QuicksortComplexity Require Import monads.
Require Import Relation_Definitions.
From QuicksortComplexity Require Import monoid_monad_trans.
From QuicksortComplexity Require Import expec.
From QuicksortComplexity Require Import monoid_expec.
From QuicksortComplexity Require Import nat_seqs.
From QuicksortComplexity Require Import list_utils.
From QuicksortComplexity Require Import sums_and_averages.
From QuicksortComplexity Require qs_definitions.
From QuicksortComplexity Require qs_parts.
From QuicksortComplexity Require U.
From QuicksortComplexity Require Import sort_order.
From QuicksortComplexity Require Import indices.
From QuicksortComplexity Require Import qs_sound_cmps.
Require Import Fourier.
Require Import Rbase.
From QuicksortComplexity Require Import skip_list.
From QuicksortComplexity Require Import nat_below.
Require Vector.

Import qs_definitions.mon_nondet.

Section contents.

Variables (ee: E) (ol: list ee) (i j: Index ee ol).

Variable n: nat.
Variable v: Vector.t (Index ee ol) (S n).
Variable iltj: (i < j)%nat.

Let flt x0 cr := filter (fun f: Index ee ol => unsum_bool (cmp_cmp (Ecmp (UE ee ol) f (vec.nth v x0)) cr)) (vec.to_list (vec.remove v x0)).

Variable IH: forall (x0: natBelow (S n)) (cr: comparison) (b: nat),
IndexSeq b (flt x0 cr) ->
monoid_expec (U.ijcount i j) (qs (U.cmp (e:=ee) (ol:=ol)) U.pick (flt x0 cr)) <= 2 / INR (S (j - i)).

Variables (b: nat) (is: IndexSeq b (vec.to_list v)).

Lemma ndi: NoDup (vec.to_list v).
apply IndexSeq_NoDup with b.
assumption.
Qed.

Variable iin: In i (vec.to_list v).
Variable jin: In j (vec.to_list v).
Variable pi: natBelow (S n).

Lemma not_In_flt (k: Index ee ol) (dr: comparison) (H0: dr <> Ecmp (UE ee ol) k (vec.nth v pi)):
~ In k (flt pi dr).
Proof with auto. hammer_hook "qs_cases" "qs_cases.not_In_flt".
unfold flt.
intros.
intro.
destruct (proj1_conj (filter_In _ _ _) H). clear H.
simpl in H0.
simpl in H2.
destruct (Ecmp ee (subscript k) (subscript (vec.nth v pi))); destruct dr; auto; simpl in H2; try discriminate...
Qed.

Lemma ndi_flt: forall x0 cr, NoDup (flt x0 cr).
Proof. hammer_hook "qs_cases" "qs_cases.ndi_flt".
unfold flt.
intros.
apply NoDup_filter.
apply (NoDup_SkipList ndi).
cset (vec.SkipList_remove x0 v).
assumption.
Qed.

Hint Immediate ndi_flt.

Lemma partition_0: nb_val (vec.nth v pi) <> i -> nb_val (vec.nth v pi) <> j ->
U.ijcount i j (map (fun i0: Index ee ol => U.unordered_nat_pair i0 (vec.nth v pi)) (vec.to_list (vec.remove v pi))) = 0%nat.
Proof. hammer_hook "qs_cases" "qs_cases.partition_0".
intros.
apply (U.ijcount_0).
intro.
destruct (In_map_inv H1). clear H1.
destruct H2.
unfold U.unordered_nat_pair in H1.
destruct (le_lt_dec x (vec.nth v pi)); inversion H1; auto.
Qed.

Hint Immediate U.hom_ijcount.
Hint Immediate vec.remove_perm.

Lemma pivot_not_In_flt cr: ~ In (vec.nth v pi) (flt pi cr).
Proof with auto. hammer_hook "qs_cases" "qs_cases.pivot_not_In_flt".
intros H.
pose proof ndi as H0.
rewrite (Permutation.Permutation_sym (vec.List_Permutation (vec.remove_perm pi v))) in H0.
inversion_clear H0...
destruct (In_filter_inv _ _ _ H)...
Qed.

Lemma NoDup_comparisons (x: Index ee ol) (l: list (Index ee ol)):
NoDup (x :: l) -> NoDup (map (fun i: Index ee ol => U.unordered_nat_pair i x) l).
Proof with auto. hammer_hook "qs_cases" "qs_cases.NoDup_comparisons".
intros.
inversion_clear H.
apply NoDup_map'...
intros.
unfold U.unordered_nat_pair.
intro.
apply H3.
unfold Index in *.
apply natBelow_unique.
destruct (le_lt_dec x0 x); destruct (le_lt_dec y x); inversion H4; reflexivity.
Qed.

Lemma case_A: (vec.nth v pi < i)%nat ->
INR (U.ijcount i j (map (fun i0: Index ee ol => U.unordered_nat_pair i0 (vec.nth v pi)) (vec.to_list (vec.remove v pi)))) +
monoid_expec (U.ijcount i j)
(foo <- @U.qs ee ol (flt pi Lt);
bar <- @U.qs ee ol (flt pi Gt);
ret  (foo ++ (vec.nth v pi :: flt pi Eq) ++ bar))
<= 2 * / INR (S (j - i)).
Proof with auto with real. hammer_hook "qs_cases" "qs_cases.case_A".
intros.
rewrite partition_0...
Focus 2.
intro.
rewrite H0 in H.
apply (lt_asym _ _ H iltj).
rewrite Rplus_0_l.
rewrite monoid_expec_plus... Focus 2. intros. repeat rewrite monoid_expec_plus...
rewrite monoid_expec_plus...
rewrite monoid_expec_ret...
rewrite Rplus_0_r.
rewrite sound_cmp_expec_0...
Focus 2.
left.
apply not_In_flt...
intro.
apply (lt_asym _ _ H).
symmetry in H0.
apply (IndicesCorrect _ _ H0).
rewrite Rplus_0_l.
case_eq (Ecmp ee (subscript i) (subscript (vec.nth v pi))); intro.

unfold Rdiv.
rewrite sound_cmp_expec_0...
left.
apply not_In_flt...
simpl.
simpl in H0.
rewrite H0. intro. discriminate.

elimtype False.
apply (lt_irrefl i).
apply lt_trans with (vec.nth v pi)...
apply (IndicesCorrect i (vec.nth v pi))...

assert (IndexSeq b (vec.nth v pi :: (vec.to_list (vec.remove v pi)))).
apply IndexSeq_perm with (vec.to_list v)...
cset (vec.List_Permutation (vec.remove_perm pi v))...
apply (IH _ Gt (@InvIndexSeq_filterGt' ee ol (vec.nth v pi) (vec.to_list (vec.remove v pi)) b H1))...
Qed.

Lemma case_E: (j < vec.nth v pi)%nat ->
INR (U.ijcount i j (map (fun i0: Index ee ol => U.unordered_nat_pair i0 (vec.nth v pi)) (vec.to_list (vec.remove v pi)))) +
monoid_expec (U.ijcount i j)
(foo <- @U.qs ee ol (flt pi Lt);
bar <- @U.qs ee ol (flt pi Gt);
ret (foo ++ (vec.nth v pi :: flt pi Eq) ++ bar))
<= 2 * / INR (S (j - i)).
Proof with auto with real. hammer_hook "qs_cases" "qs_cases.case_E".
intros.
rewrite partition_0...
Focus 2.
intro.
cset (natBelow_unique _ _ H0).
subst i.
apply (lt_asym _ _ H iltj).
rewrite Rplus_0_l.
rewrite monoid_expec_plus...
rewrite monoid_expec_plus...
rewrite monoid_expec_ret...
rewrite Rplus_0_r.
rewrite (@sound_cmp_expec_0 ee ol i j (flt pi Gt))...
Focus 2.
right.
apply not_In_flt.
intro.
apply (lt_asym _ _ H).
cset (Ecmp_sym ee (subscript (vec.nth v pi)) (subscript j)).
simpl in H0.
simpl in H1.
rewrite <- H0 in H1.
simpl in H1.
apply (IndicesCorrect _ _ H1).
rewrite Rplus_0_r.
case_eq (Ecmp ee (subscript j) (subscript (vec.nth v pi))); intro.

unfold Rdiv.
rewrite sound_cmp_expec_0...
right.
apply not_In_flt...
simpl.
simpl in H0. simpl.
rewrite H0. intro. discriminate.
Focus 2.

elimtype False.
cset (Ecmp_sym ee (subscript (vec.nth v pi)) (subscript j)).
rewrite H0 in H1.
simpl in H1.
apply (lt_asym _ _ H).
apply (IndicesCorrect _ _ H1)...

apply IH with b...
unfold flt.
assert (length (vec.nth v pi :: (vec.to_list (vec.remove v pi))) = S n).
simpl @length. rewrite vec.length...
assert (IndexSeq b (vec.nth v pi :: (vec.to_list (vec.remove v pi)))).
apply IndexSeq_perm with (vec.to_list v)...
apply (vec.List_Permutation (vec.remove_perm pi v)).
cset (@IndexSeq_filterLt ee ol (vec.nth v pi) (S n) b (vec.nth v pi :: (vec.to_list (vec.remove v pi))) H1 H2).
simpl filter in H3.
rewrite Ecmp_refl in H3...
intros.
repeat rewrite monoid_expec_plus...
Qed.

Lemma case_C: (i < vec.nth v pi)%nat -> (vec.nth v pi < j)%nat ->
INR (U.ijcount i j (map (fun i0: Index ee ol => U.unordered_nat_pair i0 (vec.nth v pi)) (vec.to_list (vec.remove v pi)))) +
monoid_expec (U.ijcount i j)
(foo <- @U.qs ee ol (flt pi Lt);
bar <- @U.qs ee ol (flt pi Gt);
ret (foo ++ (vec.nth v pi :: flt pi Eq) ++ bar))
= 0.
Proof with auto with real. hammer_hook "qs_cases" "qs_cases.case_C".
intros.
rewrite partition_0...
rewrite Rplus_0_l.
unfold U.M.
rewrite monoid_expec_bind_0_r...
apply sound_cmp_expec_0...
right.
apply not_In_flt.
intro.
apply (lt_asym _ _ H0).
symmetry in H1.
apply (IndicesCorrect _ _ H1).
intros.
rewrite monoid_expec_plus...
rewrite (monoid_expec_ret (U.hom_ijcount i j)).
rewrite Rplus_0_r.
apply sound_cmp_expec_0...
left.
apply not_In_flt.
intro.
cset (Ecmp_sym ee (subscript (vec.nth v pi)) (subscript i)).
simpl in H1. simpl in H2.
rewrite <- H1 in H2.
simpl in H2.
apply (lt_asym _ _ H).
apply (IndicesCorrect _ _ H2).
Qed.

Lemma case_BD: (i = vec.nth v pi \/ j = vec.nth v pi) ->
INR (U.ijcount i j (map (fun i0: Index ee ol => U.unordered_nat_pair i0 (vec.nth v pi)) (vec.to_list (vec.remove v pi)))) +
monoid_expec (U.ijcount i j)
(foo <- @U.qs ee ol (flt pi Lt);
bar <- @U.qs ee ol (flt pi Gt);
ret (foo ++ (vec.nth v pi :: flt pi Eq) ++ bar))
<= 1.
Proof with auto with real. hammer_hook "qs_cases" "qs_cases.case_BD".
intros.
rewrite (monoid_expec_bind_0_r (U.hom_ijcount i j)).
rewrite sound_cmp_expec_0...
rewrite Rplus_0_r.
rewrite U.ijcount_eq_count.
replace 1 with (INR 1)...
apply le_INR.
apply eq_count_NoDup.
apply NoDup_comparisons.
rewrite (vec.List_Permutation (vec.remove_perm pi v)).
apply IndexSeq_NoDup with b...
destruct H; subst; [left | right]; apply pivot_not_In_flt.
intros.
unfold U.M.
rewrite monoid_expec_plus...
rewrite (monoid_expec_ret (U.hom_ijcount i j)).
rewrite sound_cmp_expec_0...
destruct H; subst; [left | right]; apply pivot_not_In_flt.
Qed.

End contents.
