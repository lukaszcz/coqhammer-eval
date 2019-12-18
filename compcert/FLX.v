From Hammer Require Import Hammer.




From compcert Require Import Raux.
From compcert Require Import Defs.
From compcert Require Import Round_pred.
From compcert Require Import Generic_fmt.
From compcert Require Import Float_prop.
From compcert Require Import FIX.
From compcert Require Import Ulp.
From compcert Require Import Round_NE.
Require Import Psatz.

Section RND_FLX.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Variable prec : Z.

Class Prec_gt_0 :=
prec_gt_0 : (0 < prec)%Z.

Context { prec_gt_0_ : Prec_gt_0 }.

Inductive FLX_format (x : R) : Prop :=
FLX_spec (f : float beta) :
x = F2R f -> (Z.abs (Fnum f) < Zpower beta prec)%Z -> FLX_format x.

Definition FLX_exp (e : Z) := (e - prec)%Z.



Global Instance FLX_exp_valid : Valid_exp FLX_exp.
Proof. hammer_hook "FLX" "FLX.FLX_exp_valid".
intros k.
unfold FLX_exp.
generalize prec_gt_0.
repeat split ; intros ; omega.
Qed.

Theorem FIX_format_FLX :
forall x e,
(bpow (e - 1) <= Rabs x <= bpow e)%R ->
FLX_format x ->
FIX_format beta (e - prec) x.
Proof. hammer_hook "FLX" "FLX.FIX_format_FLX".
clear prec_gt_0_.
intros x e Hx [[xm xe] H1 H2].
rewrite H1, (F2R_prec_normalize beta xm xe e prec).
now eexists.
exact H2.
now rewrite <- H1.
Qed.

Theorem FLX_format_generic :
forall x, generic_format beta FLX_exp x -> FLX_format x.
Proof. hammer_hook "FLX" "FLX.FLX_format_generic".
intros x H.
rewrite H.
eexists ; repeat split.
simpl.
apply lt_IZR.
rewrite abs_IZR.
rewrite <- scaled_mantissa_generic with (1 := H).
rewrite <- scaled_mantissa_abs.
apply Rmult_lt_reg_r with (bpow (cexp beta FLX_exp (Rabs x))).
apply bpow_gt_0.
rewrite scaled_mantissa_mult_bpow.
rewrite IZR_Zpower, <- bpow_plus.
2: now apply Zlt_le_weak.
unfold cexp, FLX_exp.
ring_simplify (prec + (mag beta (Rabs x) - prec))%Z.
rewrite mag_abs.
destruct (Req_dec x 0) as [Hx|Hx].
rewrite Hx, Rabs_R0.
apply bpow_gt_0.
destruct (mag beta x) as (ex, Ex).
now apply Ex.
Qed.

Theorem generic_format_FLX :
forall x, FLX_format x -> generic_format beta FLX_exp x.
Proof. hammer_hook "FLX" "FLX.generic_format_FLX".
clear prec_gt_0_.
intros x [[mx ex] H1 H2].
simpl in H2.
rewrite H1.
apply generic_format_F2R.
intros Zmx.
unfold cexp, FLX_exp.
rewrite mag_F2R with (1 := Zmx).
apply Zplus_le_reg_r with (prec - ex)%Z.
ring_simplify.
now apply mag_le_Zpower.
Qed.

Theorem FLX_format_satisfies_any :
satisfies_any FLX_format.
Proof. hammer_hook "FLX" "FLX.FLX_format_satisfies_any".
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
intros x.
split.
apply FLX_format_generic.
apply generic_format_FLX.
Qed.

Theorem FLX_format_FIX :
forall x e,
(bpow (e - 1) <= Rabs x <= bpow e)%R ->
FIX_format beta (e - prec) x ->
FLX_format x.
Proof with auto with typeclass_instances. hammer_hook "FLX" "FLX.FLX_format_FIX".
intros x e Hx Fx.
apply FLX_format_generic.
apply generic_format_FIX in Fx.
revert Fx.
apply generic_inclusion with (e := e)...
apply Z.le_refl.
Qed.


Inductive FLXN_format (x : R) : Prop :=
FLXN_spec (f : float beta) :
x = F2R f ->
(x <> 0%R -> Zpower beta (prec - 1) <= Z.abs (Fnum f) < Zpower beta prec)%Z ->
FLXN_format x.

Theorem generic_format_FLXN :
forall x, FLXN_format x -> generic_format beta FLX_exp x.
Proof. hammer_hook "FLX" "FLX.generic_format_FLXN".
intros x [[xm ex] H1 H2].
destruct (Req_dec x 0) as [Zx|Zx].
rewrite Zx.
apply generic_format_0.
specialize (H2 Zx).
apply generic_format_FLX.
rewrite H1.
eexists ; repeat split.
apply H2.
Qed.

Theorem FLXN_format_generic :
forall x, generic_format beta FLX_exp x -> FLXN_format x.
Proof. hammer_hook "FLX" "FLX.FLXN_format_generic".
intros x Hx.
rewrite Hx.
simpl.
eexists. easy.
rewrite <- Hx.
intros Zx.
simpl.
split.

apply le_IZR.
rewrite IZR_Zpower.
2: now apply Zlt_0_le_0_pred.
rewrite abs_IZR, <- scaled_mantissa_generic with (1 := Hx).
apply Rmult_le_reg_r with (bpow (cexp beta FLX_exp x)).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite <- scaled_mantissa_abs.
rewrite <- cexp_abs.
rewrite scaled_mantissa_mult_bpow.
unfold cexp, FLX_exp.
rewrite mag_abs.
ring_simplify (prec - 1 + (mag beta x - prec))%Z.
destruct (mag beta x) as (ex,Ex).
now apply Ex.

apply lt_IZR.
rewrite IZR_Zpower.
2: now apply Zlt_le_weak.
rewrite abs_IZR, <- scaled_mantissa_generic with (1 := Hx).
apply Rmult_lt_reg_r with (bpow (cexp beta FLX_exp x)).
apply bpow_gt_0.
rewrite <- bpow_plus.
rewrite <- scaled_mantissa_abs.
rewrite <- cexp_abs.
rewrite scaled_mantissa_mult_bpow.
unfold cexp, FLX_exp.
rewrite mag_abs.
ring_simplify (prec + (mag beta x - prec))%Z.
destruct (mag beta x) as (ex,Ex).
now apply Ex.
Qed.

Theorem FLXN_format_satisfies_any :
satisfies_any FLXN_format.
Proof. hammer_hook "FLX" "FLX.FLXN_format_satisfies_any".
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FLX_exp)).
split ; intros H.
now apply FLXN_format_generic.
now apply generic_format_FLXN.
Qed.

Lemma negligible_exp_FLX :
negligible_exp FLX_exp = None.
Proof. hammer_hook "FLX" "FLX.negligible_exp_FLX".
case (negligible_exp_spec FLX_exp).
intros _; reflexivity.
intros n H2; contradict H2.
unfold FLX_exp; unfold Prec_gt_0 in prec_gt_0_; omega.
Qed.

Theorem generic_format_FLX_1 :
generic_format beta FLX_exp 1.
Proof. hammer_hook "FLX" "FLX.generic_format_FLX_1".
unfold generic_format, scaled_mantissa, cexp, F2R; simpl.
rewrite Rmult_1_l, (mag_unique beta 1 1).
{ unfold FLX_exp.
rewrite <- IZR_Zpower; [|unfold Prec_gt_0 in prec_gt_0_; omega].
rewrite Ztrunc_IZR, IZR_Zpower; [|unfold Prec_gt_0 in prec_gt_0_; omega].
rewrite <- bpow_plus.
now replace (_ + _)%Z with Z0 by ring. }
rewrite Rabs_R1; simpl; split; [now right|].
unfold Z.pow_pos; simpl; rewrite Zmult_1_r; apply IZR_lt.
assert (H := Zle_bool_imp_le _ _ (radix_prop beta)); omega.
Qed.

Theorem ulp_FLX_0: (ulp beta FLX_exp 0 = 0)%R.
Proof. hammer_hook "FLX" "FLX.ulp_FLX_0".
unfold ulp; rewrite Req_bool_true; trivial.
rewrite negligible_exp_FLX; easy.
Qed.

Lemma ulp_FLX_1 : ulp beta FLX_exp 1 = bpow (-prec + 1).
Proof. hammer_hook "FLX" "FLX.ulp_FLX_1".
unfold ulp, FLX_exp, cexp; rewrite Req_bool_false; [|apply R1_neq_R0].
rewrite mag_1; f_equal; ring.
Qed.

Lemma succ_FLX_1 : (succ beta FLX_exp 1 = 1 + bpow (-prec + 1))%R.
Proof. hammer_hook "FLX" "FLX.succ_FLX_1".
now unfold succ; rewrite Rle_bool_true; [|apply Rle_0_1]; rewrite ulp_FLX_1.
Qed.

Theorem eq_0_round_0_FLX :
forall rnd {Vr: Valid_rnd rnd} x,
round beta FLX_exp rnd x = 0%R -> x = 0%R.
Proof. hammer_hook "FLX" "FLX.eq_0_round_0_FLX".
intros rnd Hr x.
apply eq_0_round_0_negligible_exp; try assumption.
apply FLX_exp_valid.
apply negligible_exp_FLX.
Qed.

Theorem gt_0_round_gt_0_FLX :
forall rnd {Vr: Valid_rnd rnd} x,
(0 < x)%R -> (0 < round beta FLX_exp rnd x)%R.
Proof with auto with typeclass_instances. hammer_hook "FLX" "FLX.gt_0_round_gt_0_FLX".
intros rnd Hr x Hx.
assert (K: (0 <= round beta FLX_exp rnd x)%R).
rewrite <- (round_0 beta FLX_exp rnd).
apply round_le... now apply Rlt_le.
destruct K; try easy.
absurd (x = 0)%R.
now apply Rgt_not_eq.
apply eq_0_round_0_FLX with rnd...
Qed.


Theorem ulp_FLX_le :
forall x, (ulp beta FLX_exp x <= Rabs x * bpow (1-prec))%R.
Proof. hammer_hook "FLX" "FLX.ulp_FLX_le".
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLX_0, Rabs_R0.
right; ring.
rewrite ulp_neq_0; try exact Hx.
unfold cexp, FLX_exp.
replace (mag beta x - prec)%Z with ((mag beta x - 1) + (1-prec))%Z by ring.
rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
now apply bpow_mag_le.
Qed.

Theorem ulp_FLX_ge :
forall x, (Rabs x * bpow (-prec) <= ulp beta FLX_exp x)%R.
Proof. hammer_hook "FLX" "FLX.ulp_FLX_ge".
intros x; case (Req_dec x 0); intros Hx.
rewrite Hx, ulp_FLX_0, Rabs_R0.
right; ring.
rewrite ulp_neq_0; try exact Hx.
unfold cexp, FLX_exp.
unfold Zminus; rewrite bpow_plus.
apply Rmult_le_compat_r.
apply bpow_ge_0.
left; now apply bpow_mag_gt.
Qed.

Lemma ulp_FLX_exact_shift :
forall x e,
(ulp beta FLX_exp (x * bpow e) = ulp beta FLX_exp x * bpow e)%R.
Proof. hammer_hook "FLX" "FLX.ulp_FLX_exact_shift".
intros x e.
destruct (Req_dec x 0) as [Hx|Hx].
{ unfold ulp.
now rewrite !Req_bool_true, negligible_exp_FLX; rewrite ?Hx, ?Rmult_0_l. }
unfold ulp; rewrite Req_bool_false;
[|now intro H; apply Hx, (Rmult_eq_reg_r (bpow e));
[rewrite Rmult_0_l|apply Rgt_not_eq, Rlt_gt, bpow_gt_0]].
rewrite (Req_bool_false _ _ Hx), <- bpow_plus; f_equal; unfold cexp, FLX_exp.
now rewrite mag_mult_bpow; [ring|].
Qed.

Lemma succ_FLX_exact_shift :
forall x e,
(succ beta FLX_exp (x * bpow e) = succ beta FLX_exp x * bpow e)%R.
Proof. hammer_hook "FLX" "FLX.succ_FLX_exact_shift".
intros x e.
destruct (Rle_or_lt 0 x) as [Px|Nx].
{ rewrite succ_eq_pos; [|now apply Rmult_le_pos, bpow_ge_0].
rewrite (succ_eq_pos _ _ _ Px).
now rewrite Rmult_plus_distr_r; f_equal; apply ulp_FLX_exact_shift. }
unfold succ.
rewrite Rle_bool_false; [|assert (H := bpow_gt_0 beta e); nra].
rewrite Rle_bool_false; [|now simpl].
rewrite Ropp_mult_distr_l_reverse, <-Ropp_mult_distr_l_reverse; f_equal.
unfold pred_pos.
rewrite mag_mult_bpow; [|lra].
replace (_ - 1)%Z with (mag beta (- x) - 1 + e)%Z; [|ring]; rewrite bpow_plus.
unfold Req_bool; rewrite Rcompare_mult_r; [|now apply bpow_gt_0].
fold (Req_bool (-x) (bpow (mag beta (-x) - 1))); case Req_bool.
{ unfold FLX_exp.
replace (_ - _)%Z with (mag beta (- x) - 1 - prec + e)%Z; [|ring].
rewrite bpow_plus; ring. }
rewrite ulp_FLX_exact_shift; ring.
Qed.


Global Instance FLX_exp_monotone : Monotone_exp FLX_exp.
Proof. hammer_hook "FLX" "FLX.FLX_exp_monotone".
intros ex ey Hxy.
now apply Zplus_le_compat_r.
Qed.


Hypothesis NE_prop : Z.even beta = false \/ (1 < prec)%Z.

Global Instance exists_NE_FLX : Exists_NE beta FLX_exp.
Proof. hammer_hook "FLX" "FLX.exists_NE_FLX".
destruct NE_prop as [H|H].
now left.
right.
unfold FLX_exp.
split ; omega.
Qed.

End RND_FLX.
