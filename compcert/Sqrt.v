From Hammer Require Import Hammer.





From compcert Require Import Raux.
From compcert Require Import Defs.
From compcert Require Import Digits.
From compcert Require Import Generic_fmt.
From compcert Require Import Float_prop.
From compcert Require Import Bracket.

Set Implicit Arguments.
Set Strongly Strict Implicit.

Section Fcalc_sqrt.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.



Lemma mag_sqrt_F2R :
forall m1 e1,
(0 < m1)%Z ->
mag beta (sqrt (F2R (Float beta m1 e1))) = Z.div2 (Zdigits beta m1 + e1 + 1) :> Z.
Proof. hammer_hook "Sqrt" "Sqrt.mag_sqrt_F2R".
intros m1 e1 Hm1.
rewrite <- (mag_F2R_Zdigits beta m1 e1) by now apply Zgt_not_eq.
apply mag_sqrt.
now apply F2R_gt_0.
Qed.

Definition Fsqrt_core m1 e1 e :=
let d1 := Zdigits beta m1 in
let m1' := (m1 * Zpower beta (e1 - 2 * e))%Z in
let (q, r) := Z.sqrtrem m1' in
let l :=
if Zeq_bool r 0 then loc_Exact
else loc_Inexact (if Zle_bool r q then Lt else Gt) in
(q, l).

Theorem Fsqrt_core_correct :
forall m1 e1 e,
(0 < m1)%Z ->
(2 * e <= e1)%Z ->
let '(m, l) := Fsqrt_core m1 e1 e in
inbetween_float beta m e (sqrt (F2R (Float beta m1 e1))) l.
Proof. hammer_hook "Sqrt" "Sqrt.Fsqrt_core_correct".
intros m1 e1 e Hm1 He.
unfold Fsqrt_core.
set (m' := Zmult _ _).
assert (0 <= m')%Z as Hm'.
{ apply Z.mul_nonneg_nonneg.
now apply Zlt_le_weak.
apply Zpower_ge_0. }
assert (sqrt (F2R (Float beta m1 e1)) = sqrt (IZR m') * bpow e)%R as Hf.
{ rewrite <- (sqrt_Rsqr (bpow e)) by apply bpow_ge_0.
rewrite <- sqrt_mult.
unfold Rsqr, m'.
rewrite mult_IZR, IZR_Zpower by omega.
rewrite Rmult_assoc, <- 2!bpow_plus.
now replace (_ + _)%Z with e1 by ring.
now apply IZR_le.
apply Rle_0_sqr. }
generalize (Z.sqrtrem_spec m' Hm').
destruct Z.sqrtrem as [q r].
intros [Hq Hr].
rewrite Hf.
unfold inbetween_float, F2R. simpl Fnum.
apply inbetween_mult_compat.
apply bpow_gt_0.
rewrite Hq.
case Zeq_bool_spec ; intros Hr'.

rewrite Hr', Zplus_0_r, mult_IZR.
fold (Rsqr (IZR q)).
rewrite sqrt_Rsqr.
now constructor.
apply IZR_le.
clear -Hr ; omega.

constructor.
split.

apply Rle_lt_trans with (sqrt (IZR (q * q))).
rewrite mult_IZR.
fold (Rsqr (IZR q)).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply IZR_le.
clear -Hr ; omega.
apply sqrt_lt_1.
rewrite mult_IZR.
apply Rle_0_sqr.
rewrite <- Hq.
now apply IZR_le.
apply IZR_lt.
omega.
apply Rlt_le_trans with (sqrt (IZR ((q + 1) * (q + 1)))).
apply sqrt_lt_1.
rewrite <- Hq.
now apply IZR_le.
rewrite mult_IZR.
apply Rle_0_sqr.
apply IZR_lt.
ring_simplify.
omega.
rewrite mult_IZR.
fold (Rsqr (IZR (q + 1))).
rewrite sqrt_Rsqr.
apply Rle_refl.
apply IZR_le.
clear -Hr ; omega.

rewrite Rcompare_half_r.
generalize (Rcompare_sqr (2 * sqrt (IZR (q * q + r))) (IZR q + IZR (q + 1))).
rewrite 2!Rabs_pos_eq.
intros <-.
replace ((2 * sqrt (IZR (q * q + r))) * (2 * sqrt (IZR (q * q + r))))%R
with (4 * Rsqr (sqrt (IZR (q * q + r))))%R by (unfold Rsqr ; ring).
rewrite Rsqr_sqrt.
rewrite <- plus_IZR, <- 2!mult_IZR.
rewrite Rcompare_IZR.
replace ((q + (q + 1)) * (q + (q + 1)))%Z with (4 * (q * q) + 4 * q + 1)%Z by ring.
generalize (Zle_cases r q).
case (Zle_bool r q) ; intros Hr''.
change (4 * (q * q + r) < 4 * (q * q) + 4 * q + 1)%Z.
omega.
change (4 * (q * q + r) > 4 * (q * q) + 4 * q + 1)%Z.
omega.
rewrite <- Hq.
now apply IZR_le.
rewrite <- plus_IZR.
apply IZR_le.
clear -Hr ; omega.
apply Rmult_le_pos.
now apply IZR_le.
apply sqrt_ge_0.
Qed.

Definition Fsqrt (x : float beta) :=
let (m1, e1) := x in
let e' := (Zdigits beta m1 + e1 + 1)%Z in
let e := Z.min (fexp (Z.div2 e')) (Z.div2 e1) in
let '(m, l) := Fsqrt_core m1 e1 e in
(m, e, l).

Theorem Fsqrt_correct :
forall x,
(0 < F2R x)%R ->
let '(m, e, l) := Fsqrt x in
(e <= cexp beta fexp (sqrt (F2R x)))%Z /\
inbetween_float beta m e (sqrt (F2R x)) l.
Proof. hammer_hook "Sqrt" "Sqrt.Fsqrt_correct".
intros [m1 e1] Hm1.
apply gt_0_F2R in Hm1.
unfold Fsqrt.
set (e := Z.min _ _).
assert (2 * e <= e1)%Z as He.
{ assert (e <= Z.div2 e1)%Z by apply Z.le_min_r.
rewrite (Zdiv2_odd_eqn e1).
destruct Z.odd ; omega. }
generalize (Fsqrt_core_correct m1 e1 e Hm1 He).
destruct Fsqrt_core as [m l].
apply conj.
apply Z.le_trans with (1 := Z.le_min_l _ _).
unfold cexp.
rewrite (mag_sqrt_F2R m1 e1 Hm1).
apply Z.le_refl.
Qed.

End Fcalc_sqrt.
