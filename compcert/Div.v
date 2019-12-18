From Hammer Require Import Hammer.





From compcert Require Import Raux.
From compcert Require Import Defs.
From compcert Require Import Generic_fmt.
From compcert Require Import Float_prop.
From compcert Require Import Digits.
From compcert Require Import Bracket.

Set Implicit Arguments.
Set Strongly Strict Implicit.

Section Fcalc_div.

Variable beta : radix.
Notation bpow e := (bpow beta e).

Variable fexp : Z -> Z.



Lemma mag_div_F2R :
forall m1 e1 m2 e2,
(0 < m1)%Z -> (0 < m2)%Z ->
let e := ((Zdigits beta m1 + e1) - (Zdigits beta m2 + e2))%Z in
(e <= mag beta (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) <= e + 1)%Z.
Proof. hammer_hook "Div" "Div.mag_div_F2R".
intros m1 e1 m2 e2 Hm1 Hm2.
rewrite <- (mag_F2R_Zdigits beta m1 e1) by now apply Zgt_not_eq.
rewrite <- (mag_F2R_Zdigits beta m2 e2) by now apply Zgt_not_eq.
apply mag_div.
now apply F2R_neq_0, Zgt_not_eq.
now apply F2R_neq_0, Zgt_not_eq.
Qed.

Definition Fdiv_core m1 e1 m2 e2 e :=
let (m1', m2') :=
if Zle_bool e (e1 - e2)%Z
then (m1 * Zpower beta (e1 - e2 - e), m2)%Z
else (m1, m2 * Zpower beta (e - (e1 - e2)))%Z in
let '(q, r) :=  Z.div_eucl m1' m2' in
(q, new_location m2' r loc_Exact).

Theorem Fdiv_core_correct :
forall m1 e1 m2 e2 e,
(0 < m1)%Z -> (0 < m2)%Z ->
let '(m, l) := Fdiv_core m1 e1 m2 e2 e in
inbetween_float beta m e (F2R (Float beta m1 e1) / F2R (Float beta m2 e2)) l.
Proof. hammer_hook "Div" "Div.Fdiv_core_correct".
intros m1 e1 m2 e2 e Hm1 Hm2.
unfold Fdiv_core.
match goal with |- context [if ?b then ?b1 else ?b2] => set (m12 := if b then b1 else b2) end.
case_eq m12 ; intros m1' m2' Hm.
assert ((F2R (Float beta m1 e1) / F2R (Float beta m2 e2) = IZR m1' / IZR m2' * bpow e)%R /\ (0 < m2')%Z) as [Hf Hm2'].
{ unfold F2R, Zminus ; simpl.
destruct (Zle_bool e (e1 - e2)) eqn:He' ; injection Hm ; intros ; subst.
- split ; try easy.
apply Zle_bool_imp_le in He'.
rewrite mult_IZR, IZR_Zpower by omega.
unfold Zminus ; rewrite 2!bpow_plus, 2!bpow_opp.
field.
repeat split ; try apply Rgt_not_eq, bpow_gt_0.
now apply IZR_neq, Zgt_not_eq.
- apply Z.leb_gt in He'.
split ; cycle 1.
{ apply Z.mul_pos_pos with (1 := Hm2).
apply Zpower_gt_0 ; omega. }
rewrite mult_IZR, IZR_Zpower by omega.
unfold Zminus ; rewrite bpow_plus, bpow_opp, bpow_plus, bpow_opp.
field.
repeat split ; try apply Rgt_not_eq, bpow_gt_0.
now apply IZR_neq, Zgt_not_eq. }
clearbody m12 ; clear Hm Hm1 Hm2.
generalize (Z_div_mod m1' m2' (Z.lt_gt _ _ Hm2')).
destruct (Z.div_eucl m1' m2') as (q, r).
intros (Hq, Hr).
rewrite Hf.
unfold inbetween_float, F2R. simpl.
rewrite Hq, 2!plus_IZR, mult_IZR.
apply inbetween_mult_compat.
apply bpow_gt_0.
destruct (Z_lt_le_dec 1 m2') as [Hm2''|Hm2''].
- replace 1%R with (IZR m2' * /IZR m2')%R.
apply new_location_correct ; try easy.
apply Rinv_0_lt_compat.
now apply IZR_lt.
constructor.
field.
now apply IZR_neq, Zgt_not_eq.
field.
now apply IZR_neq, Zgt_not_eq.
- assert (r = 0 /\ m2' = 1)%Z as [-> ->] by (clear -Hr Hm2'' ; omega).
unfold Rdiv.
rewrite Rmult_1_l, Rplus_0_r, Rinv_1, Rmult_1_r.
now constructor.
Qed.

Definition Fdiv (x y : float beta) :=
let (m1, e1) := x in
let (m2, e2) := y in
let e' := ((Zdigits beta m1 + e1) - (Zdigits beta m2 + e2))%Z in
let e := Z.min (Z.min (fexp e') (fexp (e' + 1))) (e1 - e2) in
let '(m, l) := Fdiv_core m1 e1 m2 e2 e in
(m, e, l).

Theorem Fdiv_correct :
forall x y,
(0 < F2R x)%R -> (0 < F2R y)%R ->
let '(m, e, l) := Fdiv x y in
(e <= cexp beta fexp (F2R x / F2R y))%Z /\
inbetween_float beta m e (F2R x / F2R y) l.
Proof. hammer_hook "Div" "Div.Fdiv_correct".
intros [m1 e1] [m2 e2] Hm1 Hm2.
apply gt_0_F2R in Hm1.
apply gt_0_F2R in Hm2.
unfold Fdiv.
generalize (mag_div_F2R m1 e1 m2 e2 Hm1 Hm2).
set (e := Zminus _ _).
set (e' := Z.min (Z.min (fexp e) (fexp (e + 1))) (e1 - e2)).
intros [H1 H2].
generalize (Fdiv_core_correct m1 e1 m2 e2 e' Hm1 Hm2).
destruct Fdiv_core as [m' l].
apply conj.
apply Z.le_trans with (1 := Z.le_min_l _ _).
unfold cexp.
destruct (Zle_lt_or_eq _ _ H1) as [H|H].
- replace (fexp (mag _ _)) with (fexp (e + 1)).
apply Z.le_min_r.
clear -H1 H2 H ; apply f_equal ; omega.
- replace (fexp (mag _ _)) with (fexp e).
apply Z.le_min_l.
clear -H1 H2 H ; apply f_equal ; omega.
Qed.

End Fcalc_div.
