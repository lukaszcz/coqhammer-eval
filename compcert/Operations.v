From Hammer Require Import Hammer.




From compcert Require Import Raux.
From compcert Require Import Defs.
From compcert Require Import Float_prop.

Set Implicit Arguments.
Set Strongly Strict Implicit.

Section Float_ops.

Variable beta : radix.

Notation bpow e := (bpow beta e).

Arguments Float {beta}.

Definition Falign (f1 f2 : float beta) :=
let '(Float m1 e1) := f1 in
let '(Float m2 e2) := f2 in
if Zle_bool e1 e2
then (m1, (m2 * Zpower beta (e2 - e1))%Z, e1)
else ((m1 * Zpower beta (e1 - e2))%Z, m2, e2).

Theorem Falign_spec :
forall f1 f2 : float beta,
let '(m1, m2, e) := Falign f1 f2 in
F2R f1 = @F2R beta (Float m1 e) /\ F2R f2 = @F2R beta (Float m2 e).
Proof. hammer_hook "Operations" "Operations.Falign_spec".
unfold Falign.
intros (m1, e1) (m2, e2).
generalize (Zle_cases e1 e2).
case (Zle_bool e1 e2) ; intros He ; split ; trivial.
now rewrite <- F2R_change_exp.
rewrite <- F2R_change_exp.
apply refl_equal.
omega.
Qed.

Theorem Falign_spec_exp:
forall f1 f2 : float beta,
snd (Falign f1 f2) = Z.min (Fexp f1) (Fexp f2).
Proof. hammer_hook "Operations" "Operations.Falign_spec_exp".
intros (m1,e1) (m2,e2).
unfold Falign; simpl.
generalize (Zle_cases e1 e2);case (Zle_bool e1 e2); intros He.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
case (Zmin_spec e1 e2); intros (H1,H2); easy.
Qed.

Definition Fopp (f1 : float beta) : float beta :=
let '(Float m1 e1) := f1 in
Float (-m1)%Z e1.

Theorem F2R_opp :
forall f1 : float beta,
(F2R (Fopp f1) = -F2R f1)%R.
intros (m1,e1).
apply F2R_Zopp.
Qed.

Definition Fabs (f1 : float beta) : float beta :=
let '(Float m1 e1) := f1 in
Float (Z.abs m1)%Z e1.

Theorem F2R_abs :
forall f1 : float beta,
(F2R (Fabs f1) = Rabs (F2R f1))%R.
intros (m1,e1).
apply F2R_Zabs.
Qed.

Definition Fplus (f1 f2 : float beta) : float beta :=
let '(m1, m2 ,e) := Falign f1 f2 in
Float (m1 + m2) e.

Theorem F2R_plus :
forall f1 f2 : float beta,
F2R (Fplus f1 f2) = (F2R f1 + F2R f2)%R.
Proof. hammer_hook "Operations" "Operations.F2R_plus".
intros f1 f2.
unfold Fplus.
generalize (Falign_spec f1 f2).
destruct (Falign f1 f2) as ((m1, m2), e).
intros (H1, H2).
rewrite H1, H2.
unfold F2R. simpl.
rewrite plus_IZR.
apply Rmult_plus_distr_r.
Qed.

Theorem Fplus_same_exp :
forall m1 m2 e,
Fplus (Float m1 e) (Float m2 e) = Float (m1 + m2) e.
Proof. hammer_hook "Operations" "Operations.Fplus_same_exp".
intros m1 m2 e.
unfold Fplus.
simpl.
now rewrite Zle_bool_refl, Zminus_diag, Zmult_1_r.
Qed.

Theorem Fexp_Fplus :
forall f1 f2 : float beta,
Fexp (Fplus f1 f2) = Z.min (Fexp f1) (Fexp f2).
Proof. hammer_hook "Operations" "Operations.Fexp_Fplus".
intros f1 f2.
unfold Fplus.
rewrite <- Falign_spec_exp.
now destruct (Falign f1 f2) as ((p,q),e).
Qed.

Definition Fminus (f1 f2 : float beta) :=
Fplus f1 (Fopp f2).

Theorem F2R_minus :
forall f1 f2 : float beta,
F2R (Fminus f1 f2) = (F2R f1 - F2R f2)%R.
Proof. hammer_hook "Operations" "Operations.F2R_minus".
intros f1 f2; unfold Fminus.
rewrite F2R_plus, F2R_opp.
ring.
Qed.

Theorem Fminus_same_exp :
forall m1 m2 e,
Fminus (Float m1 e) (Float m2 e) = Float (m1 - m2) e.
Proof. hammer_hook "Operations" "Operations.Fminus_same_exp".
intros m1 m2 e.
unfold Fminus.
apply Fplus_same_exp.
Qed.

Definition Fmult (f1 f2 : float beta) : float beta :=
let '(Float m1 e1) := f1 in
let '(Float m2 e2) := f2 in
Float (m1 * m2) (e1 + e2).

Theorem F2R_mult :
forall f1 f2 : float beta,
F2R (Fmult f1 f2) = (F2R f1 * F2R f2)%R.
Proof. hammer_hook "Operations" "Operations.F2R_mult".
intros (m1, e1) (m2, e2).
unfold Fmult, F2R. simpl.
rewrite mult_IZR, bpow_plus.
ring.
Qed.

End Float_ops.
