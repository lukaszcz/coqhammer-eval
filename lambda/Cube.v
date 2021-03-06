From Hammer Require Import Hammer.









































Require Import Arith.
From Lambda Require Import Terms.
From Lambda Require Import Reduction.
From Lambda Require Import Redexes.
From Lambda Require Import Test.
From Lambda Require Import Substitution.
From Lambda Require Import Residuals.








Inductive compat : redexes -> redexes -> redexes -> Prop :=
| Compat_Var : forall n : nat, compat (Var n) (Var n) (Var n)
| Compat_Fun :
forall U V W : redexes, compat U V W -> compat (Fun U) (Fun V) (Fun W)
| Compat_Ap1 :
forall U1 V1 W1 : redexes,
compat U1 V1 W1 ->
forall U2 V2 W2 : redexes,
compat U2 V2 W2 ->
forall b : bool, compat (Ap false U1 U2) (Ap false V1 V2) (Ap b W1 W2)
| Compat_Ap2 :
forall U1 V1 W1 : redexes,
compat U1 V1 W1 ->
forall U2 V2 W2 : redexes,
compat U2 V2 W2 ->
forall b b' : bool,
compat (Ap true (Fun U1) U2) (Ap b (Fun V1) V2) (Ap b' (Fun W1) W2).

Lemma compat_intro :
forall U W WU : redexes,
residuals W U WU ->
forall (V WV : redexes) (R2 : residuals W V WV) (S : sub V U), compat U V W.
Proof. hammer_hook "Cube" "Cube.compat_intro".

simple induction 1; intros; generalize S; inversion_clear R2; intros;
inversion_clear S.
apply Compat_Var.
apply Compat_Fun.
inversion_clear S0; apply H1 with W1; auto.
inversion_clear S0; apply Compat_Ap1; auto.
apply H1 with W0; auto.
apply H3 with W3; auto.
inversion_clear S0.
inversion_clear S0; generalize H4; inversion_clear H8.
intro H11; inversion_clear H11; apply Compat_Ap2; auto.
apply H1 with W4; auto.
apply H3 with W3; auto.
generalize H4; inversion_clear S0.
inversion_clear H8.
intro H11; inversion_clear H11; apply Compat_Ap2; auto.
apply H1 with W4; auto.
apply H3 with W3; auto.
inversion_clear S0; apply Compat_Ap2; inversion_clear H8; auto.
apply H1 with W0; auto.
apply H3 with W3; auto.
inversion_clear S0; apply Compat_Ap2; inversion_clear H8; auto.
apply H1 with W0; auto.
apply H3 with W3; auto.
Qed.

Lemma prism0 :
forall U V W : redexes,
compat U V W ->
forall (UV : redexes) (R1 : residuals U V UV) (WU WV : redexes)
(R2 : residuals W U WU) (R3 : residuals W V WV),
residuals WV UV WU.
Proof. hammer_hook "Cube" "Cube.prism0".
simple induction 1.
intros; inversion_clear R1; inversion_clear R2; inversion_clear R3; auto.
intros; inversion_clear R1; inversion_clear R2; inversion_clear R3; auto.
intros; inversion_clear R1; inversion_clear R2; inversion_clear R3; auto.
simple induction b; intros; inversion_clear R1; inversion_clear R2;
inversion_clear R3; auto.
apply commutation; auto.
inversion_clear H4; inversion_clear H8; auto.
Qed.











Lemma prism1 :
forall U V W : redexes,
sub V U ->
forall UV : redexes,
residuals U V UV ->
forall WV : redexes,
residuals W V WV ->
forall WU : redexes, residuals W U WU -> residuals WV UV WU.
Proof. hammer_hook "Cube" "Cube.prism1".
intros; apply prism0 with U V W; auto.
apply compat_intro with WU WV; trivial.
Qed.


Lemma prism2 :
forall U V W : redexes,
sub V U ->
regular U ->
forall UV : redexes,
residuals U V UV ->
forall WV : redexes,
residuals W V WV ->
forall WU : redexes, residuals WV UV WU -> residuals W U WU.
Proof. hammer_hook "Cube" "Cube.prism2".
intros.
elim (residuals_intro W U); trivial.
intros WU' R; elim (residuals_function WV UV WU) with WU'; trivial.
apply prism1 with U V W; trivial.
apply comp_trans with V.
apply residuals_comp with WV; trivial.
apply comp_sym; apply residuals_comp with UV; trivial.
Qed.

Theorem prism :
forall U V W : redexes,
sub V U ->
forall UV : redexes,
residuals U V UV ->
forall WV : redexes,
residuals W V WV ->
forall WU : redexes, residuals W U WU <-> regular U /\ residuals WV UV WU.
Proof. hammer_hook "Cube" "Cube.prism".
intros; unfold iff in |- *; split.
intro; split.
apply residuals_regular with W WU; trivial.
apply prism1 with U V W; trivial.
simple induction 1; intros; apply prism2 with V UV WV; trivial.
Qed.









Lemma cube :
forall U V UV VU : redexes,
residuals U V UV ->
residuals V U VU ->
forall W WU WV WUV : redexes,
residuals W U WU ->
residuals WU VU WUV -> residuals W V WV -> residuals WV UV WUV.
Proof. hammer_hook "Cube" "Cube.cube".
intros.
cut (comp U V).
2: apply residuals_comp with UV; trivial.
intro C; elim (union_defined U V C); intros T UVT.
apply prism1 with T V W; trivial.
apply union_r with U; trivial.
apply preservation with U; trivial.
apply prism2 with U VU WU; trivial.
apply union_l with V; trivial.
apply union_preserve_regular with U V; trivial.
apply residuals_regular with V VU; trivial.
apply residuals_regular with U UV; trivial.
apply preservation with V; trivial.
apply union_sym; trivial.
Qed.



Lemma paving :
forall U V W WU WV : redexes,
residuals W U WU ->
residuals W V WV ->
exists UV : redexes,
(exists VU : redexes,
(exists WUV : redexes, residuals WU VU WUV /\ residuals WV UV WUV)).
Proof. hammer_hook "Cube" "Cube.paving".
intros; elim (residuals_intro U V).
intros UV R1; exists UV.
elim (residuals_intro V U).
intros VU R2; exists VU.
elim (residuals_intro WU VU).
intros WUV R3; exists WUV.
split; trivial.
apply cube with U V VU W WU; trivial.
apply mutual_residuals_comp with U W V; trivial.
apply residuals_preserve_regular with V U; trivial.
apply residuals_regular with U UV; trivial.
apply comp_sym; apply residuals_comp with UV; trivial.
apply residuals_regular with W WU; trivial.
apply comp_trans with W.
apply comp_sym; apply residuals_comp with WU; trivial.
apply residuals_comp with WV; trivial.
apply residuals_regular with W WV; trivial.
Qed.
