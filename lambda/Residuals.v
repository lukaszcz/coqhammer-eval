From Hammer Require Import Hammer.









































Require Import Arith.
From Lambda Require Import Terms.
From Lambda Require Import Reduction.
From Lambda Require Import Redexes.
From Lambda Require Import Test.
From Lambda Require Import Substitution.







Inductive residuals : redexes -> redexes -> redexes -> Prop :=
| Res_Var : forall n : nat, residuals (Var n) (Var n) (Var n)
| Res_Fun :
forall U V W : redexes,
residuals U V W -> residuals (Fun U) (Fun V) (Fun W)
| Res_Ap :
forall U1 V1 W1 : redexes,
residuals U1 V1 W1 ->
forall U2 V2 W2 : redexes,
residuals U2 V2 W2 ->
forall b : bool, residuals (Ap b U1 U2) (Ap false V1 V2) (Ap b W1 W2)
| Res_redex :
forall U1 V1 W1 : redexes,
residuals U1 V1 W1 ->
forall U2 V2 W2 : redexes,
residuals U2 V2 W2 ->
forall b : bool,
residuals (Ap b (Fun U1) U2) (Ap true (Fun V1) V2) (subst_r W2 W1).


Hint Resolve Res_Var Res_Fun Res_Ap Res_redex.

Lemma residuals_function :
forall U V W : redexes,
residuals U V W -> forall (W' : redexes) (R : residuals U V W'), W' = W.
Proof. hammer_hook "Residuals" "Residuals.residuals_function".

simple induction 1; intros; inversion R; auto with arith.
elim H1 with W1; trivial with arith.
elim H1 with W0; elim H3 with W3; trivial with arith.
elim H1 with W0; elim H3 with W3; trivial with arith.
Qed.



Lemma residuals_lift_rec :
forall U1 U2 U3 : redexes,
residuals U1 U2 U3 ->
forall k n : nat,
residuals (lift_rec_r U1 n k) (lift_rec_r U2 n k) (lift_rec_r U3 n k).
Proof. hammer_hook "Residuals" "Residuals.residuals_lift_rec".
simple induction 1; simpl in |- *; intros; auto with arith.
rewrite lift_subst; auto with arith.
Qed.

Lemma residuals_lift :
forall U1 U2 U3 : redexes,
residuals U1 U2 U3 ->
forall k : nat, residuals (lift_r k U1) (lift_r k U2) (lift_r k U3).
Proof. hammer_hook "Residuals" "Residuals.residuals_lift".
unfold lift_r in |- *; intros; apply residuals_lift_rec; trivial with arith.
Qed.
Hint Resolve residuals_lift.

Lemma residuals_subst_rec :
forall U1 U2 U3 V1 V2 V3 : redexes,
residuals U1 U2 U3 ->
residuals V1 V2 V3 ->
forall k : nat,
residuals (subst_rec_r U1 V1 k) (subst_rec_r U2 V2 k) (subst_rec_r U3 V3 k).
Proof. hammer_hook "Residuals" "Residuals.residuals_subst_rec".
simple induction 1; simpl in |- *; auto with arith.
intros n R k; unfold insert_Var in |- *; elim (compare k n); auto with arith.
simple induction a; auto with arith.
intros; rewrite substitution; auto with arith.
Qed.
Hint Resolve residuals_subst_rec.





Theorem commutation :
forall U1 U2 U3 V1 V2 V3 : redexes,
residuals U1 U2 U3 ->
residuals V1 V2 V3 ->
residuals (subst_r V1 U1) (subst_r V2 U2) (subst_r V3 U3).
Proof. hammer_hook "Residuals" "Residuals.commutation".
unfold subst_r in |- *; auto with arith.
Qed.

Lemma residuals_comp : forall U V W : redexes, residuals U V W -> comp U V.
Proof. hammer_hook "Residuals" "Residuals.residuals_comp".
simple induction 1; simpl in |- *; auto with arith.
Qed.

Lemma preservation1 :
forall U V UV : redexes,
residuals U V UV ->
forall (T : redexes) (UVT : union U V T), residuals T V UV.
Proof. hammer_hook "Residuals" "Residuals.preservation1".

simple induction 1; simple induction T; intros; inversion UVT;
auto with arith.
rewrite (max_false b); auto with arith.
inversion H8; auto with arith.
Qed.

Lemma preservation :
forall U V W UV : redexes,
union U V W -> residuals U V UV -> residuals W V UV.
Proof. hammer_hook "Residuals" "Residuals.preservation".
intros; apply preservation1 with U; auto with arith.
Qed.

Lemma mutual_residuals_comp :
forall (W U UW : redexes) (RU : residuals U W UW)
(V VW : redexes) (RV : residuals V W VW), comp UW VW.
Proof. hammer_hook "Residuals" "Residuals.mutual_residuals_comp".
simple induction W.
intros; inversion_clear RU; inversion_clear RV; trivial with arith.
intros; inversion_clear RU; inversion_clear RV; apply Comp_Fun;
apply H with U0 U1; auto with arith.
simple induction b; intros; generalize RU H; inversion_clear RV.
intro RU1; inversion_clear RU1; intros.
apply subst_preserve_comp.
cut (comp (Fun W0) (Fun W1)).
intro CF; inversion_clear CF; trivial with arith.
apply H5 with (Fun U0) (Fun U1); auto with arith.
apply H0 with U3 U2; auto with arith.
intros; inversion_clear RU; apply Comp_Ap.
apply H with U0 U1; auto with arith.
apply H0 with U3 U2; auto with arith.
Qed.



Lemma residuals_regular :
forall U V W : redexes, residuals U V W -> regular V.
Proof. hammer_hook "Residuals" "Residuals.residuals_regular".
simple induction 1; simpl in |- *; auto with arith.
Qed.



Lemma residuals_intro :
forall U V : redexes,
comp U V -> regular V -> exists W : redexes, residuals U V W.
Proof. hammer_hook "Residuals" "Residuals.residuals_intro".
simple induction 1; simpl in |- *.
intro n; exists (Var n); trivial with arith.
intros U0 V0 C E O; elim (E O); intros W0 R; exists (Fun W0); auto with arith.
simple induction b2.
generalize H1; elim H0; try contradiction.
intros; elim H7; intros H8 H9; elim (H6 H8); intros FW0 R.
inversion_clear R.
elim (H3 H9); intros W2 R2.
eapply ex_intro. eapply Res_redex.
apply H10.
apply R2.
simple induction 1; intros O1 O2; elim (H1 O1); intro W1; elim (H3 O2);
intro W2.
intros; exists (Ap b1 W1 W2); auto with arith.
Qed.



Lemma residuals_preserve_regular :
forall U V W : redexes, residuals U V W -> regular U -> regular W.
Proof. hammer_hook "Residuals" "Residuals.residuals_preserve_regular".
simple induction 1; simpl in |- *; auto with arith.
simple induction b.
generalize H1; elim H0; try contradiction.
intros; elim H7; split; auto with arith.
simple induction 1; split; auto with arith.
simple induction b; intros; apply subst_preserve_regular; elim H4;
auto with arith.
Qed.
