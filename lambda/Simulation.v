From Hammer Require Import Hammer.









































Require Import Arith.
From Lambda Require Import Terms.
From Lambda Require Import Reduction.
From Lambda Require Import Redexes.
From Lambda Require Import Test.
From Lambda Require Import Marks.
From Lambda Require Import Substitution.
From Lambda Require Import Residuals.



Lemma mark_lift_rec :
forall (M : lambda) (n k : nat),
lift_rec_r (mark M) k n = mark (lift_rec M k n).
Proof. hammer_hook "Simulation" "Simulation.mark_lift_rec".
simple induction M; simpl in |- *; intros.
elim (test k n); simpl in |- *; intros; trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma mark_lift :
forall (M : lambda) (n : nat), lift_r n (mark M) = mark (lift n M).
Proof. hammer_hook "Simulation" "Simulation.mark_lift".
unfold lift in |- *; unfold lift_r in |- *; intros; apply mark_lift_rec.
Qed.

Lemma mark_subst_rec :
forall (N M : lambda) (n : nat),
subst_rec_r (mark M) (mark N) n = mark (subst_rec M N n).
Proof. hammer_hook "Simulation" "Simulation.mark_subst_rec".
simple induction M; simpl in |- *; intros.
unfold insert_Var, insert_Ref in |- *.
elim (compare n0 n); intro H.
elim H; intro H'.
simpl in |- *; trivial.
rewrite (mark_lift N n0); trivial.
simpl in |- *; trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma mark_subst :
forall M N : lambda, subst_r (mark M) (mark N) = mark (subst M N).
Proof. hammer_hook "Simulation" "Simulation.mark_subst".
unfold subst in |- *; unfold subst_r in |- *; intros; apply mark_subst_rec.
Qed.



Lemma simulation :
forall M M' : lambda,
par_red1 M M' -> exists V : redexes, residuals (mark M) V (mark M').
Proof. hammer_hook "Simulation" "Simulation.simulation".
simple induction 1; simpl in |- *; intros.
elim H1; intros V1 P1.
elim H3; intros V2 P2.
exists (Ap true (Fun V1) V2).
elim mark_subst; auto.
exists (Var n); trivial.
elim H1; intros V1 P1.
exists (Fun V1); auto.
elim H1; intros V1 P1.
elim H3; intros V2 P2.
exists (Ap false V1 V2); auto.
Qed.



Lemma unmark_lift_rec :
forall (U : redexes) (n k : nat),
lift_rec (unmark U) k n = unmark (lift_rec_r U k n).
Proof. hammer_hook "Simulation" "Simulation.unmark_lift_rec".
simple induction U; simpl in |- *; intros.
elim (test k n); trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma unmark_lift :
forall (U : redexes) (n : nat), lift n (unmark U) = unmark (lift_r n U).
Proof. hammer_hook "Simulation" "Simulation.unmark_lift".
unfold lift in |- *; unfold lift_r in |- *; intros; apply unmark_lift_rec.
Qed.

Lemma unmark_subst_rec :
forall (V U : redexes) (n : nat),
subst_rec (unmark U) (unmark V) n = unmark (subst_rec_r U V n).
Proof. hammer_hook "Simulation" "Simulation.unmark_subst_rec".
simple induction U; simpl in |- *; intros.
unfold insert_Var, insert_Ref in |- *.
elim (compare n0 n); intro H; simpl in |- *; trivial.
elim H; trivial.
rewrite (unmark_lift V n0); trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma unmark_subst :
forall U V : redexes, subst (unmark U) (unmark V) = unmark (subst_r U V).
Proof. hammer_hook "Simulation" "Simulation.unmark_subst".
unfold subst in |- *; unfold subst_r in |- *; intros; apply unmark_subst_rec.
Qed.

Lemma completeness :
forall U V W : redexes, residuals U V W -> par_red1 (unmark U) (unmark W).
Proof. hammer_hook "Simulation" "Simulation.completeness".
simple induction 1; simpl in |- *; auto.
intros; elim unmark_subst; auto.
Qed.






Definition reduction (M : lambda) (U : redexes) (N : lambda) :=
residuals (mark M) U (mark N).

Lemma reduction_function :
forall (M N P : lambda) (U : redexes),
reduction M U N -> reduction M U P -> N = P.
Proof. hammer_hook "Simulation" "Simulation.reduction_function".
unfold reduction in |- *; intros; cut (comp (mark N) (mark P)).
intro; rewrite (inverse N); rewrite (inverse P); apply comp_unmark_eq;
trivial.
apply mutual_residuals_comp with U (mark M) (mark M); trivial.
Qed.
