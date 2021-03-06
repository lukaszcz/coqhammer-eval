From Hammer Require Import Hammer.









































Require Import Arith.
From Lambda Require Import Test.
From Lambda Require Import Terms.


Inductive red1 : lambda -> lambda -> Prop :=
| beta : forall M N : lambda, red1 (App (Abs M) N) (subst N M)
| abs_red : forall M N : lambda, red1 M N -> red1 (Abs M) (Abs N)
| app_red_l :
forall M1 N1 : lambda,
red1 M1 N1 -> forall M2 : lambda, red1 (App M1 M2) (App N1 M2)
| app_red_r :
forall M2 N2 : lambda,
red1 M2 N2 -> forall M1 : lambda, red1 (App M1 M2) (App M1 N2).


Inductive red : lambda -> lambda -> Prop :=
| one_step_red : forall M N : lambda, red1 M N -> red M N
| refl_red : forall M : lambda, red M M
| trans_red : forall M N P : lambda, red M N -> red N P -> red M P.

Lemma red_abs : forall M M' : lambda, red M M' -> red (Abs M) (Abs M').
Proof. hammer_hook "Reduction" "Reduction.red_abs".
simple induction 1; intros.
apply one_step_red; apply abs_red; trivial.
apply refl_red.
apply trans_red with (Abs N); trivial.
Qed.

Lemma red_appl :
forall M M' : lambda,
red M M' -> forall N : lambda, red (App M N) (App M' N).
Proof. hammer_hook "Reduction" "Reduction.red_appl".
simple induction 1; intros.
apply one_step_red; apply app_red_l; trivial.
apply refl_red.
apply trans_red with (App N N0); trivial.
Qed.

Lemma red_appr :
forall M M' : lambda,
red M M' -> forall N : lambda, red (App N M) (App N M').
Proof. hammer_hook "Reduction" "Reduction.red_appr".
simple induction 1; intros.
apply one_step_red; apply app_red_r; trivial.
apply refl_red.
apply trans_red with (App N0 N); trivial.
Qed.

Lemma red_app :
forall M M' N N' : lambda, red M M' -> red N N' -> red (App M N) (App M' N').
Proof. hammer_hook "Reduction" "Reduction.red_app".
intros; apply trans_red with (App M' N).
apply red_appl; trivial.
apply red_appr; trivial.
Qed.

Lemma red_beta :
forall M M' N N' : lambda,
red M M' -> red N N' -> red (App (Abs M) N) (subst N' M').
Proof. hammer_hook "Reduction" "Reduction.red_beta".
intros; apply trans_red with (App (Abs M') N').
apply red_app; trivial.
apply red_abs; trivial.
apply one_step_red; apply beta.
Qed.


Inductive par_red1 : lambda -> lambda -> Prop :=
| par_beta :
forall M M' : lambda,
par_red1 M M' ->
forall N N' : lambda,
par_red1 N N' -> par_red1 (App (Abs M) N) (subst N' M')
| ref_par_red : forall n : nat, par_red1 (Ref n) (Ref n)
| abs_par_red :
forall M M' : lambda, par_red1 M M' -> par_red1 (Abs M) (Abs M')
| app_par_red :
forall M M' : lambda,
par_red1 M M' ->
forall N N' : lambda, par_red1 N N' -> par_red1 (App M N) (App M' N').

Hint Resolve par_beta ref_par_red abs_par_red app_par_red.

Lemma refl_par_red1 : forall M : lambda, par_red1 M M.
Proof. hammer_hook "Reduction" "Reduction.refl_par_red1".
simple induction M; auto.
Qed.

Hint Resolve refl_par_red1.

Lemma red1_par_red1 : forall M N : lambda, red1 M N -> par_red1 M N.
Proof. hammer_hook "Reduction" "Reduction.red1_par_red1".
simple induction 1; auto.
Qed.



Inductive par_red : lambda -> lambda -> Prop :=
| one_step_par_red : forall M N : lambda, par_red1 M N -> par_red M N
| trans_par_red :
forall M N P : lambda, par_red M N -> par_red N P -> par_red M P.




Lemma red_par_red : forall M N : lambda, red M N -> par_red M N.
Proof. hammer_hook "Reduction" "Reduction.red_par_red".
simple induction 1; intros.
apply one_step_par_red; apply red1_par_red1; trivial.
apply one_step_par_red; auto.
apply trans_par_red with N0; trivial.
Qed.

Lemma par_red_red : forall M N : lambda, par_red M N -> red M N.
Proof. hammer_hook "Reduction" "Reduction.par_red_red".
simple induction 1.
2: intros; apply trans_red with N0; trivial.
simple induction 1.
intros; apply red_beta; trivial.
intros; apply refl_red.
intros; apply red_abs; trivial.
intros; apply red_app; trivial.
Qed.
