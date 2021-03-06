From Hammer Require Import Hammer.







































From Lambda Require Import Terms.
From Lambda Require Import Reduction.
From Lambda Require Import Confluence.

Inductive conv1 : lambda -> lambda -> Prop :=
| red1_conv : forall M N : lambda, red1 M N -> conv1 M N
| exp1_conv : forall M N : lambda, red1 N M -> conv1 M N.


Inductive conv : lambda -> lambda -> Prop :=
| one_step_conv : forall M N : lambda, conv1 M N -> conv M N
| refl_conv : forall M : lambda, conv M M
| trans_conv : forall M N P : lambda, conv M N -> conv N P -> conv M P.

Lemma sym_conv : forall M N : lambda, conv M N -> conv N M.
Proof. hammer_hook "Conversion" "Conversion.sym_conv".
simple induction 1.
simple induction 1; intros; apply one_step_conv.
apply exp1_conv; trivial.
apply red1_conv; trivial.
intro; apply refl_conv; trivial.
intros; apply trans_conv with N0; trivial.
Qed.

From Lambda Require Import Confluence.

Theorem Church_Rosser :
forall M N : lambda, conv M N -> exists P : lambda, red M P /\ red N P.
Proof. hammer_hook "Conversion" "Conversion.Church_Rosser".
simple induction 1.
simple induction 1; intros.
exists N1; split; [ apply one_step_red; trivial | apply refl_red; trivial ].
exists M1; split; [ apply refl_red; trivial | apply one_step_red; trivial ].
intro M0; exists M0; split; apply refl_red; trivial.
intros; elim H1; intros P0 C0; elim H3; intros P1 C1; elim C0; elim C1;
intros.
elim confluence_beta_reduction with N0 P0 P1; trivial.
intros Q C3; exists Q; elim C3; split.
apply trans_red with P0; trivial.
apply trans_red with P1; trivial.
Qed.
