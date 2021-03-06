From Hammer Require Import Hammer.







































Require Import Arith.
From Lambda Require Import Terms.
From Lambda Require Import Reduction.
From Lambda Require Import Redexes.
From Lambda Require Import Test.
From Lambda Require Import Marks.
From Lambda Require Import Substitution.
From Lambda Require Import Residuals.
From Lambda Require Import Simulation.
From Lambda Require Import Cube.



Definition confluence (A : Set) (R : A -> A -> Prop) :=
forall x y : A,
R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.


Lemma lemma1 : confluence lambda par_red -> confluence lambda red.
Proof. hammer_hook "Confluence" "Confluence.lemma1".
unfold all, confluence in |- *; intros.
cut (exists u : lambda, par_red y u /\ par_red z u).
simple induction 1.
intros u C; exists u; elim C; intros; split; apply par_red_red;
trivial with arith.
apply H with x; apply red_par_red; trivial with arith.
Qed.




Definition strip :=
forall x y : lambda,
par_red x y ->
forall z : lambda,
par_red1 x z -> exists u : lambda, par_red1 y u /\ par_red z u.

Lemma strip_lemma_r : confluence lambda par_red1 -> strip.
Proof. hammer_hook "Confluence" "Confluence.strip_lemma_r".
unfold strip in |- *; simple induction 2; intros.
elim H with M N z; trivial with arith.
intros u C; exists u; elim C; intros; split; trivial with arith.
apply one_step_par_red; trivial with arith.
elim (H2 z H5); intros.
elim H6; intros.
elim (H4 x0 H7); intros.
elim H9; intros.
exists x1; split; trivial with arith.
apply trans_par_red with x0; trivial with arith.
Qed.

Lemma strip_lemma_l : strip -> confluence lambda par_red.
Proof. hammer_hook "Confluence" "Confluence.strip_lemma_l".
unfold confluence in |- *; simple induction 2; intros.
elim (H M z H2 N H1).
intros u C; exists u; elim C; intros; split; trivial with arith.
apply one_step_par_red; trivial with arith.
elim (H2 z H5); intros.
elim H6; intros.
elim (H4 x0 H7); intros.
elim H9; intros.
exists x1; split; trivial with arith.
apply trans_par_red with x0; trivial with arith.
Qed.

Lemma lemma2 : confluence lambda par_red1 -> confluence lambda par_red.
Proof. hammer_hook "Confluence" "Confluence.lemma2".
intro C; unfold confluence in |- *; intros.
apply (strip_lemma_l (strip_lemma_r C) x); trivial with arith.
Qed.





Lemma parallel_moves : confluence lambda par_red1.
Proof. hammer_hook "Confluence" "Confluence.parallel_moves".
red in |- *; intros M N R1 P R2.
elim (simulation M N); trivial with arith.
elim (simulation M P); trivial with arith.
intros V RV U RU.
elim (paving U V (mark M) (mark N) (mark P)); trivial with arith.
intros UV C1; elim C1.
intros VU C2; elim C2.
intros UVW C3; elim C3; intros P1 P2.
exists (unmark UVW); split.
rewrite (inverse N).
apply Simulation.completeness with VU; trivial with arith.
rewrite (inverse P).
apply Simulation.completeness with UV; trivial with arith.
Qed.

Lemma confluence_parallel_reduction : confluence lambda par_red.
Proof. hammer_hook "Confluence" "Confluence.confluence_parallel_reduction".
apply lemma2; exact parallel_moves.
Qed.

Theorem confluence_beta_reduction : confluence lambda red.
Proof. hammer_hook "Confluence" "Confluence.confluence_beta_reduction".
apply lemma1; exact confluence_parallel_reduction.
Qed.
