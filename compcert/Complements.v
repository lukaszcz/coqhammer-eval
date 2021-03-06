From Hammer Require Import Hammer.















Require Import Classical.
From compcert Require Import Coqlib.
From compcert Require Import Errors.
From compcert Require Import AST.
From compcert Require Import Linking.
From compcert Require Import Events.
From compcert Require Import Smallstep.
From compcert Require Import Behaviors.
From compcert Require Import Csyntax.
From compcert Require Import Csem.
From compcert Require Import Cstrategy.
From compcert Require Import Asm.
From compcert Require Import Compiler.





Theorem transf_c_program_preservation:
forall p tp beh,
transf_c_program p = OK tp ->
program_behaves (Asm.semantics tp) beh ->
exists beh', program_behaves (Csem.semantics p) beh' /\ behavior_improves beh' beh.
Proof. hammer_hook "Complements" "Complements.transf_c_program_preservation".
intros. eapply backward_simulation_behavior_improves; eauto.
apply transf_c_program_correct; auto.
Qed.



Theorem transf_c_program_is_refinement:
forall p tp,
transf_c_program p = OK tp ->
(forall beh, program_behaves (Csem.semantics p) beh -> not_wrong beh) ->
(forall beh, program_behaves (Asm.semantics tp) beh -> program_behaves (Csem.semantics p) beh).
Proof. hammer_hook "Complements" "Complements.transf_c_program_is_refinement".
intros. eapply backward_simulation_same_safe_behavior; eauto.
apply transf_c_program_correct; auto.
Qed.



Theorem transf_cstrategy_program_preservation:
forall p tp,
transf_c_program p = OK tp ->
(forall beh, program_behaves (Cstrategy.semantics p) beh ->
exists beh', program_behaves (Asm.semantics tp) beh' /\ behavior_improves beh beh')
/\(forall beh, program_behaves (Asm.semantics tp) beh ->
exists beh', program_behaves (Cstrategy.semantics p) beh' /\ behavior_improves beh' beh)
/\(forall beh, not_wrong beh ->
program_behaves (Cstrategy.semantics p) beh -> program_behaves (Asm.semantics tp) beh)
/\(forall beh,
(forall beh', program_behaves (Cstrategy.semantics p) beh' -> not_wrong beh') ->
program_behaves (Asm.semantics tp) beh ->
program_behaves (Cstrategy.semantics p) beh).
Proof. hammer_hook "Complements" "Complements.transf_cstrategy_program_preservation".
assert (WBT: forall p, well_behaved_traces (Cstrategy.semantics p)).
intros. eapply ssr_well_behaved. apply Cstrategy.semantics_strongly_receptive.
intros.
assert (MATCH: match_prog p tp) by (apply transf_c_program_match; auto).
intuition auto.
eapply forward_simulation_behavior_improves; eauto.
apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
exploit backward_simulation_behavior_improves.
apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
eauto.
intros [beh1 [A B]]. exists beh1; split; auto. rewrite atomic_behaviors; auto.
eapply forward_simulation_same_safe_behavior; eauto.
apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
exploit backward_simulation_same_safe_behavior.
apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
intros. rewrite <- atomic_behaviors in H2; eauto. eauto.
intros. rewrite atomic_behaviors; auto.
Qed.



Theorem bigstep_cstrategy_preservation:
forall p tp,
transf_c_program p = OK tp ->
(forall t r,
Cstrategy.bigstep_program_terminates p t r ->
program_behaves (Asm.semantics tp) (Terminates t r))
/\(forall T,
Cstrategy.bigstep_program_diverges p T ->
program_behaves (Asm.semantics tp) (Reacts T)
\/ exists t, program_behaves (Asm.semantics tp) (Diverges t) /\ traceinf_prefix t T).
Proof. hammer_hook "Complements" "Complements.bigstep_cstrategy_preservation".
intuition.
apply transf_cstrategy_program_preservation with p; auto. red; auto.
apply behavior_bigstep_terminates with (Cstrategy.bigstep_semantics p); auto.
apply Cstrategy.bigstep_semantics_sound.
exploit (behavior_bigstep_diverges (Cstrategy.bigstep_semantics_sound p)). eassumption.
intros [A | [t [A B]]].
left. apply transf_cstrategy_program_preservation with p; auto. red; auto.
right; exists t; split; auto. apply transf_cstrategy_program_preservation with p; auto. red; auto.
Qed.







Definition specification := program_behavior -> Prop.



Definition c_program_satisfies_spec (p: Csyntax.program) (spec: specification): Prop :=
forall beh,  program_behaves (Csem.semantics p) beh -> spec beh.
Definition asm_program_satisfies_spec (p: Asm.program) (spec: specification): Prop :=
forall beh,  program_behaves (Asm.semantics p) beh -> spec beh.



Definition safety_enforcing_specification (spec: specification): Prop :=
forall beh, spec beh -> not_wrong beh.



Theorem transf_c_program_preserves_spec:
forall p tp spec,
transf_c_program p = OK tp ->
safety_enforcing_specification spec ->
c_program_satisfies_spec p spec ->
asm_program_satisfies_spec tp spec.
Proof. hammer_hook "Complements" "Complements.transf_c_program_preserves_spec".
intros p tp spec TRANSF SES CSAT; red; intros beh AEXEC.
exploit transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
apply CSAT in CEXEC. destruct IMPR as [EQ | [t [A B]]].
- congruence.
- subst beh'. apply SES in CEXEC. contradiction.
Qed.



Definition c_program_has_initial_trace (p: Csyntax.program) (t: trace): Prop :=
forall beh, program_behaves (Csem.semantics p) beh -> behavior_prefix t beh.
Definition asm_program_has_initial_trace (p: Asm.program) (t: trace): Prop :=
forall beh, program_behaves (Asm.semantics p) beh -> behavior_prefix t beh.

Theorem transf_c_program_preserves_initial_trace:
forall p tp t,
transf_c_program p = OK tp ->
c_program_has_initial_trace p t ->
asm_program_has_initial_trace tp t.
Proof. hammer_hook "Complements" "Complements.transf_c_program_preserves_initial_trace".
intros p tp t TRANSF CTRACE; red; intros beh AEXEC.
exploit transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
apply CTRACE in CEXEC. destruct IMPR as [EQ | [t' [A B]]].
- congruence.
- destruct CEXEC as (beh1' & EQ').
destruct B as (beh1 & EQ).
subst beh'. destruct beh1'; simpl in A; inv A.
exists (behavior_app t0 beh1). apply behavior_app_assoc.
Qed.





Section SEPARATE_COMPILATION.


Variable c_units: nlist Csyntax.program.


Variable asm_units: nlist Asm.program.
Hypothesis separate_compilation_succeeds:
nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units.


Variable c_program: Csyntax.program.
Hypothesis source_linking: link_list c_units = Some c_program.


Lemma compiled_linking_succeeds:
{ asm_program | link_list asm_units = Some asm_program }.
Proof. hammer_hook "Complements" "Complements.compiled_linking_succeeds".
destruct (link_list asm_units) eqn:E.
- exists p; auto.
- exfalso.
exploit separate_transf_c_program_correct; eauto. intros (a & P & Q).
congruence.
Qed.


Let asm_program: Asm.program := proj1_sig compiled_linking_succeeds.
Let compiled_linking: link_list asm_units = Some asm_program := proj2_sig compiled_linking_succeeds.



Theorem separate_transf_c_program_preservation:
forall beh,
program_behaves (Asm.semantics asm_program) beh ->
exists beh', program_behaves (Csem.semantics c_program) beh' /\ behavior_improves beh' beh.
Proof. hammer_hook "Complements" "Complements.separate_transf_c_program_preservation".
intros. exploit separate_transf_c_program_correct; eauto. intros (a & P & Q).
assert (a = asm_program) by congruence. subst a.
eapply backward_simulation_behavior_improves; eauto.
Qed.



Theorem separate_transf_c_program_is_refinement:
(forall beh, program_behaves (Csem.semantics c_program) beh -> not_wrong beh) ->
(forall beh, program_behaves (Asm.semantics asm_program) beh -> program_behaves (Csem.semantics c_program) beh).
Proof. hammer_hook "Complements" "Complements.separate_transf_c_program_is_refinement".
intros. exploit separate_transf_c_program_preservation; eauto. intros (beh' & P & Q).
assert (not_wrong beh') by auto.
inv Q.
- auto.
- destruct H2 as (t & U & V). subst beh'. elim H1.
Qed.



Theorem separate_transf_c_program_preserves_spec:
forall spec,
safety_enforcing_specification spec ->
c_program_satisfies_spec c_program spec ->
asm_program_satisfies_spec asm_program spec.
Proof. hammer_hook "Complements" "Complements.separate_transf_c_program_preserves_spec".
intros spec SES CSAT; red; intros beh AEXEC.
exploit separate_transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
apply CSAT in CEXEC. destruct IMPR as [EQ | [t [A B]]].
- congruence.
- subst beh'. apply SES in CEXEC. contradiction.
Qed.



Theorem separate_transf_c_program_preserves_initial_trace:
forall t,
c_program_has_initial_trace c_program t ->
asm_program_has_initial_trace asm_program t.
Proof. hammer_hook "Complements" "Complements.separate_transf_c_program_preserves_initial_trace".
intros t CTRACE; red; intros beh AEXEC.
exploit separate_transf_c_program_preservation; eauto. intros (beh' & CEXEC & IMPR).
apply CTRACE in CEXEC. destruct IMPR as [EQ | [t' [A B]]].
- congruence.
- destruct CEXEC as (beh1' & EQ').
destruct B as (beh1 & EQ).
subst beh'. destruct beh1'; simpl in A; inv A.
exists (behavior_app t0 beh1). apply behavior_app_assoc.
Qed.

End SEPARATE_COMPILATION.
