From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Postorder.
From compcert Require Import AST.
From compcert Require Import Linking.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Events.
From compcert Require Import Smallstep.
From compcert Require Import Op.
From compcert Require Import Registers.
From compcert Require Import RTL.
From compcert Require Import Renumber.

Definition match_prog (p tp: RTL.program) :=
match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
forall p, match_prog p (transf_program p).
Proof. hammer_hook "Renumberproof" "Renumberproof.transf_program_match".
intros. eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
forall v f,
Genv.find_funct ge v = Some f ->
Genv.find_funct tge v = Some (transf_fundef f).
Proof. hammer_hook "Renumberproof" "Renumberproof.functions_translated". exact ((Genv.find_funct_transf TRANSL)). Qed.

Lemma function_ptr_translated:
forall v f,
Genv.find_funct_ptr ge v = Some f ->
Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. hammer_hook "Renumberproof" "Renumberproof.function_ptr_translated". exact ((Genv.find_funct_ptr_transf TRANSL)). Qed.

Lemma symbols_preserved:
forall id,
Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. hammer_hook "Renumberproof" "Renumberproof.symbols_preserved". exact ((Genv.find_symbol_transf TRANSL)). Qed.

Lemma senv_preserved:
Senv.equiv ge tge.
Proof. hammer_hook "Renumberproof" "Renumberproof.senv_preserved". exact ((Genv.senv_transf TRANSL)). Qed.

Lemma sig_preserved:
forall f, funsig (transf_fundef f) = funsig f.
Proof. hammer_hook "Renumberproof" "Renumberproof.sig_preserved".
destruct f; reflexivity.
Qed.

Lemma find_function_translated:
forall ros rs fd,
find_function ge ros rs = Some fd ->
find_function tge ros rs = Some (transf_fundef fd).
Proof. hammer_hook "Renumberproof" "Renumberproof.find_function_translated".
unfold find_function; intros. destruct ros as [r|id].
eapply functions_translated; eauto.
rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
eapply function_ptr_translated; eauto.
Qed.



Section RENUMBER.

Variable f: PTree.t positive.

Hypothesis f_inj: forall x1 x2 y, f!x1 = Some y -> f!x2 = Some y -> x1 = x2.

Lemma renum_cfg_nodes:
forall c x y i,
c!x = Some i -> f!x = Some y -> (renum_cfg f c)!y = Some(renum_instr f i).
Proof. hammer_hook "Renumberproof" "Renumberproof.renum_cfg_nodes".
set (P := fun (c c': code) =>
forall x y i, c!x = Some i -> f!x = Some y -> c'!y = Some(renum_instr f i)).
intros c0. change (P c0 (renum_cfg f c0)). unfold renum_cfg.
apply PTree_Properties.fold_rec; unfold P; intros.

eapply H0; eauto. rewrite H; auto.

rewrite PTree.gempty in H; congruence.

rewrite PTree.gsspec in H2. unfold renum_node. destruct (peq x k).
inv H2. rewrite H3. apply PTree.gss.
destruct f!k as [y'|] eqn:?.
rewrite PTree.gso. eauto. red; intros; subst y'. elim n. eapply f_inj; eauto.
eauto.
Qed.

End RENUMBER.

Definition pnum (f: function) := postorder (successors_map f) f.(fn_entrypoint).

Definition reach (f: function) (pc: node) := reachable (successors_map f) f.(fn_entrypoint) pc.

Lemma transf_function_at:
forall f pc i,
f.(fn_code)!pc = Some i ->
reach f pc ->
(transf_function f).(fn_code)!(renum_pc (pnum f) pc) = Some(renum_instr (pnum f) i).
Proof. hammer_hook "Renumberproof" "Renumberproof.transf_function_at".
intros.
destruct (postorder_correct (successors_map f) f.(fn_entrypoint)) as [A B].
fold (pnum f) in *.
unfold renum_pc. destruct (pnum f)! pc as [pc'|] eqn:?.
simpl. eapply renum_cfg_nodes; eauto.
elim (B pc); auto. unfold successors_map. rewrite PTree.gmap1. rewrite H. simpl. congruence.
Qed.

Ltac TR_AT :=
match goal with
| [ A: (fn_code _)!_ = Some _ , B: reach _ _ |- _ ] =>
generalize (transf_function_at _ _ _ A B); simpl renum_instr; intros
end.

Lemma reach_succ:
forall f pc i s,
f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
reach f pc -> reach f s.
Proof. hammer_hook "Renumberproof" "Renumberproof.reach_succ".
unfold reach; intros. econstructor; eauto.
unfold successors_map. rewrite PTree.gmap1. rewrite H. auto.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
| match_frames_intro: forall res f sp pc rs
(REACH: reach f pc),
match_frames (Stackframe res f sp pc rs)
(Stackframe res (transf_function f) sp (renum_pc (pnum f) pc) rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
| match_regular_states: forall stk f sp pc rs m stk'
(STACKS: list_forall2 match_frames stk stk')
(REACH: reach f pc),
match_states (State stk f sp pc rs m)
(State stk' (transf_function f) sp (renum_pc (pnum f) pc) rs m)
| match_callstates: forall stk f args m stk'
(STACKS: list_forall2 match_frames stk stk'),
match_states (Callstate stk f args m)
(Callstate stk' (transf_fundef f) args m)
| match_returnstates: forall stk v m stk'
(STACKS: list_forall2 match_frames stk stk'),
match_states (Returnstate stk v m)
(Returnstate stk' v m).

Lemma step_simulation:
forall S1 t S2, RTL.step ge S1 t S2 ->
forall S1', match_states S1 S1' ->
exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof. hammer_hook "Renumberproof" "Renumberproof.step_simulation".
induction 1; intros S1' MS; inv MS; try TR_AT.

econstructor; split. eapply exec_Inop; eauto.
constructor; auto. eapply reach_succ; eauto. simpl; auto.

econstructor; split.
eapply exec_Iop; eauto.
instantiate (1 := v). rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
constructor; auto. eapply reach_succ; eauto. simpl; auto.

econstructor; split.
assert (eval_addressing tge sp addr rs ## args = Some a).
rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
eapply exec_Iload; eauto.
constructor; auto. eapply reach_succ; eauto. simpl; auto.

econstructor; split.
assert (eval_addressing tge sp addr rs ## args = Some a).
rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
eapply exec_Istore; eauto.
constructor; auto. eapply reach_succ; eauto. simpl; auto.

econstructor; split.
eapply exec_Icall with (fd := transf_fundef fd); eauto.
eapply find_function_translated; eauto.
apply sig_preserved.
constructor. constructor; auto. constructor. eapply reach_succ; eauto. simpl; auto.

econstructor; split.
eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
eapply find_function_translated; eauto.
apply sig_preserved.
constructor. auto.

econstructor; split.
eapply exec_Ibuiltin; eauto.
eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
eapply external_call_symbols_preserved; eauto. apply senv_preserved.
constructor; auto. eapply reach_succ; eauto. simpl; auto.

econstructor; split.
eapply exec_Icond; eauto.
replace (if b then renum_pc (pnum f) ifso else renum_pc (pnum f) ifnot)
with (renum_pc (pnum f) (if b then ifso else ifnot)).
constructor; auto. eapply reach_succ; eauto. simpl. destruct b; auto.
destruct b; auto.

econstructor; split.
eapply exec_Ijumptable; eauto. rewrite list_nth_z_map. rewrite H1. simpl; eauto.
constructor; auto. eapply reach_succ; eauto. simpl. eapply list_nth_z_in; eauto.

econstructor; split.
eapply exec_Ireturn; eauto.
constructor; auto.

simpl. econstructor; split.
eapply exec_function_internal; eauto.
constructor; auto. unfold reach. constructor.

econstructor; split.
eapply exec_function_external; eauto.
eapply external_call_symbols_preserved; eauto. apply senv_preserved.
constructor; auto.

inv STACKS. inv H1.
econstructor; split.
eapply exec_return; eauto.
constructor; auto.
Qed.

Lemma transf_initial_states:
forall S1, RTL.initial_state prog S1 ->
exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof. hammer_hook "Renumberproof" "Renumberproof.transf_initial_states".
intros. inv H. econstructor; split.
econstructor.
eapply (Genv.init_mem_transf TRANSL); eauto.
rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
eapply function_ptr_translated; eauto.
rewrite <- H3; apply sig_preserved.
constructor. constructor.
Qed.

Lemma transf_final_states:
forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. hammer_hook "Renumberproof" "Renumberproof.transf_final_states".
intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Theorem transf_program_correct:
forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof. hammer_hook "Renumberproof" "Renumberproof.transf_program_correct".
eapply forward_simulation_step.
apply senv_preserved.
eexact transf_initial_states.
eexact transf_final_states.
exact step_simulation.
Qed.

End PRESERVATION.







