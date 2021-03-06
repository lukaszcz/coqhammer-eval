From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Integers.
From compcert Require Import AST.
From compcert Require Import Linking.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Events.
From compcert Require Import Globalenvs.
From compcert Require Import Smallstep.
From compcert Require Import Op.
From compcert Require Import Registers.
From compcert Require Import RTL.
From compcert Require Import Conventions.
From compcert Require Import Tailcall.







Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
{struct n}: nat :=
match n with
| O => O
| S n' =>
match c!pc with
| Some(Inop s) => S(return_measure_rec n' c s)
| Some(Iop op args dst s) => S(return_measure_rec n' c s)
| _ => O
end
end.

Definition return_measure (c: code) (pc: node) :=
return_measure_rec niter c pc.

Lemma return_measure_bounds:
forall f pc, (return_measure f pc <= niter)%nat.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.return_measure_bounds".
intro f.
assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
induction n; intros; simpl.
omega.
destruct (f!pc); try omega.
destruct i; try omega.
generalize (IHn n0). omega.
generalize (IHn n0). omega.
intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
forall f n1 n2 pc,
(n1 <= n2)%nat ->
(return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.return_measure_rec_incr".
induction n1; intros; simpl.
omega.
destruct n2. omegaContradiction. assert (n1 <= n2)%nat by omega.
simpl. destruct f!pc; try omega. destruct i; try omega.
generalize (IHn1 n2 n H0). omega.
generalize (IHn1 n2 n H0). omega.
Qed.

Lemma is_return_measure_rec:
forall f n n' pc r,
is_return n f pc r = true -> (n <= n')%nat ->
return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.is_return_measure_rec".
induction n; simpl; intros.
congruence.
destruct n'. omegaContradiction. simpl.
destruct (fn_code f)!pc; try congruence.
destruct i; try congruence.
decEq. apply IHn with r. auto. omega.
destruct (is_move_operation o l); try congruence.
destruct (Reg.eq r r1); try congruence.
decEq. apply IHn with r0. auto. omega.
Qed.





Inductive is_return_spec (f:function): node -> reg -> Prop :=
| is_return_none: forall pc r,
f.(fn_code)!pc = Some(Ireturn None) ->
is_return_spec f pc r
| is_return_some: forall pc r,
f.(fn_code)!pc = Some(Ireturn (Some r)) ->
is_return_spec f pc r
| is_return_nop: forall pc r s,
f.(fn_code)!pc = Some(Inop s) ->
is_return_spec f s r ->
(return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
is_return_spec f pc r
| is_return_move: forall pc r r' s,
f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
is_return_spec f s r' ->
(return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
is_return_spec f pc r.

Lemma is_return_charact:
forall f n pc rret,
is_return n f pc rret = true -> (n <= niter)%nat ->
is_return_spec f pc rret.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.is_return_charact".
induction n; intros.
simpl in H. congruence.
generalize H. simpl.
caseEq ((fn_code f)!pc); try congruence.
intro i. caseEq i; try congruence.
intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. omega.
unfold return_measure.
rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
rewrite <- (is_return_measure_rec f n niter s rret); auto.
simpl. rewrite H2. omega. omega.

intros op args dst s EQ1 EQ2.
caseEq (is_move_operation op args); try congruence.
intros src IMO. destruct (Reg.eq rret src); try congruence.
subst rret. intro.
exploit is_move_operation_correct; eauto. intros [A B]. subst.
eapply is_return_move; eauto. eapply IHn; eauto. omega.
unfold return_measure.
rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
rewrite <- (is_return_measure_rec f n niter s dst); auto.
simpl. rewrite EQ2. omega. omega.

intros or EQ1 EQ2. destruct or; intros.
assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
apply is_return_some; auto.
apply is_return_none; auto.
Qed.



Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
| transf_instr_tailcall: forall sig ros args res s,
f.(fn_stacksize) = 0 ->
is_return_spec f s res ->
transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
| transf_instr_default: forall i,
transf_instr_spec f i i.

Lemma transf_instr_charact:
forall f pc instr,
f.(fn_stacksize) = 0 ->
transf_instr_spec f instr (transf_instr f pc instr).
Proof. hammer_hook "Tailcallproof" "Tailcallproof.transf_instr_charact".
intros. unfold transf_instr. destruct instr; try constructor.
caseEq (is_return niter f n r && tailcall_is_possible s &&
opt_typ_eq (sig_res s) (sig_res (fn_sig f))); intros.
destruct (andb_prop _ _ H0). destruct (andb_prop _ _ H1).
eapply transf_instr_tailcall; eauto.
eapply is_return_charact; eauto.
constructor.
Qed.

Lemma transf_instr_lookup:
forall f pc i,
f.(fn_code)!pc = Some i ->
exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.transf_instr_lookup".
intros. unfold transf_function.
destruct (zeq (fn_stacksize f) 0).
simpl. rewrite PTree.gmap. rewrite H. simpl.
exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
exists i; split. auto. constructor.
Qed.







Lemma regs_lessdef_init_regs:
forall params vl vl',
Val.lessdef_list vl vl' ->
regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof. hammer_hook "Tailcallproof" "Tailcallproof.regs_lessdef_init_regs".
induction params; intros.
simpl. red; intros. rewrite Regmap.gi. constructor.
simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
apply set_reg_lessdef. auto. auto.
Qed.



Definition match_prog (p tp: RTL.program) :=
match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
forall p, match_prog p (transf_program p).
Proof. hammer_hook "Tailcallproof" "Tailcallproof.transf_program_match".
intros. apply match_transform_program; auto.
Qed.

Section PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.symbols_preserved". exact ((Genv.find_symbol_transf TRANSL)). Qed.

Lemma functions_translated:
forall (v: val) (f: RTL.fundef),
Genv.find_funct ge v = Some f ->
Genv.find_funct tge v = Some (transf_fundef f).
Proof. hammer_hook "Tailcallproof" "Tailcallproof.functions_translated". exact ((Genv.find_funct_transf TRANSL)). Qed.

Lemma funct_ptr_translated:
forall (b: block) (f: RTL.fundef),
Genv.find_funct_ptr ge b = Some f ->
Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof. hammer_hook "Tailcallproof" "Tailcallproof.funct_ptr_translated". exact ((Genv.find_funct_ptr_transf TRANSL)). Qed.

Lemma senv_preserved:
Senv.equiv ge tge.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.senv_preserved". exact ((Genv.senv_transf TRANSL)). Qed.

Lemma sig_preserved:
forall f, funsig (transf_fundef f) = funsig f.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.sig_preserved".
destruct f; auto. simpl. unfold transf_function.
destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.stacksize_preserved".
unfold transf_function. intros.
destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
forall ros rs rs' f,
find_function ge ros rs = Some f ->
regs_lessdef rs rs' ->
find_function tge ros rs' = Some (transf_fundef f).
Proof. hammer_hook "Tailcallproof" "Tailcallproof.find_function_translated".
intros until f; destruct ros; simpl.
intros.
assert (rs'#r = rs#r).
exploit Genv.find_funct_inv; eauto. intros [b EQ].
generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
rewrite H1. apply functions_translated; auto.
rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
apply funct_ptr_translated; auto.
discriminate.
Qed.



Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
| match_stackframes_nil:
match_stackframes nil nil
| match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
match_stackframes stk stk' ->
regs_lessdef rs rs' ->
match_stackframes
(Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
(Stackframe res (transf_function f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
| match_stackframes_tail: forall stk stk' res sp pc rs f,
match_stackframes stk stk' ->
is_return_spec f pc res ->
f.(fn_stacksize) = 0 ->
match_stackframes
(Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
stk'.



Inductive match_states: state -> state -> Prop :=
| match_states_normal:
forall s sp pc rs m s' rs' m' f
(STACKS: match_stackframes s s')
(RLD: regs_lessdef rs rs')
(MLD: Mem.extends m m'),
match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
(State s' (transf_function f) (Vptr sp Ptrofs.zero) pc rs' m')
| match_states_call:
forall s f args m s' args' m',
match_stackframes s s' ->
Val.lessdef_list args args' ->
Mem.extends m m' ->
match_states (Callstate s f args m)
(Callstate s' (transf_fundef f) args' m')
| match_states_return:
forall s v m s' v' m',
match_stackframes s s' ->
Val.lessdef v v' ->
Mem.extends m m' ->
match_states (Returnstate s v m)
(Returnstate s' v' m')
| match_states_interm:
forall s sp pc rs m s' m' f r v'
(STACKS: match_stackframes s s')
(MLD: Mem.extends m m'),
is_return_spec f pc r ->
f.(fn_stacksize) = 0 ->
Val.lessdef (rs#r) v' ->
match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
(Returnstate s' v' m').



Definition measure (st: state) : nat :=
match st with
| State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
| Callstate s f args m => 0%nat
| Returnstate s v m => (List.length s * (niter + 2))%nat
end.

Ltac TransfInstr :=
match goal with
| H: (PTree.get _ (fn_code _) = _) |- _ =>
destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
end.

Ltac EliminatedInstr :=
match goal with
| H: (is_return_spec _ _ _) |- _ => inv H; try congruence
| _ => idtac
end.



Lemma transf_step_correct:
forall s1 t s2, step ge s1 t s2 ->
forall s1' (MS: match_states s1 s1'),
(exists s2', step tge s1' t s2' /\ match_states s2 s2')
\/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.transf_step_correct".
induction 1; intros; inv MS; EliminatedInstr.

-
TransfInstr. left. econstructor; split.
eapply exec_Inop; eauto. constructor; auto.
-
assert (s0 = pc') by congruence. subst s0.
right. split. simpl. omega. split. auto.
econstructor; eauto.

-
TransfInstr.
assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
exploit eval_operation_lessdef; eauto.
intros [v' [EVAL' VLD]].
left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#res <- v') m'); split.
eapply exec_Iop; eauto.  rewrite <- EVAL'.
apply eval_operation_preserved. exact symbols_preserved.
econstructor; eauto. apply set_reg_lessdef; auto.
-
rewrite H1 in H. clear H1. inv H.
right. split. simpl. omega. split. auto.
econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

-
TransfInstr.
assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
exploit eval_addressing_lessdef; eauto.
intros [a' [ADDR' ALD]].
exploit Mem.loadv_extends; eauto.
intros [v' [LOAD' VLD]].
left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
apply eval_addressing_preserved. exact symbols_preserved. eauto.
econstructor; eauto. apply set_reg_lessdef; auto.

-
TransfInstr.
assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
exploit eval_addressing_lessdef; eauto.
intros [a' [ADDR' ALD]].
exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.
intros [m'1 [STORE' MLD']].
left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'1); split.
eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
apply eval_addressing_preserved. exact symbols_preserved. eauto.
destruct a; simpl in H1; try discriminate.
econstructor; eauto.

-
exploit find_function_translated; eauto. intro FIND'.
TransfInstr.
+
assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7.
red; intros; omegaContradiction.
destruct X as [m'' FREE].
left. exists (Callstate s' (transf_fundef fd) (rs'##args) m''); split.
eapply exec_Itailcall; eauto. apply sig_preserved.
constructor. eapply match_stackframes_tail; eauto. apply regs_lessdef_regs; auto.
eapply Mem.free_right_extends; eauto.
rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
+
left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' :: s')
(transf_fundef fd) (rs'##args) m'); split.
eapply exec_Icall; eauto. apply sig_preserved.
constructor. constructor; auto. apply regs_lessdef_regs; auto. auto.

-
exploit find_function_translated; eauto. intro FIND'.
exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
TransfInstr.
left. exists (Callstate s' (transf_fundef fd) (rs'##args) m'1); split.
eapply exec_Itailcall; eauto. apply sig_preserved.
rewrite stacksize_preserved; auto.
constructor. auto.  apply regs_lessdef_regs; auto. auto.

-
TransfInstr.
exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
intros (vargs' & P & Q).
exploit external_call_mem_extends; eauto.
intros [v' [m'1 [A [B [C D]]]]].
left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res v' rs') m'1); split.
eapply exec_Ibuiltin; eauto.
eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
eapply external_call_symbols_preserved; eauto. apply senv_preserved.
econstructor; eauto. apply set_res_lessdef; auto.

-
TransfInstr.
left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
eapply exec_Icond; eauto.
apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
constructor; auto.

-
TransfInstr.
left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
eapply exec_Ijumptable; eauto.
generalize (RLD arg). rewrite H0. intro. inv H2. auto.
constructor; auto.

-
exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
TransfInstr.
left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
constructor. auto.
destruct or; simpl. apply RLD. constructor.
auto.

-
assert (or = None) by congruence. subst or.
right. split. simpl. omega. split. auto.
constructor. auto.
simpl. constructor.
eapply Mem.free_left_extends; eauto.

-
assert (or = Some r) by congruence. subst or.
right. split. simpl. omega. split. auto.
constructor. auto.
simpl. auto.
eapply Mem.free_left_extends; eauto.

-
exploit Mem.alloc_extends; eauto.
instantiate (1 := 0). omega.
instantiate (1 := fn_stacksize f). omega.
intros [m'1 [ALLOC EXT]].
assert (fn_stacksize (transf_function f) = fn_stacksize f /\
fn_entrypoint (transf_function f) = fn_entrypoint f /\
fn_params (transf_function f) = fn_params f).
unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
destruct H0 as [EQ1 [EQ2 EQ3]].
left. econstructor; split.
simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
rewrite EQ2. rewrite EQ3. constructor; auto.
apply regs_lessdef_init_regs. auto.

-
exploit external_call_mem_extends; eauto.
intros [res' [m2' [A [B [C D]]]]].
left. exists (Returnstate s' res' m2'); split.
simpl. econstructor; eauto.
eapply external_call_symbols_preserved; eauto. apply senv_preserved.
constructor; auto.

-
inv H2.
+
left. econstructor; split.
apply exec_return.
constructor; auto. apply set_reg_lessdef; auto.
+
right. split. unfold measure. simpl length.
change (S (length s) * (niter + 2))%nat
with ((niter + 2) + (length s) * (niter + 2))%nat.
generalize (return_measure_bounds (fn_code f) pc). omega.
split. auto.
econstructor; eauto.
rewrite Regmap.gss. auto.
Qed.

Lemma transf_initial_states:
forall st1, initial_state prog st1 ->
exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.transf_initial_states".
intros. inv H.
exploit funct_ptr_translated; eauto. intro FIND.
exists (Callstate nil (transf_fundef f) nil m0); split.
econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto.
replace (prog_main tprog) with (prog_main prog).
rewrite symbols_preserved. eauto.
symmetry; eapply match_program_main; eauto.
rewrite <- H3. apply sig_preserved.
constructor. constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
forall st1 st2 r,
match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof. hammer_hook "Tailcallproof" "Tailcallproof.transf_final_states".
intros. inv H0. inv H. inv H5. inv H3. constructor.
Qed.




Theorem transf_program_correct:
forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof. hammer_hook "Tailcallproof" "Tailcallproof.transf_program_correct".
eapply forward_simulation_opt with (measure := measure); eauto.
apply senv_preserved.
eexact transf_initial_states.
eexact transf_final_states.
exact transf_step_correct.
Qed.

End PRESERVATION.

