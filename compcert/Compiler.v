From Hammer Require Import Hammer.
















Require Import String.
From compcert Require Import Coqlib.
From compcert Require Import Errors.
From compcert Require Import AST.
From compcert Require Import Linking.
From compcert Require Import Smallstep.

From compcert Require Ctypes.
From compcert Require Csyntax.
From compcert Require Csem.
From compcert Require Cstrategy.
From compcert Require Cexec.
From compcert Require Clight.
From compcert Require Csharpminor.
From compcert Require Cminor.
From compcert Require CminorSel.
From compcert Require RTL.
From compcert Require LTL.
From compcert Require Linear.
From compcert Require Mach.
From compcert Require Asm.

From compcert Require Initializers.
From compcert Require SimplExpr.
From compcert Require SimplLocals.
From compcert Require Cshmgen.
From compcert Require Cminorgen.
From compcert Require Selection.
From compcert Require RTLgen.
From compcert Require Tailcall.
From compcert Require Inlining.
From compcert Require Renumber.
From compcert Require Constprop.
From compcert Require CSE.
From compcert Require Deadcode.
From compcert Require Unusedglob.
From compcert Require Allocation.
From compcert Require Tunneling.
From compcert Require Linearize.
From compcert Require CleanupLabels.
From compcert Require Debugvar.
From compcert Require Stacking.
From compcert Require Asmgen.

From compcert Require SimplExprproof.
From compcert Require SimplLocalsproof.
From compcert Require Cshmgenproof.
From compcert Require Cminorgenproof.
From compcert Require Selectionproof.
From compcert Require RTLgenproof.
From compcert Require Tailcallproof.
From compcert Require Inliningproof.
From compcert Require Renumberproof.
From compcert Require Constpropproof.
From compcert Require CSEproof.
From compcert Require Deadcodeproof.
From compcert Require Unusedglobproof.
From compcert Require Allocproof.
From compcert Require Tunnelingproof.
From compcert Require Linearizeproof.
From compcert Require CleanupLabelsproof.
From compcert Require Debugvarproof.
From compcert Require Stackingproof.
From compcert Require Asmgenproof.

From compcert Require Import Compopts.


Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Local Open Scope string_scope.





Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
(x: res A) (f: A -> res B) : res B :=
match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
(apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
(apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
(flag: unit -> bool) (f: A -> A) (prog: A) : A :=
if flag tt then f prog else prog.

Definition partial_if {A: Type}
(flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
if flag tt then f prog else OK prog.



Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
OK f
@@ print (print_RTL 0)
@@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
@@ print (print_RTL 1)
@@@ time "Inlining" Inlining.transf_program
@@ print (print_RTL 2)
@@ time "Renumbering" Renumber.transf_program
@@ print (print_RTL 3)
@@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
@@ print (print_RTL 4)
@@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
@@ print (print_RTL 5)
@@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
@@ print (print_RTL 6)
@@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
@@ print (print_RTL 7)
@@@ time "Unused globals" Unusedglob.transform_program
@@ print (print_RTL 8)
@@@ time "Register allocation" Allocation.transf_program
@@ print print_LTL
@@ time "Branch tunneling" Tunneling.tunnel_program
@@@ time "CFG linearization" Linearize.transf_program
@@ time "Label cleanup" CleanupLabels.transf_program
@@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
@@@ time "Mach generation" Stacking.transf_program
@@ print print_Mach
@@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
OK p
@@ print print_Cminor
@@@ time "Instruction selection" Selection.sel_program
@@@ time "RTL generation" RTLgen.transl_program
@@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
OK p
@@ print print_Clight
@@@ time "Simplification of locals" SimplLocals.transf_program
@@@ time "C#minor generation" Cshmgen.transl_program
@@@ time "Cminor generation" Cminorgen.transl_program
@@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
OK p
@@@ time "Clight generation" SimplExpr.transl_program
@@@ transf_clight_program.



Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.



Lemma print_identity:
forall (A: Type) (printer: A -> unit) (prog: A),
print printer prog = prog.
Proof. hammer_hook "Compiler" "Compiler.print_identity".
intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
forall (A: Type) (x: res A) (f: A -> unit),
x @@ print f = x.
Proof. hammer_hook "Compiler" "Compiler.compose_print_identity".
intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.



Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
if flag tt then R else eq.

Lemma total_if_match:
forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
(forall p, rel p (f p)) ->
match_if flag rel prog (total_if flag f prog).
Proof. hammer_hook "Compiler" "Compiler.total_if_match".
intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
(forall p tp, f p = OK tp -> rel p tp) ->
partial_if flag f prog = OK tprog ->
match_if flag rel prog tprog.
Proof. hammer_hook "Compiler" "Compiler.partial_if_match".
intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
Qed.

Instance TransfIfLink {A: Type} {LA: Linker A}
(flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
: TransfLink (match_if flag transf).
Proof. hammer_hook "Compiler" "Compiler.TransfIfLink".
unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.



Local Open Scope linking_scope.

Definition CompCert's_passes :=
mkpass SimplExprproof.match_prog
::: mkpass SimplLocalsproof.match_prog
::: mkpass Cshmgenproof.match_prog
::: mkpass Cminorgenproof.match_prog
::: mkpass Selectionproof.match_prog
::: mkpass RTLgenproof.match_prog
::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
::: mkpass Inliningproof.match_prog
::: mkpass Renumberproof.match_prog
::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
::: mkpass Unusedglobproof.match_prog
::: mkpass Allocproof.match_prog
::: mkpass Tunnelingproof.match_prog
::: mkpass Linearizeproof.match_prog
::: mkpass CleanupLabelsproof.match_prog
::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
::: mkpass Stackingproof.match_prog
::: mkpass Asmgenproof.match_prog
::: pass_nil _.



Definition match_prog: Csyntax.program -> Asm.program -> Prop :=
pass_match (compose_passes CompCert's_passes).



Theorem transf_c_program_match:
forall p tp,
transf_c_program p = OK tp ->
match_prog p tp.
Proof. hammer_hook "Compiler" "Compiler.transf_c_program_match".
intros p tp T.
unfold transf_c_program, time in T. simpl in T.
destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
set (p9 := Renumber.transf_program p8) in *.
set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
set (p16 := Tunneling.tunnel_program p15) in *.
destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
set (p18 := CleanupLabels.transf_program p17) in *.
destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
unfold match_prog; simpl.
exists p1; split. apply SimplExprproof.transf_program_match; auto.
exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
exists p3; split. apply Cshmgenproof.transf_program_match; auto.
exists p4; split. apply Cminorgenproof.transf_program_match; auto.
exists p5; split. apply Selectionproof.transf_program_match; auto.
exists p6; split. apply RTLgenproof.transf_program_match; auto.
exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
exists p8; split. apply Inliningproof.transf_program_match; auto.
exists p9; split. apply Renumberproof.transf_program_match; auto.
exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
exists p14; split. apply Unusedglobproof.transf_program_match; auto.
exists p15; split. apply Allocproof.transf_program_match; auto.
exists p16; split. apply Tunnelingproof.transf_program_match.
exists p17; split. apply Linearizeproof.transf_program_match; auto.
exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
exists p20; split. apply Stackingproof.transf_program_match; auto.
exists tp; split. apply Asmgenproof.transf_program_match; auto.
reflexivity.
Qed.





Remark forward_simulation_identity:
forall sem, forward_simulation sem sem.
Proof. hammer_hook "Compiler" "Compiler.forward_simulation_identity".
intros. apply forward_simulation_step with (fun s1 s2 => s2 = s1); intros.
- auto.
- exists s1; auto.
- subst s2; auto.
- subst s2. exists s1'; auto.
Qed.

Lemma match_if_simulation:
forall (A: Type) (sem: A -> semantics) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
match_if flag transf prog tprog ->
(forall p tp, transf p tp -> forward_simulation (sem p) (sem tp)) ->
forward_simulation (sem prog) (sem tprog).
Proof. hammer_hook "Compiler" "Compiler.match_if_simulation".
intros. unfold match_if in *. destruct (flag tt). eauto. subst. apply forward_simulation_identity.
Qed.

Theorem cstrategy_semantic_preservation:
forall p tp,
match_prog p tp ->
forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)
/\ backward_simulation (atomic (Cstrategy.semantics p)) (Asm.semantics tp).
Proof. hammer_hook "Compiler" "Compiler.cstrategy_semantic_preservation".
intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
match goal with
[ H: exists p, _ /\ _ |- _ ] =>
let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
destruct H as (p & M & MM); clear H
end.
repeat DestructM. subst tp.
assert (F: forward_simulation (Cstrategy.semantics p) (Asm.semantics p21)).
{
eapply compose_forward_simulations.
eapply SimplExprproof.transl_program_correct; eassumption.
eapply compose_forward_simulations.
eapply SimplLocalsproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply Cshmgenproof.transl_program_correct; eassumption.
eapply compose_forward_simulations.
eapply Cminorgenproof.transl_program_correct; eassumption.
eapply compose_forward_simulations.
eapply Selectionproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply RTLgenproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
eapply compose_forward_simulations.
eapply Inliningproof.transf_program_correct; eassumption.
eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
eapply compose_forward_simulations.
eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
eapply compose_forward_simulations.
eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
eapply compose_forward_simulations.
eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply Unusedglobproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply Allocproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply Tunnelingproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply Linearizeproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply CleanupLabelsproof.transf_program_correct; eassumption.
eapply compose_forward_simulations.
eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
eapply compose_forward_simulations.
eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
exact Asmgenproof.return_address_exists.
eassumption.
eapply Asmgenproof.transf_program_correct; eassumption.
}
split. auto.
apply forward_to_backward_simulation.
apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
apply Asm.semantics_determinate.
Qed.

Theorem c_semantic_preservation:
forall p tp,
match_prog p tp ->
backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof. hammer_hook "Compiler" "Compiler.c_semantic_preservation".
intros.
apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
eapply sd_traces; eapply Asm.semantics_determinate.
apply factor_backward_simulation.
apply Cstrategy.strategy_simulation.
apply Csem.semantics_single_events.
eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
exact (proj2 (cstrategy_semantic_preservation _ _ H)).
Qed.





Theorem transf_c_program_correct:
forall p tp,
transf_c_program p = OK tp ->
backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof. hammer_hook "Compiler" "Compiler.transf_c_program_correct".
intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.



Theorem separate_transf_c_program_correct:
forall c_units asm_units c_program,
nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units ->
link_list c_units = Some c_program ->
exists asm_program,
link_list asm_units = Some asm_program
/\ backward_simulation (Csem.semantics c_program) (Asm.semantics asm_program).
Proof. hammer_hook "Compiler" "Compiler.separate_transf_c_program_correct".
intros.
assert (nlist_forall2 match_prog c_units asm_units).
{ eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_c_program_match; auto. }
assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
{ eapply link_list_compose_passes; eauto. }
destruct H2 as (asm_program & P & Q).
exists asm_program; split; auto. apply c_semantic_preservation; auto.
Qed.
