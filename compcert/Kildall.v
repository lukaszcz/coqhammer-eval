From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import Iteration.
From compcert Require Import Maps.
From compcert Require Import Lattice.


Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.







Module Type DATAFLOW_SOLVER.

Declare Module L: SEMILATTICE.



Parameter fixpoint:
forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
(transf: positive -> L.t -> L.t)
(ep: positive) (ev: L.t),
option (PMap.t L.t).



Axiom fixpoint_solution:
forall A (code: PTree.t A) successors transf ep ev res n instr s,
fixpoint code successors transf ep ev = Some res ->
code!n = Some instr -> In s (successors instr) ->
(forall n, L.eq (transf n L.bot) L.bot) ->
L.ge res!!s (transf n res!!n).



Axiom fixpoint_entry:
forall A (code: PTree.t A) successors transf ep ev res,
fixpoint code successors transf ep ev = Some res ->
L.ge res!!ep ev.



Axiom fixpoint_invariant:
forall A (code: PTree.t A) successors transf ep ev
(P: L.t -> Prop),
P L.bot ->
(forall x y, P x -> P y -> P (L.lub x y)) ->
(forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x)) ->
P ev ->
forall res pc,
fixpoint code successors transf ep ev = Some res ->
P res!!pc.

End DATAFLOW_SOLVER.



Module Type NODE_SET.

Parameter t: Type.
Parameter empty: t.
Parameter add: positive -> t -> t.
Parameter pick: t -> option (positive * t).
Parameter all_nodes: forall {A: Type}, PTree.t A -> t.

Parameter In: positive -> t -> Prop.
Axiom empty_spec:
forall n, ~In n empty.
Axiom add_spec:
forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
Axiom pick_none:
forall s n, pick s = None -> ~In n s.
Axiom pick_some:
forall s n s', pick s = Some(n, s') ->
forall n', In n' s <-> n = n' \/ In n' s'.
Axiom all_nodes_spec:
forall A (code: PTree.t A) n instr,
code!n = Some instr -> In n (all_nodes code).

End NODE_SET.



Section REACHABLE.

Context {A: Type} (code: PTree.t A) (successors: A -> list positive).

Inductive reachable: positive -> positive -> Prop :=
| reachable_refl: forall n, reachable n n
| reachable_left: forall n1 n2 n3 i,
code!n1 = Some i -> In n2 (successors i) -> reachable n2 n3 ->
reachable n1 n3.

Scheme reachable_ind := Induction for reachable Sort Prop.

Lemma reachable_trans:
forall n1 n2, reachable n1 n2 -> forall n3, reachable n2 n3 -> reachable n1 n3.
Proof. hammer_hook "Kildall" "Kildall.reachable_trans".
induction 1; intros.
- auto.
- econstructor; eauto.
Qed.

Lemma reachable_right:
forall n1 n2 n3 i,
reachable n1 n2 -> code!n2 = Some i -> In n3 (successors i) ->
reachable n1 n3.
Proof. hammer_hook "Kildall" "Kildall.reachable_right".
intros. apply reachable_trans with n2; auto. econstructor; eauto. constructor.
Qed.

End REACHABLE.



Module Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET) <:
DATAFLOW_SOLVER with Module L := LAT.

Module L := LAT.

Section Kildall.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.
Variable transf: positive -> L.t -> L.t.



Record state : Type :=
mkstate { aval: PTree.t L.t; worklist: NS.t; visited: positive -> Prop }.

Definition abstr_value (n: positive) (s: state) : L.t :=
match s.(aval)!n with
| None => L.bot
| Some v => v
end.





Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
match s.(aval)!n with
| None =>
{| aval := PTree.set n out s.(aval);
worklist := NS.add n s.(worklist);
visited := fun p => p = n \/ s.(visited) p |}
| Some oldl =>
let newl := L.lub oldl out in
if L.beq oldl newl
then s
else {| aval := PTree.set n newl s.(aval);
worklist := NS.add n s.(worklist);
visited := fun p => p = n \/ s.(visited) p |}
end.



Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list positive)
{struct succs} : state :=
match succs with
| nil => s
| n :: rem => propagate_succ_list (propagate_succ s out n) out rem
end.



Definition step (s: state) : PMap.t L.t + state :=
match NS.pick s.(worklist) with
| None =>
inl _ (L.bot, s.(aval))
| Some(n, rem) =>
match code!n with
| None =>
inr _ {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
| Some instr =>
inr _ (propagate_succ_list
{| aval := s.(aval); worklist := rem; visited := s.(visited) |}
(transf n (abstr_value n s))
(successors instr))
end
end.



Definition fixpoint_from (start: state) : option (PMap.t L.t) :=
PrimIter.iterate _ _ step start.



Definition start_state (enode: positive) (eval: L.t) :=
{| aval := PTree.set enode eval (PTree.empty L.t);
worklist := NS.add enode NS.empty;
visited := fun n => n = enode |}.

Definition fixpoint (enode: positive) (eval: L.t) :=
fixpoint_from (start_state enode eval).



Definition start_state_nodeset (enodes: NS.t) :=
{| aval := PTree.empty L.t;
worklist := enodes;
visited := fun n => NS.In n enodes |}.

Definition fixpoint_nodeset (enodes: NS.t) :=
fixpoint_from (start_state_nodeset enodes).

Definition start_state_allnodes :=
{| aval := PTree.empty L.t;
worklist := NS.all_nodes code;
visited := fun n => exists instr, code!n = Some instr |}.

Definition fixpoint_allnodes :=
fixpoint_from start_state_allnodes.



Inductive optge: option L.t -> option L.t -> Prop :=
| optge_some: forall l l',
L.ge l l' -> optge (Some l) (Some l')
| optge_none: forall ol,
optge ol None.

Remark optge_refl: forall ol, optge ol ol.
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.optge_refl". destruct ol; constructor. apply L.ge_refl; apply L.eq_refl. Qed.

Remark optge_trans: forall ol1 ol2 ol3, optge ol1 ol2 -> optge ol2 ol3 -> optge ol1 ol3.
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.optge_trans".
intros. inv H0.
inv H. constructor. eapply L.ge_trans; eauto.
constructor.
Qed.

Remark optge_abstr_value:
forall st st' n,
optge st.(aval)!n st'.(aval)!n ->
L.ge (abstr_value n st) (abstr_value n st').
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.optge_abstr_value".
intros. unfold abstr_value. inv H. auto. apply L.ge_bot.
Qed.

Lemma propagate_succ_charact:
forall st out n,
let st' := propagate_succ st out n in
optge st'.(aval)!n (Some out)
/\ (forall s, n <> s -> st'.(aval)!s = st.(aval)!s)
/\ (forall s, optge st'.(aval)!s st.(aval)!s)
/\ (NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n)
/\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist))
/\ (forall n', NS.In n' st'.(worklist) -> n' = n \/ NS.In n' st.(worklist))
/\ (forall n', st.(visited) n' -> st'.(visited) n')
/\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')
/\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n').
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.propagate_succ_charact".
unfold propagate_succ; intros; simpl.
destruct st.(aval)!n as [v|] eqn:E;
[predSpec L.beq L.beq_correct v (L.lub v out) | idtac].
-
repeat split; intros.
+ rewrite E. constructor. eapply L.ge_trans. apply L.ge_refl. apply H; auto. apply L.ge_lub_right.
+ apply optge_refl.
+ right; auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ congruence.
-
simpl; repeat split; intros.
+ rewrite PTree.gss. constructor. apply L.ge_lub_right.
+ rewrite PTree.gso by auto. auto.
+ rewrite PTree.gsspec. destruct (peq s n).
subst s. rewrite E. constructor. apply L.ge_lub_left.
apply optge_refl.
+ rewrite NS.add_spec. auto.
+ rewrite NS.add_spec. auto.
+ rewrite NS.add_spec in H0. intuition.
+ auto.
+ destruct H0; auto. subst n'. rewrite NS.add_spec; auto.
+ rewrite PTree.gsspec in H1. destruct (peq n' n). auto. congruence.
-
simpl; repeat split; intros.
+ rewrite PTree.gss. apply optge_refl.
+ rewrite PTree.gso by auto. auto.
+ rewrite PTree.gsspec. destruct (peq s n).
subst s. rewrite E. constructor.
apply optge_refl.
+ rewrite NS.add_spec. auto.
+ rewrite NS.add_spec. auto.
+ rewrite NS.add_spec in H. intuition.
+ auto.
+ destruct H; auto. subst n'. rewrite NS.add_spec. auto.
+ rewrite PTree.gsspec in H0. destruct (peq n' n). auto. congruence.
Qed.

Lemma propagate_succ_list_charact:
forall out l st,
let st' := propagate_succ_list st out l in
(forall n, In n l -> optge st'.(aval)!n (Some out))
/\ (forall n, ~In n l -> st'.(aval)!n = st.(aval)!n)
/\ (forall n, optge st'.(aval)!n st.(aval)!n)
/\ (forall n, NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n)
/\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist))
/\ (forall n', NS.In n' st'.(worklist) -> In n' l \/ NS.In n' st.(worklist))
/\ (forall n', st.(visited) n' -> st'.(visited) n')
/\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')
/\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n').
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.propagate_succ_list_charact".
induction l; simpl; intros.
- repeat split; intros.
+ contradiction.
+ apply optge_refl.
+ auto.
+ auto.
+ auto.
+ auto.
+ auto.
+ congruence.
- generalize (propagate_succ_charact st out a).
set (st1 := propagate_succ st out a).
intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
generalize (IHl st1).
set (st2 := propagate_succ_list st1 out l).
intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). clear IHl.
repeat split; intros.
+ destruct H.
* subst n. eapply optge_trans; eauto.
* auto.
+ rewrite B2 by tauto. apply A2; tauto.
+ eapply optge_trans; eauto.
+ destruct (B4 n). auto.
destruct (peq n a).
* subst n. destruct A4. left; auto. right; congruence.
* right. rewrite H. auto.
+ eauto.
+ exploit B6; eauto. intros [P|P]. auto.
exploit A6; eauto. intuition.
+ eauto.
+ specialize (B8 n'); specialize (A8 n'). intuition.
+ destruct st1.(aval)!n' eqn:ST1.
apply B7. apply A9; auto. congruence.
apply B9; auto.
Qed.



Inductive steps: state -> state -> Prop :=
| steps_base: forall s, steps s s
| steps_right: forall s1 s2 s3, steps s1 s2 -> step s2 = inr s3 -> steps s1 s3.

Scheme steps_ind := Induction for steps Sort Prop.

Lemma fixpoint_from_charact:
forall start res,
fixpoint_from start = Some res ->
exists st, steps start st /\ NS.pick st.(worklist) = None /\ res = (L.bot, st.(aval)).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.fixpoint_from_charact".
unfold fixpoint; intros.
eapply (PrimIter.iterate_prop _ _ step
(fun st => steps start st)
(fun res => exists st, steps start st /\ NS.pick (worklist st) = None /\ res = (L.bot, aval st))); eauto.
intros. destruct (step a) eqn:E.
exists a; split; auto.
unfold step in E. destruct (NS.pick (worklist a)) as [[n rem]|].
destruct (code!n); discriminate.
inv E. auto.
eapply steps_right; eauto.
constructor.
Qed.





Lemma step_incr:
forall n s1 s2, step s1 = inr s2 ->
optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.step_incr".
unfold step; intros.
destruct (NS.pick (worklist s1)) as [[p rem] | ]; try discriminate.
destruct (code!p) as [instr|]; inv H.
+ generalize (propagate_succ_list_charact
(transf p (abstr_value p s1))
(successors instr)
{| aval := aval s1; worklist := rem; visited := visited s1 |}).
simpl.
set (s' := propagate_succ_list {| aval := aval s1; worklist := rem; visited := visited s1 |}
(transf p (abstr_value p s1)) (successors instr)).
intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
auto.
+ split. apply optge_refl. auto.
Qed.

Lemma steps_incr:
forall n s1 s2, steps s1 s2 ->
optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.steps_incr".
induction 1.
- split. apply optge_refl. auto.
- destruct IHsteps. exploit (step_incr n); eauto. intros [P Q].
split. eapply optge_trans; eauto. eauto.
Qed.





Record good_state (st: state) : Prop := {
gs_stable: forall n,
st.(visited) n ->
NS.In n st.(worklist) \/
(forall i s,
code!n = Some i -> In s (successors i) ->
optge st.(aval)!s (Some (transf n (abstr_value n st))));
gs_defined: forall n v,
st.(aval)!n = Some v -> st.(visited) n
}.



Lemma step_state_good:
forall st pc rem instr,
NS.pick st.(worklist) = Some (pc, rem) ->
code!pc = Some instr ->
good_state st ->
good_state (propagate_succ_list (mkstate st.(aval) rem st.(visited))
(transf pc (abstr_value pc st))
(successors instr)).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.step_state_good".
intros until instr; intros PICK CODEAT [GOOD1 GOOD2].
generalize (NS.pick_some _ _ _ PICK); intro PICK2.
set (out := transf pc (abstr_value pc st)).
generalize (propagate_succ_list_charact out (successors instr) {| aval := aval st; worklist := rem; visited := visited st |}).
set (st' := propagate_succ_list {| aval := aval st; worklist := rem; visited := visited st |} out
(successors instr)).
simpl; intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
constructor; intros.
-
destruct (A8 n H); auto. destruct (A4 n); auto.
replace (abstr_value n st') with (abstr_value n st)
by (unfold abstr_value; rewrite H1; auto).
exploit GOOD1; eauto. intros [P|P].
+
rewrite PICK2 in P; destruct P.
*
subst n. fold out. right; intros.
assert (i = instr) by congruence. subst i.
apply A1; auto.
*
left. apply A5; auto.
+
right; intros. apply optge_trans with st.(aval)!s; eauto.
-
destruct st.(aval)!n as [v'|] eqn:ST.
+ apply A7. eapply GOOD2; eauto.
+ apply A9; auto. congruence.
Qed.

Lemma step_state_good_2:
forall st pc rem,
good_state st ->
NS.pick (worklist st) = Some (pc, rem) ->
code!pc = None ->
good_state (mkstate st.(aval) rem st.(visited)).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.step_state_good_2".
intros until rem; intros [GOOD1 GOOD2] PICK CODE.
generalize (NS.pick_some _ _ _ PICK); intro PICK2.
constructor; simpl; intros.
-
exploit GOOD1; eauto. intros [P | P].
+ rewrite PICK2 in P. destruct P; auto.
subst n. right; intros. congruence.
+ right; exact P.
-
eapply GOOD2; eauto.
Qed.

Lemma steps_state_good:
forall st1 st2, steps st1 st2 -> good_state st1 -> good_state st2.
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.steps_state_good".
induction 1; intros.
- auto.
- unfold step in e.
destruct (NS.pick (worklist s2)) as [[n rem] | ] eqn:PICK; try discriminate.
destruct (code!n) as [instr|] eqn:CODE; inv e.
eapply step_state_good; eauto.
eapply step_state_good_2; eauto.
Qed.



Lemma start_state_good:
forall enode eval, good_state (start_state enode eval).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.start_state_good".
intros. unfold start_state; constructor; simpl; intros.
- subst n. rewrite NS.add_spec; auto.
- rewrite PTree.gsspec in H. rewrite PTree.gempty in H.
destruct (peq n enode). auto. discriminate.
Qed.

Lemma start_state_nodeset_good:
forall enodes, good_state (start_state_nodeset enodes).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.start_state_nodeset_good".
intros. unfold start_state_nodeset; constructor; simpl; intros.
- left. auto.
- rewrite PTree.gempty in H. congruence.
Qed.

Lemma start_state_allnodes_good:
good_state start_state_allnodes.
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.start_state_allnodes_good".
unfold start_state_allnodes; constructor; simpl; intros.
- destruct H as [instr CODE]. left. eapply NS.all_nodes_spec; eauto.
- rewrite PTree.gempty in H. congruence.
Qed.



Lemma reachable_visited:
forall st, good_state st -> NS.pick st.(worklist) = None ->
forall p q, reachable code successors p q -> st.(visited) p -> st.(visited) q.
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.reachable_visited".
intros st [GOOD1 GOOD2] PICK. induction 1; intros.
- auto.
- eapply IHreachable; eauto.
exploit GOOD1; eauto. intros [P | P].
eelim NS.pick_none; eauto.
exploit P; eauto. intros OGE; inv OGE. eapply GOOD2; eauto.
Qed.





Theorem fixpoint_solution:
forall ep ev res n instr s,
fixpoint ep ev = Some res ->
code!n = Some instr ->
In s (successors instr) ->
(forall n, L.eq (transf n L.bot) L.bot) ->
L.ge res!!s (transf n res!!n).
Proof. hammer_hook "Kildall" "Kildall.DATAFLOW_SOLVER.fixpoint_solution".
unfold fixpoint; intros.
exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
exploit steps_state_good; eauto. apply start_state_good. intros [GOOD1 GOOD2].
rewrite RES; unfold PMap.get; simpl.
destruct st.(aval)!n as [v|] eqn:STN.
- destruct (GOOD1 n) as [P|P]; eauto.
eelim NS.pick_none; eauto.
exploit P; eauto. unfold abstr_value; rewrite STN. intros OGE; inv OGE. auto.
- apply L.ge_trans with L.bot. apply L.ge_bot. apply L.ge_refl. apply L.eq_sym. eauto.
Qed.



Theorem fixpoint_entry:
forall ep ev res,
fixpoint ep ev = Some res ->
L.ge res!!ep ev.
Proof. hammer_hook "Kildall" "Kildall.DATAFLOW_SOLVER.fixpoint_entry".
unfold fixpoint; intros.
exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
exploit (steps_incr ep); eauto. simpl. rewrite PTree.gss. intros [P Q].
rewrite RES; unfold PMap.get; simpl. inv P; auto.
Qed.



Theorem fixpoint_allnodes_solution:
forall res n instr s,
fixpoint_allnodes = Some res ->
code!n = Some instr ->
In s (successors instr) ->
L.ge res!!s (transf n res!!n).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.fixpoint_allnodes_solution".
unfold fixpoint_allnodes; intros.
exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
exploit steps_state_good; eauto. apply start_state_allnodes_good. intros [GOOD1 GOOD2].
exploit (steps_incr n); eauto. simpl. intros [U V].
exploit (GOOD1 n). apply V. exists instr; auto. intros [P|P].
eelim NS.pick_none; eauto.
exploit P; eauto. intros OGE. rewrite RES; unfold PMap.get; simpl.
inv OGE. assumption.
Qed.



Theorem fixpoint_nodeset_solution:
forall enodes res e n instr s,
fixpoint_nodeset enodes = Some res ->
NS.In e enodes ->
reachable code successors e n ->
code!n = Some instr ->
In s (successors instr) ->
L.ge res!!s (transf n res!!n).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.fixpoint_nodeset_solution".
unfold fixpoint_nodeset; intros.
exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
exploit steps_state_good; eauto. apply start_state_nodeset_good. intros GOOD.
exploit (steps_incr e); eauto. simpl. intros [U V].
assert (st.(visited) n).
{ eapply reachable_visited; eauto. }
destruct GOOD as [GOOD1 GOOD2].
exploit (GOOD1 n); eauto. intros [P|P].
eelim NS.pick_none; eauto.
exploit P; eauto. intros OGE. rewrite RES; unfold PMap.get; simpl.
inv OGE. assumption.
Qed.



Theorem fixpoint_invariant:
forall ep ev
(P: L.t -> Prop)
(P_bot: P L.bot)
(P_lub: forall x y, P x -> P y -> P (L.lub x y))
(P_transf: forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x))
(P_entrypoint: P ev)
res pc,
fixpoint ep ev = Some res ->
P res!!pc.
Proof. hammer_hook "Kildall" "Kildall.DATAFLOW_SOLVER.fixpoint_invariant".
intros.
set (inv := fun st => forall x, P (abstr_value x st)).
assert (inv (start_state ep ev)).
{
red; simpl; intros. unfold abstr_value, start_state; simpl.
rewrite PTree.gsspec. rewrite PTree.gempty.
destruct (peq x ep). auto. auto.
}
assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
{
unfold inv, propagate_succ. intros.
destruct (aval st)!n as [oldl|] eqn:E.
destruct (L.beq oldl (L.lub oldl v)).
auto.
unfold abstr_value. simpl. rewrite PTree.gsspec. destruct (peq x n).
apply P_lub; auto. replace oldl with (abstr_value n st). auto.
unfold abstr_value; rewrite E; auto.
apply H1.
unfold abstr_value. simpl. rewrite PTree.gsspec. destruct (peq x n).
auto.
apply H1.
}
assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
{
induction l; intros; simpl. auto.
apply IHl; auto.
}
assert (forall st1 st2, steps st1 st2 -> inv st1 -> inv st2).
{
induction 1; intros.
auto.
unfold step in e. destruct (NS.pick (worklist s2)) as [[n rem]|]; try discriminate.
destruct (code!n) as [instr|] eqn:INSTR; inv e.
apply H2. apply IHsteps; auto. eapply P_transf; eauto. apply IHsteps; auto.
apply IHsteps; auto.
}
unfold fixpoint in H. exploit fixpoint_from_charact; eauto.
intros (st & STEPS & PICK & RES).
replace (res!!pc) with (abstr_value pc st). eapply H3; eauto.
rewrite RES; auto.
Qed.

End Kildall.

End Dataflow_Solver.







Definition successors_list (successors: PTree.t (list positive)) (pc: positive) : list positive :=
match successors!pc with None => nil | Some l => l end.

Notation "a !!! b" := (successors_list a b) (at level 1).

Section Predecessor.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.

Fixpoint add_successors (pred: PTree.t (list positive))
(from: positive) (tolist: list positive)
{struct tolist} : PTree.t (list positive) :=
match tolist with
| nil => pred
| to :: rem => add_successors (PTree.set to (from :: pred!!!to) pred) from rem
end.

Lemma add_successors_correct:
forall tolist from pred n s,
In n pred!!!s \/ (n = from /\ In s tolist) ->
In n (add_successors pred from tolist)!!!s.
Proof. hammer_hook "Kildall" "Kildall.add_successors_correct".
induction tolist; simpl; intros.
tauto.
apply IHtolist.
unfold successors_list at 1. rewrite PTree.gsspec. destruct (peq s a).
subst a. destruct H. auto with coqlib.
destruct H. subst n. auto with coqlib.
fold (successors_list pred s). intuition congruence.
Qed.

Definition make_predecessors : PTree.t (list positive) :=
PTree.fold (fun pred pc instr => add_successors pred pc (successors instr))
code (PTree.empty (list positive)).

Lemma make_predecessors_correct_1:
forall n instr s,
code!n = Some instr -> In s (successors instr) ->
In n make_predecessors!!!s.
Proof. hammer_hook "Kildall" "Kildall.make_predecessors_correct_1".
intros until s.
set (P := fun m p => m!n = Some instr -> In s (successors instr) ->
In n p!!!s).
unfold make_predecessors.
apply PTree_Properties.fold_rec with (P := P); unfold P; intros.

apply H0; auto. rewrite H; auto.

rewrite PTree.gempty in H; congruence.

apply add_successors_correct.
rewrite PTree.gsspec in H2. destruct (peq n k).
inv H2. auto.
auto.
Qed.

Lemma make_predecessors_correct_2:
forall n instr s,
code!n = Some instr -> In s (successors instr) ->
exists l, make_predecessors!s = Some l /\ In n l.
Proof. hammer_hook "Kildall" "Kildall.make_predecessors_correct_2".
intros. exploit make_predecessors_correct_1; eauto.
unfold successors_list. destruct (make_predecessors!s); simpl; intros.
exists l; auto.
contradiction.
Qed.

Lemma reachable_predecessors:
forall p q,
reachable code successors p q ->
reachable make_predecessors (fun l => l) q p.
Proof. hammer_hook "Kildall" "Kildall.reachable_predecessors".
induction 1.
- constructor.
- exploit make_predecessors_correct_2; eauto. intros [l [P Q]].
eapply reachable_right; eauto.
Qed.

End Predecessor.





Module Type BACKWARD_DATAFLOW_SOLVER.

Declare Module L: SEMILATTICE.



Parameter fixpoint:
forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
(transf: positive -> L.t -> L.t),
option (PMap.t L.t).



Axiom fixpoint_solution:
forall A (code: PTree.t A) successors transf res n instr s,
fixpoint code successors transf = Some res ->
code!n = Some instr -> In s (successors instr) ->
(forall n a, code!n = None -> L.eq (transf n a) L.bot) ->
L.ge res!!n (transf s res!!s).



Parameter fixpoint_allnodes:
forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
(transf: positive -> L.t -> L.t),
option (PMap.t L.t).

Axiom fixpoint_allnodes_solution:
forall A (code: PTree.t A) successors transf res n instr s,
fixpoint_allnodes code successors transf = Some res ->
code!n = Some instr -> In s (successors instr) ->
L.ge res!!n (transf s res!!s).

End BACKWARD_DATAFLOW_SOLVER.



Module Backward_Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET):
BACKWARD_DATAFLOW_SOLVER with Module L := LAT.

Module L := LAT.

Module DS := Dataflow_Solver L NS.

Section Kildall.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.
Variable transf: positive -> L.t -> L.t.



Section Exit_points.



Definition sequential_node (pc: positive) (instr: A): bool :=
existsb (fun s => match code!s with None => false | Some _ => plt s pc end)
(successors instr).

Definition exit_points : NS.t :=
PTree.fold
(fun ep pc instr =>
if sequential_node pc instr
then ep
else NS.add pc ep)
code NS.empty.

Lemma exit_points_charact:
forall n,
NS.In n exit_points <-> exists i, code!n = Some i /\ sequential_node n i = false.
Proof. hammer_hook "Kildall" "Kildall.Backward_Dataflow_Solver.exit_points_charact".
intros n. unfold exit_points. eapply PTree_Properties.fold_rec.
-
intros. rewrite <- H. auto.
-
simpl. split; intros.
eelim NS.empty_spec; eauto.
destruct H as [i [P Q]]. rewrite PTree.gempty in P. congruence.
-
intros. destruct (sequential_node k v) eqn:SN.
+ rewrite H1. rewrite PTree.gsspec. destruct (peq n k).
subst. split; intros [i [P Q]]. congruence. inv P. congruence.
tauto.
+ rewrite NS.add_spec. rewrite H1. rewrite PTree.gsspec. destruct (peq n k).
subst. split. intros. exists v; auto. auto.
split. intros [P | [i [P Q]]]. congruence. exists i; auto.
intros [i [P Q]]. right; exists i; auto.
Qed.

Lemma reachable_exit_points:
forall pc i,
code!pc = Some i -> exists x, NS.In x exit_points /\ reachable code successors pc x.
Proof. hammer_hook "Kildall" "Kildall.Backward_Dataflow_Solver.reachable_exit_points".
intros pc0. pattern pc0. apply (well_founded_ind Plt_wf).
intros pc HR i CODE.
destruct (sequential_node pc i) eqn:SN.
-
unfold sequential_node in SN. rewrite existsb_exists in SN.
destruct SN as [s [P Q]]. destruct (code!s) as [i'|] eqn:CS; try discriminate. InvBooleans.
exploit (HR s); eauto. intros [x [U V]].
exists x; split; auto. eapply reachable_left; eauto.
-
exists pc; split.
rewrite exit_points_charact. exists i; auto. constructor.
Qed.



Lemma reachable_exit_points_predecessor:
forall pc i,
code!pc = Some i ->
exists x, NS.In x exit_points /\ reachable (make_predecessors code successors) (fun l => l) x pc.
Proof. hammer_hook "Kildall" "Kildall.Backward_Dataflow_Solver.reachable_exit_points_predecessor".
intros. exploit reachable_exit_points; eauto. intros [x [P Q]].
exists x; split; auto. apply reachable_predecessors. auto.
Qed.

End Exit_points.



Definition fixpoint :=
DS.fixpoint_nodeset
(make_predecessors code successors) (fun l => l)
transf exit_points.

Theorem fixpoint_solution:
forall res n instr s,
fixpoint = Some res ->
code!n = Some instr -> In s (successors instr) ->
(forall n a, code!n = None -> L.eq (transf n a) L.bot) ->
L.ge res!!n (transf s res!!s).
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.fixpoint_solution".
intros.
exploit (make_predecessors_correct_2 code); eauto. intros [l [P Q]].
destruct code!s as [instr'|] eqn:CS.
- exploit reachable_exit_points_predecessor. eexact CS. intros (ep & U & V).
unfold fixpoint in H. eapply DS.fixpoint_nodeset_solution; eauto.
- apply L.ge_trans with L.bot. apply L.ge_bot.
apply L.ge_refl. apply L.eq_sym. auto.
Qed.



Definition fixpoint_allnodes :=
DS.fixpoint_allnodes
(make_predecessors code successors) (fun l => l)
transf.

Theorem fixpoint_allnodes_solution:
forall res n instr s,
fixpoint_allnodes = Some res ->
code!n = Some instr -> In s (successors instr) ->
L.ge res!!n (transf s res!!s).
Proof. hammer_hook "Kildall" "Kildall.BACKWARD_DATAFLOW_SOLVER.fixpoint_allnodes_solution".
intros.
exploit (make_predecessors_correct_2 code); eauto. intros [l [P Q]].
unfold fixpoint_allnodes in H.
eapply DS.fixpoint_allnodes_solution; eauto.
Qed.

End Kildall.

End Backward_Dataflow_Solver.





Module Type ORDERED_TYPE_WITH_TOP.

Parameter t: Type.
Parameter ge: t -> t -> Prop.
Parameter top: t.
Axiom top_ge: forall x, ge top x.
Axiom refl_ge: forall x, ge x x.

End ORDERED_TYPE_WITH_TOP.



Module Type BBLOCK_SOLVER.

Declare Module L: ORDERED_TYPE_WITH_TOP.

Parameter fixpoint:
forall {A: Type} (code: PTree.t A) (successors: A -> list positive)
(transf: positive -> L.t -> L.t)
(entrypoint: positive),
option (PMap.t L.t).

Axiom fixpoint_solution:
forall A (code: PTree.t A) successors transf entrypoint res n instr s,
fixpoint code successors transf entrypoint = Some res ->
code!n = Some instr -> In s (successors instr) ->
L.ge res!!s (transf n res!!n).

Axiom fixpoint_entry:
forall A (code: PTree.t A) successors transf entrypoint res,
fixpoint code successors transf entrypoint = Some res ->
res!!entrypoint = L.top.

Axiom fixpoint_invariant:
forall A (code: PTree.t A) successors transf entrypoint
(P: L.t -> Prop),
P L.top ->
(forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x)) ->
forall res pc,
fixpoint code successors transf entrypoint = Some res ->
P res!!pc.

End BBLOCK_SOLVER.



Module BBlock_solver(LAT: ORDERED_TYPE_WITH_TOP):
BBLOCK_SOLVER with Module L := LAT.

Module L := LAT.

Section Solver.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.
Variable transf: positive -> L.t -> L.t.
Variable entrypoint: positive.
Variable P: L.t -> Prop.
Hypothesis Ptop: P L.top.
Hypothesis Ptransf: forall pc instr x, code!pc = Some instr -> P x -> P (transf pc x).

Definition bbmap := positive -> bool.
Definition result := PMap.t L.t.



Record state : Type := mkstate
{ aval: result; worklist: list positive }.



Fixpoint propagate_successors
(bb: bbmap) (succs: list positive) (l: L.t) (st: state)
{struct succs} : state :=
match succs with
| nil => st
| s1 :: sl =>
if bb s1 then
propagate_successors bb sl l st
else
propagate_successors bb sl l
(mkstate (PMap.set s1 l st.(aval))
(s1 :: st.(worklist)))
end.

Definition step (bb: bbmap) (st: state) : result + state :=
match st.(worklist) with
| nil => inl _ st.(aval)
| pc :: rem =>
match code!pc with
| None =>
inr _ (mkstate st.(aval) rem)
| Some instr =>
inr _ (propagate_successors
bb (successors instr)
(transf pc st.(aval)!!pc)
(mkstate st.(aval) rem))
end
end.



Definition is_basic_block_head
(preds: PTree.t (list positive)) (pc: positive) : bool :=
if peq pc entrypoint then true else
match preds!!!pc with
| nil => false
| s :: nil => peq s pc
| _ :: _ :: _ => true
end.

Definition basic_block_map : bbmap :=
is_basic_block_head (make_predecessors code successors).

Definition basic_block_list (bb: bbmap) : list positive :=
PTree.fold (fun l pc instr => if bb pc then pc :: l else l)
code nil.



Definition fixpoint : option result :=
let bb := basic_block_map in
PrimIter.iterate _ _ (step bb) (mkstate (PMap.init L.top) (basic_block_list bb)).



Definition predecessors := make_predecessors code successors.

Lemma predecessors_correct:
forall n instr s,
code!n = Some instr -> In s (successors instr) -> In n predecessors!!!s.
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.predecessors_correct".
intros. unfold predecessors. eapply make_predecessors_correct_1; eauto.
Qed.

Lemma multiple_predecessors:
forall s n1 instr1 n2 instr2,
code!n1 = Some instr1 -> In s (successors instr1) ->
code!n2 = Some instr2 -> In s (successors instr2) ->
n1 <> n2 ->
basic_block_map s = true.
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.multiple_predecessors".
intros.
assert (In n1 predecessors!!!s). eapply predecessors_correct; eauto.
assert (In n2 predecessors!!!s). eapply predecessors_correct; eauto.
unfold basic_block_map, is_basic_block_head.
destruct (peq s entrypoint). auto.
fold predecessors.
destruct (predecessors!!!s).
auto.
destruct l.
apply proj_sumbool_is_true. simpl in *. intuition congruence.
auto.
Qed.

Lemma no_self_loop:
forall n instr,
code!n = Some instr -> In n (successors instr) -> basic_block_map n = true.
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.no_self_loop".
intros. unfold basic_block_map, is_basic_block_head.
destruct (peq n entrypoint). auto.
fold predecessors.
exploit predecessors_correct; eauto. intros.
destruct (predecessors!!!n).
contradiction.
destruct l. apply proj_sumbool_is_true. simpl in H1. tauto.
auto.
Qed.





Definition state_invariant (st: state) : Prop :=
(forall n, basic_block_map n = true -> st.(aval)!!n = L.top)
/\
(forall n,
In n st.(worklist) \/
(forall instr s, code!n = Some instr -> In s (successors instr) ->
L.ge st.(aval)!!s (transf n st.(aval)!!n))).

Lemma propagate_successors_charact1:
forall bb succs l st,
incl st.(worklist)
(propagate_successors bb succs l st).(worklist).
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.propagate_successors_charact1".
induction succs; simpl; intros.
apply incl_refl.
case (bb a).
auto.
apply incl_tran with (a :: worklist st).
apply incl_tl. apply incl_refl.
set (st1 := (mkstate (PMap.set a l (aval st)) (a :: worklist st))).
change (a :: worklist st) with (worklist st1).
auto.
Qed.

Lemma propagate_successors_charact2:
forall bb succs l st n,
let st' := propagate_successors bb succs l st in
(In n succs -> bb n = false -> In n st'.(worklist) /\ st'.(aval)!!n = l)
/\ (~In n succs \/ bb n = true -> st'.(aval)!!n = st.(aval)!!n).
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.propagate_successors_charact2".
induction succs; simpl; intros.

split. tauto. auto.

caseEq (bb a); intro.
elim (IHsuccs l st n); intros U V.
split; intros. apply U; auto.
elim H0; intro. subst a. congruence. auto.
apply V. tauto.
set (st1 := mkstate (PMap.set a l (aval st)) (a :: worklist st)).
elim (IHsuccs l st1 n); intros U V.
split; intros.
elim H0; intros.
subst n. split.
apply propagate_successors_charact1. simpl. tauto.
case (In_dec peq a succs); intro.
elim (U i H1); auto.
rewrite V. unfold st1; simpl. apply PMap.gss. tauto.
apply U; auto.
rewrite V. unfold st1; simpl. apply PMap.gso.
red; intro; subst n. elim H0; intro. tauto. congruence.
tauto.
Qed.

Lemma propagate_successors_invariant:
forall pc instr res rem,
code!pc = Some instr ->
state_invariant (mkstate res (pc :: rem)) ->
state_invariant
(propagate_successors basic_block_map (successors instr)
(transf pc res!!pc)
(mkstate res rem)).
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.propagate_successors_invariant".
intros until rem. intros CODE [INV1 INV2]. simpl in INV1. simpl in INV2.
set (l := transf pc res!!pc).
generalize (propagate_successors_charact1 basic_block_map
(successors instr) l (mkstate res rem)).
generalize (propagate_successors_charact2 basic_block_map
(successors instr) l (mkstate res rem)).
set (st1 := propagate_successors basic_block_map
(successors instr) l (mkstate res rem)).
intros U V. simpl in U.

split; intros.
elim (U n); intros C D. rewrite D. simpl. apply INV1. auto. tauto.


destruct (peq pc n). subst n.
right; intros.
assert (instr0 = instr) by congruence. subst instr0.
elim (U s); intros C D.
replace (st1.(aval)!!pc) with res!!pc. fold l.
destruct (basic_block_map s) eqn:BB.
rewrite D. simpl. rewrite INV1. apply L.top_ge. auto. tauto.
elim (C H0 (eq_refl _)). intros X Y. rewrite Y. apply L.refl_ge.
elim (U pc); intros E F. rewrite F. reflexivity.
destruct (In_dec peq pc (successors instr)).
right. eapply no_self_loop; eauto.
left; auto.

elim (INV2 n); intro.

left. apply V. simpl. tauto.

assert (INV3: forall s instr', code!n = Some instr' -> In s (successors instr') -> st1.(aval)!!s = res!!s).

intros. elim (U s); intros C D. rewrite D. reflexivity.
destruct (In_dec peq s (successors instr)).
right. eapply multiple_predecessors with (n1 := pc) (n2 := n); eauto.
left; auto.
destruct (In_dec peq n (successors instr)).

destruct (basic_block_map n) eqn:BB.
right; intros.
elim (U n); intros C D. rewrite D. erewrite INV3; eauto.
tauto.
left. elim (U n); intros C D. elim (C i BB); intros. auto.

right; intros.
elim (U n); intros C D. rewrite D.
erewrite INV3; eauto.
tauto.
Qed.

Lemma propagate_successors_invariant_2:
forall pc res rem,
code!pc = None ->
state_invariant (mkstate res (pc :: rem)) ->
state_invariant (mkstate res rem).
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.propagate_successors_invariant_2".
intros until rem. intros CODE [INV1 INV2]. simpl in INV1. simpl in INV2.
split; simpl; intros.
apply INV1; auto.
destruct (INV2 n) as [[U | U] | U].
subst n. right; intros; congruence.
auto.
auto.
Qed.

Lemma initial_state_invariant:
state_invariant (mkstate (PMap.init L.top) (basic_block_list basic_block_map)).
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.initial_state_invariant".
split; simpl; intros.
apply PMap.gi.
right. intros. repeat rewrite PMap.gi. apply L.top_ge.
Qed.

Lemma analyze_invariant:
forall res,
fixpoint = Some res ->
state_invariant (mkstate res nil).
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.analyze_invariant".
unfold fixpoint; intros. pattern res.
eapply (PrimIter.iterate_prop _ _ (step basic_block_map)
state_invariant).

intros st INV. destruct st as [stin stwrk].
unfold step. simpl. destruct stwrk as [ | pc rem ] eqn:WRK.
auto.
destruct (code!pc) as [instr|] eqn:CODE.
eapply propagate_successors_invariant; eauto.
eapply propagate_successors_invariant_2; eauto.

eauto. apply initial_state_invariant.
Qed.



Theorem fixpoint_solution:
forall res n instr s,
fixpoint = Some res ->
code!n = Some instr -> In s (successors instr) ->
L.ge res!!s (transf n res!!n).
Proof. hammer_hook "Kildall" "Kildall.BACKWARD_DATAFLOW_SOLVER.fixpoint_solution".
intros.
assert (state_invariant (mkstate res nil)).
eapply analyze_invariant; eauto.
elim H2; simpl; intros.
elim (H4 n); intros.
contradiction.
eauto.
Qed.

Theorem fixpoint_entry:
forall res,
fixpoint = Some res ->
res!!entrypoint = L.top.
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.fixpoint_entry".
intros.
assert (state_invariant (mkstate res nil)).
eapply analyze_invariant; eauto.
elim H0; simpl; intros.
apply H1. unfold basic_block_map, is_basic_block_head.
fold predecessors. apply peq_true.
Qed.



Definition Pstate (st: state) : Prop :=
forall pc, P st.(aval)!!pc.

Lemma propagate_successors_P:
forall bb l,
P l ->
forall succs st,
Pstate st ->
Pstate (propagate_successors bb succs l st).
Proof. hammer_hook "Kildall" "Kildall.BBlock_solver.propagate_successors_P".
induction succs; simpl; intros.
auto.
case (bb a). auto.
apply IHsuccs. red; simpl; intros.
rewrite PMap.gsspec. case (peq pc a); intro.
auto. apply H0.
Qed.

Theorem fixpoint_invariant:
forall res pc, fixpoint = Some res -> P res!!pc.
Proof. hammer_hook "Kildall" "Kildall.Dataflow_Solver.fixpoint_invariant".
unfold fixpoint; intros. pattern res.
eapply (PrimIter.iterate_prop _ _ (step basic_block_map) Pstate).

intros st PS. unfold step. destruct (st.(worklist)).
apply PS.
assert (PS2: Pstate (mkstate st.(aval) l)).
red; intro; simpl. apply PS.
destruct (code!p) as [instr|] eqn:CODE.
apply propagate_successors_P. eauto. auto.
auto.

eauto.
red; intro; simpl. rewrite PMap.gi. apply Ptop.
Qed.

End Solver.

End BBlock_solver.





From compcert Require Import Heaps.

Module NodeSetForward <: NODE_SET.
Definition t := PHeap.t.
Definition empty := PHeap.empty.
Definition add (n: positive) (s: t) : t := PHeap.insert n s.
Definition pick (s: t) :=
match PHeap.findMax s with
| Some n => Some(n, PHeap.deleteMax s)
| None => None
end.
Definition all_nodes {A: Type} (code: PTree.t A) :=
PTree.fold (fun s pc instr => PHeap.insert pc s) code PHeap.empty.
Definition In := PHeap.In.

Lemma empty_spec:
forall n, ~In n empty.
Proof. hammer_hook "Kildall" "Kildall.NODE_SET.empty_spec".
intros. apply PHeap.In_empty.
Qed.

Lemma add_spec:
forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
Proof. hammer_hook "Kildall" "Kildall.NODE_SET.add_spec".
intros. rewrite PHeap.In_insert. unfold In. intuition.
Qed.

Lemma pick_none:
forall s n, pick s = None -> ~In n s.
Proof. hammer_hook "Kildall" "Kildall.NODE_SET.pick_none".
intros until n; unfold pick. caseEq (PHeap.findMax s); intros.
congruence.
apply PHeap.findMax_empty. auto.
Qed.

Lemma pick_some:
forall s n s', pick s = Some(n, s') ->
forall n', In n' s <-> n = n' \/ In n' s'.
Proof. hammer_hook "Kildall" "Kildall.NODE_SET.pick_some".
intros until s'; unfold pick. caseEq (PHeap.findMax s); intros.
inv H0.
generalize (PHeap.In_deleteMax s n n' H). unfold In. intuition.
congruence.
Qed.

Lemma all_nodes_spec:
forall A (code: PTree.t A) n instr,
code!n = Some instr -> In n (all_nodes code).
Proof. hammer_hook "Kildall" "Kildall.NODE_SET.all_nodes_spec".
intros A code n instr.
apply PTree_Properties.fold_rec with
(P := fun m set => m!n = Some instr -> In n set).

intros. apply H0. rewrite H. auto.

rewrite PTree.gempty. congruence.

intros. rewrite PTree.gsspec in H2. rewrite add_spec.
destruct (peq n k). auto. eauto.
Qed.
End NodeSetForward.

Module NodeSetBackward <: NODE_SET.
Definition t := PHeap.t.
Definition empty := PHeap.empty.
Definition add (n: positive) (s: t) : t := PHeap.insert n s.
Definition pick (s: t) :=
match PHeap.findMin s with
| Some n => Some(n, PHeap.deleteMin s)
| None => None
end.
Definition all_nodes {A: Type} (code: PTree.t A) :=
PTree.fold (fun s pc instr => PHeap.insert pc s) code PHeap.empty.
Definition In := PHeap.In.

Lemma empty_spec:
forall n, ~In n empty.
Proof. hammer_hook "Kildall" "Kildall.NodeSetForward.empty_spec". exact (NodeSetForward.empty_spec). Qed.

Lemma add_spec:
forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
Proof. hammer_hook "Kildall" "Kildall.NodeSetForward.add_spec". exact (NodeSetForward.add_spec). Qed.

Lemma pick_none:
forall s n, pick s = None -> ~In n s.
Proof. hammer_hook "Kildall" "Kildall.NodeSetForward.pick_none".
intros until n; unfold pick. caseEq (PHeap.findMin s); intros.
congruence.
apply PHeap.findMin_empty. auto.
Qed.

Lemma pick_some:
forall s n s', pick s = Some(n, s') ->
forall n', In n' s <-> n = n' \/ In n' s'.
Proof. hammer_hook "Kildall" "Kildall.NodeSetForward.pick_some".
intros until s'; unfold pick. caseEq (PHeap.findMin s); intros.
inv H0.
generalize (PHeap.In_deleteMin s n n' H). unfold In. intuition.
congruence.
Qed.

Lemma all_nodes_spec:
forall A (code: PTree.t A) n instr,
code!n = Some instr -> In n (all_nodes code).
Proof. hammer_hook "Kildall" "Kildall.NodeSetForward.all_nodes_spec". exact (NodeSetForward.all_nodes_spec). Qed.
End NodeSetBackward.

