From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Lattice.
From compcert Require Import AST.
From compcert Require Import Op.
From compcert Require Import Registers.
From compcert Require Import RTL.
From compcert Require Import Kildall.



Notation reg_live := Regset.add.
Notation reg_dead := Regset.remove.

Definition reg_option_live (or: option reg) (lv: Regset.t) :=
match or with None => lv | Some r => reg_live r lv end.

Definition reg_sum_live (ros: reg + ident) (lv: Regset.t) :=
match ros with inl r => reg_live r lv | inr s => lv end.

Fixpoint reg_list_live
(rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
match rl with
| nil => lv
| r1 :: rs => reg_list_live rs (reg_live r1 lv)
end.

Fixpoint reg_list_dead
(rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
match rl with
| nil => lv
| r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
end.



Definition transfer
(f: function) (pc: node) (after: Regset.t) : Regset.t :=
match f.(fn_code)!pc with
| None =>
Regset.empty
| Some i =>
match i with
| Inop s =>
after
| Iop op args res s =>
if Regset.mem res after then
reg_list_live args (reg_dead res after)
else
after
| Iload chunk addr args dst s =>
if Regset.mem dst after then
reg_list_live args (reg_dead dst after)
else
after
| Istore chunk addr args src s =>
reg_list_live args (reg_live src after)
| Icall sig ros args res s =>
reg_list_live args
(reg_sum_live ros (reg_dead res after))
| Itailcall sig ros args =>
reg_list_live args (reg_sum_live ros Regset.empty)
| Ibuiltin ef args res s =>
reg_list_live (params_of_builtin_args args)
(reg_list_dead (params_of_builtin_res res) after)
| Icond cond args ifso ifnot =>
reg_list_live args after
| Ijumptable arg tbl =>
reg_live arg after
| Ireturn optarg =>
reg_option_live optarg Regset.empty
end
end.



Module RegsetLat := LFSet(Regset).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).

Definition analyze (f: function): option (PMap.t Regset.t) :=
DS.fixpoint f.(fn_code) successors_instr (transfer f).



Lemma analyze_solution:
forall f live n i s,
analyze f = Some live ->
f.(fn_code)!n = Some i ->
In s (successors_instr i) ->
Regset.Subset (transfer f s live!!s) live!!n.
Proof. hammer_hook "Liveness" "Liveness.analyze_solution".
unfold analyze; intros. eapply DS.fixpoint_solution; eauto.
intros. unfold transfer; rewrite H2. apply DS.L.eq_refl.
Qed.



Definition last_uses_at (live: PMap.t Regset.t) (pc: node) (i: instruction) : list reg :=
let l := live!!pc in
let lu := List.filter (fun r => negb (Regset.mem r l)) (instr_uses i) in
match instr_defs i with
| None => lu
| Some r => if Regset.mem r l then lu else r :: lu
end.

Definition last_uses (f: function) : PTree.t (list reg) :=
match analyze f with
| None => PTree.empty (list reg)
| Some live => PTree.map (last_uses_at live) f.(fn_code)
end.


