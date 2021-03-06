From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import Wfsimpl.
From compcert Require Import Maps.
From compcert Require Import Errors.
From compcert Require Import Integers.
From compcert Require Import AST.
From compcert Require Import Linking.
From compcert Require Import Op.
From compcert Require Import Registers.
From compcert Require Import RTL.





Definition funenv : Type := PTree.t function.

Definition size_fenv (fenv: funenv) := PTree_Properties.cardinal fenv.

Parameter inlining_info: Type.

Parameter inlining_analysis: program -> inlining_info.

Parameter should_inline: inlining_info -> ident -> function -> bool.

Definition add_globdef (io: inlining_info) (fenv: funenv) (idg: ident * globdef fundef unit) : funenv :=
match idg with
| (id, Gfun (Internal f)) =>
if should_inline io id f
then PTree.set id f fenv
else PTree.remove id fenv
| (id, _) =>
PTree.remove id fenv
end.

Definition funenv_program (p: program) : funenv :=
let io := inlining_analysis p in
List.fold_left (add_globdef io) p.(prog_defs) (PTree.empty function).





Record state : Type := mkstate {
st_nextreg: positive;
st_nextnode: positive;
st_code: code;
st_stksize: Z
}.



Inductive sincr (s1 s2: state) : Prop :=
Sincr (NEXTREG: Ple s1.(st_nextreg) s2.(st_nextreg))
(NEXTNODE: Ple s1.(st_nextnode) s2.(st_nextnode))
(STKSIZE: s1.(st_stksize) <= s2.(st_stksize)).

Remark sincr_refl: forall s, sincr s s.
Proof. hammer_hook "Inlining" "Inlining.sincr_refl".
intros; constructor; xomega.
Qed.

Lemma sincr_trans: forall s1 s2 s3, sincr s1 s2 -> sincr s2 s3 -> sincr s1 s3.
Proof. hammer_hook "Inlining" "Inlining.sincr_trans".
intros. inv H; inv H0. constructor; xomega.
Qed.



Inductive res {A: Type} {s: state}: Type := R (x: A) (s': state) (I: sincr s s').

Definition mon (A: Type) : Type := forall (s: state), @res A s.



Definition ret {A: Type} (x: A): mon A :=
fun s => R x s (sincr_refl s).

Definition bind {A B: Type} (x: mon A) (f: A -> mon B): mon B :=
fun s1 => match x s1 with R vx s2 I1 =>
match f vx s2 with R vy s3 I2 =>
R vy s3 (sincr_trans s1 s2 s3 I1 I2)
end
end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
(at level 200, X ident, A at level 100, B at level 200).

Definition initstate :=
mkstate 1%positive 1%positive (PTree.empty instruction) 0.

Program Definition set_instr (pc: node) (i: instruction): mon unit :=
fun s =>
R tt
(mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set pc i s.(st_code)) s.(st_stksize))
_.
Next Obligation.
intros; constructor; simpl; xomega.
Qed.

Program Definition add_instr (i: instruction): mon node :=
fun s =>
let pc := s.(st_nextnode) in
R pc
(mkstate s.(st_nextreg) (Pos.succ pc) (PTree.set pc i s.(st_code)) s.(st_stksize))
_.
Next Obligation.
intros; constructor; simpl; xomega.
Qed.

Program Definition reserve_nodes (numnodes: positive): mon positive :=
fun s =>
R s.(st_nextnode)
(mkstate s.(st_nextreg) (Pos.add s.(st_nextnode) numnodes) s.(st_code) s.(st_stksize))
_.
Next Obligation.
intros; constructor; simpl; xomega.
Qed.

Program Definition reserve_regs (numregs: positive): mon positive :=
fun s =>
R s.(st_nextreg)
(mkstate (Pos.add s.(st_nextreg) numregs) s.(st_nextnode) s.(st_code) s.(st_stksize))
_.
Next Obligation.
intros; constructor; simpl; xomega.
Qed.

Program Definition request_stack (sz: Z): mon unit :=
fun s =>
R tt
(mkstate s.(st_nextreg) s.(st_nextnode) s.(st_code) (Z.max s.(st_stksize) sz))
_.
Next Obligation.
intros; constructor; simpl; xomega.
Qed.

Program Definition ptree_mfold {A: Type} (f: positive -> A -> mon unit) (t: PTree.t A): mon unit :=
fun s =>
R tt
(PTree.fold (fun s1 k v => match f k v s1 return _ with R _ s2 _ => s2 end) t s)
_.
Next Obligation.
apply PTree_Properties.fold_rec.
auto.
apply sincr_refl.
intros. destruct (f k v a). eapply sincr_trans; eauto.
Qed.





Record context: Type := mkcontext {
dpc: positive;
dreg: positive;
dstk: Z;
mreg: positive;
mstk: Z;
retinfo: option(node * reg)

}.



Definition shiftpos (p amount: positive) := Pos.pred (Pos.add p amount).

Definition spc (ctx: context) (pc: node) := shiftpos pc ctx.(dpc).

Definition sreg (ctx: context) (r: reg) := shiftpos r ctx.(dreg).

Definition sregs (ctx: context) (rl: list reg) := List.map (sreg ctx) rl.

Definition sros (ctx: context) (ros: reg + ident) := sum_left_map (sreg ctx) ros.

Definition sop (ctx: context) (op: operation) :=
shift_stack_operation ctx.(dstk) op.

Definition saddr (ctx: context) (addr: addressing) :=
shift_stack_addressing ctx.(dstk) addr.

Fixpoint sbuiltinarg (ctx: context) (a: builtin_arg reg) : builtin_arg reg :=
match a with
| BA x => BA (sreg ctx x)
| BA_loadstack chunk ofs => BA_loadstack chunk (Ptrofs.add ofs (Ptrofs.repr ctx.(dstk)))
| BA_addrstack ofs => BA_addrstack (Ptrofs.add ofs (Ptrofs.repr ctx.(dstk)))
| BA_splitlong hi lo => BA_splitlong (sbuiltinarg ctx hi) (sbuiltinarg ctx lo)
| BA_addptr a1 a2 => BA_addptr (sbuiltinarg ctx a1) (sbuiltinarg ctx a2)
| _ => a
end.

Definition sbuiltinres (ctx: context) (a: builtin_res reg) : builtin_res reg :=
match a with
| BR x => BR (sreg ctx x)
| _    => BR_none
end.



Definition initcontext (dpc dreg nreg: positive) (sz: Z) :=
{| dpc := dpc;
dreg := dreg;
dstk := 0;
mreg := nreg;
mstk := Z.max sz 0;
retinfo := None |}.



Definition min_alignment (sz: Z) :=
if zle sz 1 then 1
else if zle sz 2 then 2
else if zle sz 4 then 4 else 8.

Definition callcontext (ctx: context)
(dpc dreg nreg: positive) (sz: Z)
(retpc: node) (retreg: reg) :=
{| dpc := dpc;
dreg := dreg;
dstk := align (ctx.(dstk) + ctx.(mstk)) (min_alignment sz);
mreg := nreg;
mstk := Z.max sz 0;
retinfo := Some (spc ctx retpc, sreg ctx retreg) |}.



Definition tailcontext (ctx: context) (dpc dreg nreg: positive) (sz: Z) :=
{| dpc := dpc;
dreg := dreg;
dstk := align ctx.(dstk) (min_alignment sz);
mreg := nreg;
mstk := Z.max sz 0;
retinfo := ctx.(retinfo) |}.





Fixpoint add_moves (srcs dsts: list reg) (succ: node): mon node :=
match srcs, dsts with
| s1 :: sl, d1 :: dl =>
do n <- add_instr (Iop Omove (s1 :: nil) d1 succ);
add_moves sl dl n
| _, _ =>
ret succ
end.



Section EXPAND_CFG.

Variable fenv: funenv.



Variable rec: forall fenv', (size_fenv fenv' < size_fenv fenv)%nat -> context -> function -> mon unit.



Inductive inline_decision (ros: reg + ident) : Type :=
| Cannot_inline
| Can_inline (id: ident) (f: function) (P: ros = inr reg id) (Q: fenv!id = Some f).

Program Definition can_inline (ros: reg + ident): inline_decision ros :=
match ros with
| inl r => Cannot_inline _
| inr id => match fenv!id with Some f => Can_inline _ id f _ _ | None => Cannot_inline _ end
end.



Definition inline_function (ctx: context) (id: ident) (f: function)
(P: PTree.get id fenv = Some f)
(args: list reg)
(retpc: node) (retreg: reg) : mon node :=
let npc := max_pc_function f in
let nreg := max_reg_function f in
do dpc <- reserve_nodes npc;
do dreg <- reserve_regs nreg;
let ctx' := callcontext ctx dpc dreg nreg f.(fn_stacksize) retpc retreg in
do x <- rec (PTree.remove id fenv) (PTree_Properties.cardinal_remove P) ctx' f;
add_moves (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)).



Definition inline_tail_function (ctx: context) (id: ident) (f: function)
(P: PTree.get id fenv = Some f)
(args: list reg): mon node :=
let npc := max_pc_function f in
let nreg := max_reg_function f in
do dpc <- reserve_nodes npc;
do dreg <- reserve_regs nreg;
let ctx' := tailcontext ctx dpc dreg nreg f.(fn_stacksize) in
do x <- rec (PTree.remove id fenv) (PTree_Properties.cardinal_remove P) ctx' f;
add_moves (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)).



Definition inline_return (ctx: context) (or: option reg) (retinfo: node * reg) :=
match retinfo, or with
| (retpc, retreg), Some r => Iop Omove (sreg ctx r :: nil) retreg retpc
| (retpc, retreg), None   => Inop retpc
end.



Definition expand_instr (ctx: context) (pc: node) (i: instruction): mon unit :=
match i with
| Inop s =>
set_instr (spc ctx pc) (Inop (spc ctx s))
| Iop op args res s =>
set_instr (spc ctx pc)
(Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s))
| Iload chunk addr args dst s =>
set_instr (spc ctx pc)
(Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx dst) (spc ctx s))
| Istore chunk addr args src s =>
set_instr (spc ctx pc)
(Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s))
| Icall sg ros args res s =>
match can_inline ros with
| Cannot_inline =>
set_instr (spc ctx pc)
(Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s))
| Can_inline id f P Q =>
do n <- inline_function ctx id f Q args s res;
set_instr (spc ctx pc) (Inop n)
end
| Itailcall sg ros args =>
match can_inline ros with
| Cannot_inline =>
match ctx.(retinfo) with
| None =>
set_instr (spc ctx pc)
(Itailcall sg (sros ctx ros) (sregs ctx args))
| Some(rpc, rreg) =>
set_instr (spc ctx pc)
(Icall sg (sros ctx ros) (sregs ctx args) rreg rpc)
end
| Can_inline id f P Q =>
do n <- inline_tail_function ctx id f Q args;
set_instr (spc ctx pc) (Inop n)
end
| Ibuiltin ef args res s =>
set_instr (spc ctx pc)
(Ibuiltin ef (map (sbuiltinarg ctx) args) (sbuiltinres ctx res) (spc ctx s))
| Icond cond args s1 s2 =>
set_instr (spc ctx pc)
(Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2))
| Ijumptable r tbl =>
set_instr (spc ctx pc)
(Ijumptable (sreg ctx r) (List.map (spc ctx) tbl))
| Ireturn or =>
match ctx.(retinfo) with
| None =>
set_instr (spc ctx pc) (Ireturn (option_map (sreg ctx) or))
| Some rinfo =>
set_instr (spc ctx pc) (inline_return ctx or rinfo)
end
end.



Definition expand_cfg_rec (ctx: context) (f: function): mon unit :=
do x <- request_stack (ctx.(dstk) + ctx.(mstk));
ptree_mfold (expand_instr ctx) f.(fn_code).

End EXPAND_CFG.



Definition expand_cfg := Fixm size_fenv expand_cfg_rec.



Definition expand_function (fenv: funenv) (f: function): mon context :=
let npc := max_pc_function f in
let nreg := max_reg_function f in
do dpc <- reserve_nodes npc;
do dreg <- reserve_regs nreg;
let ctx := initcontext dpc dreg nreg f.(fn_stacksize) in
do x <- expand_cfg fenv ctx f;
ret ctx.



Local Open Scope string_scope.



Definition transf_function (fenv: funenv) (f: function) : Errors.res function :=
let '(R ctx s _) := expand_function fenv f initstate in
if zlt s.(st_stksize) Ptrofs.max_unsigned then
OK (mkfunction f.(fn_sig)
(sregs ctx f.(fn_params))
s.(st_stksize)
s.(st_code)
(spc ctx f.(fn_entrypoint)))
else
Error(msg "Inlining: stack too big").

Definition transf_fundef (fenv: funenv) (fd: fundef) : Errors.res fundef :=
AST.transf_partial_fundef (transf_function fenv) fd.

Definition transf_program (p: program): Errors.res program :=
let fenv := funenv_program p in
AST.transform_partial_program (transf_fundef fenv) p.

