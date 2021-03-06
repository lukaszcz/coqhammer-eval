From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Values.
From compcert Require Import Events.
From compcert Require Import Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Smallstep.
From compcert Require Import Op.
From compcert Require Import Registers.





Definition node := positive.

Inductive instruction: Type :=
| Inop: node -> instruction

| Iop: operation -> list reg -> reg -> node -> instruction

| Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction

| Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction

| Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction

| Itailcall: signature -> reg + ident -> list reg -> instruction

| Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction

| Icond: condition -> list reg -> node -> node -> instruction

| Ijumptable: reg -> list node -> instruction

| Ireturn: option reg -> instruction.


Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
fn_sig: signature;
fn_params: list reg;
fn_stacksize: Z;
fn_code: code;
fn_entrypoint: node
}.



Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
match fd with
| Internal f => fn_sig f
| External ef => ef_sig ef
end.



Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
match rl, vl with
| r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
| _, _ => Regmap.init Vundef
end.



Inductive stackframe : Type :=
| Stackframe:
forall (res: reg)
(f: function)
(sp: val)
(pc: node)
(rs: regset),
stackframe.

Inductive state : Type :=
| State:
forall (stack: list stackframe)
(f: function)
(sp: val)
(pc: node)
(rs: regset)
(m: mem),
state
| Callstate:
forall (stack: list stackframe)
(f: fundef)
(args: list val)
(m: mem),
state
| Returnstate:
forall (stack: list stackframe)
(v: val)
(m: mem),
state.

Section RELSEM.

Variable ge: genv.

Definition find_function
(ros: reg + ident) (rs: regset) : option fundef :=
match ros with
| inl r => Genv.find_funct ge rs#r
| inr symb =>
match Genv.find_symbol ge symb with
| None => None
| Some b => Genv.find_funct_ptr ge b
end
end.



Inductive step: state -> trace -> state -> Prop :=
| exec_Inop:
forall s f sp pc rs m pc',
(fn_code f)!pc = Some(Inop pc') ->
step (State s f sp pc rs m)
E0 (State s f sp pc' rs m)
| exec_Iop:
forall s f sp pc rs m op args res pc' v,
(fn_code f)!pc = Some(Iop op args res pc') ->
eval_operation ge sp op rs##args m = Some v ->
step (State s f sp pc rs m)
E0 (State s f sp pc' (rs#res <- v) m)
| exec_Iload:
forall s f sp pc rs m chunk addr args dst pc' a v,
(fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
eval_addressing ge sp addr rs##args = Some a ->
Mem.loadv chunk m a = Some v ->
step (State s f sp pc rs m)
E0 (State s f sp pc' (rs#dst <- v) m)
| exec_Istore:
forall s f sp pc rs m chunk addr args src pc' a m',
(fn_code f)!pc = Some(Istore chunk addr args src pc') ->
eval_addressing ge sp addr rs##args = Some a ->
Mem.storev chunk m a rs#src = Some m' ->
step (State s f sp pc rs m)
E0 (State s f sp pc' rs m')
| exec_Icall:
forall s f sp pc rs m sig ros args res pc' fd,
(fn_code f)!pc = Some(Icall sig ros args res pc') ->
find_function ros rs = Some fd ->
funsig fd = sig ->
step (State s f sp pc rs m)
E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
| exec_Itailcall:
forall s f stk pc rs m sig ros args fd m',
(fn_code f)!pc = Some(Itailcall sig ros args) ->
find_function ros rs = Some fd ->
funsig fd = sig ->
Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
step (State s f (Vptr stk Ptrofs.zero) pc rs m)
E0 (Callstate s fd rs##args m')
| exec_Ibuiltin:
forall s f sp pc rs m ef args res pc' vargs t vres m',
(fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
external_call ef ge vargs m t vres m' ->
step (State s f sp pc rs m)
t (State s f sp pc' (regmap_setres res vres rs) m')
| exec_Icond:
forall s f sp pc rs m cond args ifso ifnot b pc',
(fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
eval_condition cond rs##args m = Some b ->
pc' = (if b then ifso else ifnot) ->
step (State s f sp pc rs m)
E0 (State s f sp pc' rs m)
| exec_Ijumptable:
forall s f sp pc rs m arg tbl n pc',
(fn_code f)!pc = Some(Ijumptable arg tbl) ->
rs#arg = Vint n ->
list_nth_z tbl (Int.unsigned n) = Some pc' ->
step (State s f sp pc rs m)
E0 (State s f sp pc' rs m)
| exec_Ireturn:
forall s f stk pc rs m or m',
(fn_code f)!pc = Some(Ireturn or) ->
Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
step (State s f (Vptr stk Ptrofs.zero) pc rs m)
E0 (Returnstate s (regmap_optget or Vundef rs) m')
| exec_function_internal:
forall s f args m m' stk,
Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
step (Callstate s (Internal f) args m)
E0 (State s
f
(Vptr stk Ptrofs.zero)
f.(fn_entrypoint)
(init_regs args f.(fn_params))
m')
| exec_function_external:
forall s ef args res t m m',
external_call ef ge args m t res m' ->
step (Callstate s (External ef) args m)
t (Returnstate s res m')
| exec_return:
forall res f sp pc rs s vres m,
step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
E0 (State s f sp pc (rs#res <- vres) m).

Lemma exec_Iop':
forall s f sp pc rs m op args res pc' rs' v,
(fn_code f)!pc = Some(Iop op args res pc') ->
eval_operation ge sp op rs##args m = Some v ->
rs' = (rs#res <- v) ->
step (State s f sp pc rs m)
E0 (State s f sp pc' rs' m).
Proof. hammer_hook "RTL" "RTL.exec_Iop'".
intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
forall s f sp pc rs m chunk addr args dst pc' rs' a v,
(fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
eval_addressing ge sp addr rs##args = Some a ->
Mem.loadv chunk m a = Some v ->
rs' = (rs#dst <- v) ->
step (State s f sp pc rs m)
E0 (State s f sp pc' rs' m).
Proof. hammer_hook "RTL" "RTL.exec_Iload'".
intros. subst rs'. eapply exec_Iload; eauto.
Qed.

End RELSEM.



Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
let ge := Genv.globalenv p in
Genv.init_mem p = Some m0 ->
Genv.find_symbol ge p.(prog_main) = Some b ->
Genv.find_funct_ptr ge b = Some f ->
funsig f = signature_main ->
initial_state p (Callstate nil f nil m0).



Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
final_state (Returnstate nil (Vint r) m) r.



Definition semantics (p: program) :=
Semantics step (initial_state p) final_state (Genv.globalenv p).



Lemma semantics_receptive:
forall (p: program), receptive (semantics p).
Proof. hammer_hook "RTL" "RTL.semantics_receptive".
intros. constructor; simpl; intros.

assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
intros. subst. inv H0. exists s1; auto.
inversion H; subst; auto.
exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
exists (State s0 f sp pc' (regmap_setres res vres2 rs) m2). eapply exec_Ibuiltin; eauto.
exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
exists (Returnstate s0 vres2 m2). econstructor; eauto.

red; intros; inv H; simpl; try omega.
eapply external_call_trace_length; eauto.
eapply external_call_trace_length; eauto.
Qed.





Section TRANSF.

Variable transf: node -> instruction -> instruction.

Definition transf_function (f: function) : function :=
mkfunction
f.(fn_sig)
f.(fn_params)
f.(fn_stacksize)
(PTree.map transf f.(fn_code))
f.(fn_entrypoint).

End TRANSF.



Definition successors_instr (i: instruction) : list node :=
match i with
| Inop s => s :: nil
| Iop op args res s => s :: nil
| Iload chunk addr args dst s => s :: nil
| Istore chunk addr args src s => s :: nil
| Icall sig ros args res s => s :: nil
| Itailcall sig ros args => nil
| Ibuiltin ef args res s => s :: nil
| Icond cond args ifso ifnot => ifso :: ifnot :: nil
| Ijumptable arg tbl => tbl
| Ireturn optarg => nil
end.

Definition successors_map (f: function) : PTree.t (list node) :=
PTree.map1 successors_instr f.(fn_code).



Definition instr_uses (i: instruction) : list reg :=
match i with
| Inop s => nil
| Iop op args res s => args
| Iload chunk addr args dst s => args
| Istore chunk addr args src s => src :: args
| Icall sig (inl r) args res s => r :: args
| Icall sig (inr id) args res s => args
| Itailcall sig (inl r) args => r :: args
| Itailcall sig (inr id) args => args
| Ibuiltin ef args res s => params_of_builtin_args args
| Icond cond args ifso ifnot => args
| Ijumptable arg tbl => arg :: nil
| Ireturn None => nil
| Ireturn (Some arg) => arg :: nil
end.



Definition instr_defs (i: instruction) : option reg :=
match i with
| Inop s => None
| Iop op args res s => Some res
| Iload chunk addr args dst s => Some dst
| Istore chunk addr args src s => None
| Icall sig ros args res s => Some res
| Itailcall sig ros args => None
| Ibuiltin ef args res s =>
match res with BR r => Some r | _ => None end
| Icond cond args ifso ifnot => None
| Ijumptable arg tbl => None
| Ireturn optarg => None
end.



Definition max_pc_function (f: function) :=
PTree.fold (fun m pc i => Pos.max m pc) f.(fn_code) 1%positive.

Lemma max_pc_function_sound:
forall f pc i, f.(fn_code)!pc = Some i -> Ple pc (max_pc_function f).
Proof. hammer_hook "RTL" "RTL.max_pc_function_sound".
intros until i. unfold max_pc_function.
apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).

intros. apply H0. rewrite H; auto.

rewrite PTree.gempty. congruence.

intros. rewrite PTree.gsspec in H2. destruct (peq pc k).
inv H2. xomega.
apply Ple_trans with a. auto. xomega.
Qed.



Definition max_reg_instr (m: positive) (pc: node) (i: instruction) :=
match i with
| Inop s => m
| Iop op args res s => fold_left Pos.max args (Pos.max res m)
| Iload chunk addr args dst s => fold_left Pos.max args (Pos.max dst m)
| Istore chunk addr args src s => fold_left Pos.max args (Pos.max src m)
| Icall sig (inl r) args res s => fold_left Pos.max args (Pos.max r (Pos.max res m))
| Icall sig (inr id) args res s => fold_left Pos.max args (Pos.max res m)
| Itailcall sig (inl r) args => fold_left Pos.max args (Pos.max r m)
| Itailcall sig (inr id) args => fold_left Pos.max args m
| Ibuiltin ef args res s =>
fold_left Pos.max (params_of_builtin_args args)
(fold_left Pos.max (params_of_builtin_res res) m)
| Icond cond args ifso ifnot => fold_left Pos.max args m
| Ijumptable arg tbl => Pos.max arg m
| Ireturn None => m
| Ireturn (Some arg) => Pos.max arg m
end.

Definition max_reg_function (f: function) :=
Pos.max
(PTree.fold max_reg_instr f.(fn_code) 1%positive)
(fold_left Pos.max f.(fn_params) 1%positive).

Remark max_reg_instr_ge:
forall m pc i, Ple m (max_reg_instr m pc i).
Proof. hammer_hook "RTL" "RTL.max_reg_instr_ge".
intros.
assert (X: forall l n, Ple m n -> Ple m (fold_left Pos.max l n)).
{ induction l; simpl; intros.
auto.
apply IHl. xomega. }
destruct i; simpl; try (destruct s0); repeat (apply X); try xomega.
destruct o; xomega.
Qed.

Remark max_reg_instr_def:
forall m pc i r, instr_defs i = Some r -> Ple r (max_reg_instr m pc i).
Proof. hammer_hook "RTL" "RTL.max_reg_instr_def".
intros.
assert (X: forall l n, Ple r n -> Ple r (fold_left Pos.max l n)).
{ induction l; simpl; intros. xomega. apply IHl. xomega. }
destruct i; simpl in *; inv H.
- apply X. xomega.
- apply X. xomega.
- destruct s0; apply X; xomega.
- destruct b; inv H1. apply X. simpl. xomega.
Qed.

Remark max_reg_instr_uses:
forall m pc i r, In r (instr_uses i) -> Ple r (max_reg_instr m pc i).
Proof. hammer_hook "RTL" "RTL.max_reg_instr_uses".
intros.
assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pos.max l n)).
{ induction l; simpl; intros.
tauto.
apply IHl. destruct H0 as [[A|A]|A]. right; subst; xomega. auto. right; xomega. }
destruct i; simpl in *; try (destruct s0); try (apply X; auto).
- contradiction.
- destruct H. right; subst; xomega. auto.
- destruct H. right; subst; xomega. auto.
- destruct H. right; subst; xomega. auto.
- intuition. subst; xomega.
- destruct o; simpl in H; intuition. subst; xomega.
Qed.

Lemma max_reg_function_def:
forall f pc i r,
f.(fn_code)!pc = Some i -> instr_defs i = Some r -> Ple r (max_reg_function f).
Proof. hammer_hook "RTL" "RTL.max_reg_function_def".
intros.
assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
{  revert H.
apply PTree_Properties.fold_rec with
(P := fun c m => c!pc = Some i -> Ple r m).
- intros. rewrite H in H1; auto.
- rewrite PTree.gempty; congruence.
- intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
+ inv H3. eapply max_reg_instr_def; eauto.
+ apply Ple_trans with a. auto. apply max_reg_instr_ge.
}
unfold max_reg_function. xomega.
Qed.

Lemma max_reg_function_use:
forall f pc i r,
f.(fn_code)!pc = Some i -> In r (instr_uses i) -> Ple r (max_reg_function f).
Proof. hammer_hook "RTL" "RTL.max_reg_function_use".
intros.
assert (Ple r (PTree.fold max_reg_instr f.(fn_code) 1%positive)).
{  revert H.
apply PTree_Properties.fold_rec with
(P := fun c m => c!pc = Some i -> Ple r m).
- intros. rewrite H in H1; auto.
- rewrite PTree.gempty; congruence.
- intros. rewrite PTree.gsspec in H3. destruct (peq pc k).
+ inv H3. eapply max_reg_instr_uses; eauto.
+ apply Ple_trans with a. auto. apply max_reg_instr_ge.
}
unfold max_reg_function. xomega.
Qed.

Lemma max_reg_function_params:
forall f r, In r f.(fn_params) -> Ple r (max_reg_function f).
Proof. hammer_hook "RTL" "RTL.max_reg_function_params".
intros.
assert (X: forall l n, In r l \/ Ple r n -> Ple r (fold_left Pos.max l n)).
{ induction l; simpl; intros.
tauto.
apply IHl. destruct H0 as [[A|A]|A]. right; subst; xomega. auto. right; xomega. }
assert (Y: Ple r (fold_left Pos.max f.(fn_params) 1%positive)).
{ apply X; auto. }
unfold max_reg_function. xomega.
Qed.
