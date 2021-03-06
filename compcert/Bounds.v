From Hammer Require Import Hammer.















Require Import FSets.
Require Import FSetAVL.
From compcert Require Import Coqlib.
From compcert Require Import Ordered.
From compcert Require Intv.
From compcert Require Import AST.
From compcert Require Import Op.
From compcert Require Import Machregs.
From compcert Require Import Locations.
From compcert Require Import Linear.
From compcert Require Import Conventions.

Module RegOrd := OrderedIndexed (IndexedMreg).
Module RegSet := FSetAVL.Make (RegOrd).







Record bounds : Type := mkbounds {
used_callee_save: list mreg;
bound_local: Z;
bound_outgoing: Z;
bound_stack_data: Z;
bound_local_pos: bound_local >= 0;
bound_outgoing_pos: bound_outgoing >= 0;
bound_stack_data_pos: bound_stack_data >= 0;
used_callee_save_norepet: list_norepet used_callee_save;
used_callee_save_prop: forall r, In r used_callee_save -> is_callee_save r = true
}.



Section WITHIN_BOUNDS.

Variable b: bounds.

Definition mreg_within_bounds (r: mreg) :=
is_callee_save r = true -> In r (used_callee_save b).

Definition slot_within_bounds (sl: slot) (ofs: Z) (ty: typ) :=
match sl with
| Local => ofs + typesize ty <= bound_local b
| Outgoing => ofs + typesize ty <= bound_outgoing b
| Incoming => True
end.

Definition instr_within_bounds (i: instruction) :=
match i with
| Lgetstack sl ofs ty r => slot_within_bounds sl ofs ty /\ mreg_within_bounds r
| Lsetstack r sl ofs ty => slot_within_bounds sl ofs ty
| Lop op args res => mreg_within_bounds res
| Lload chunk addr args dst => mreg_within_bounds dst
| Lcall sig ros => size_arguments sig <= bound_outgoing b
| Lbuiltin ef args res =>
(forall r, In r (params_of_builtin_res res) \/ In r (destroyed_by_builtin ef) -> mreg_within_bounds r)
/\ (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args args) -> slot_within_bounds sl ofs ty)
| _ => True
end.

End WITHIN_BOUNDS.

Definition function_within_bounds (f: function) (b: bounds) : Prop :=
forall instr, In instr f.(fn_code) -> instr_within_bounds b instr.





Section BOUNDS.

Variable f: function.

Definition record_reg (u: RegSet.t) (r: mreg) : RegSet.t :=
if is_callee_save r then RegSet.add r u else u.

Definition record_regs (u: RegSet.t) (rl: list mreg) : RegSet.t :=
fold_left record_reg rl u.



Definition record_regs_of_instr (u: RegSet.t) (i: instruction) : RegSet.t :=
match i with
| Lgetstack sl ofs ty r => record_reg u r
| Lsetstack r sl ofs ty => record_reg u r
| Lop op args res => record_reg u res
| Lload chunk addr args dst => record_reg u dst
| Lstore chunk addr args src => u
| Lcall sig ros => u
| Ltailcall sig ros => u
| Lbuiltin ef args res =>
record_regs (record_regs u (params_of_builtin_res res)) (destroyed_by_builtin ef)
| Llabel lbl => u
| Lgoto lbl => u
| Lcond cond args lbl => u
| Ljumptable arg tbl => u
| Lreturn => u
end.

Definition record_regs_of_function : RegSet.t :=
fold_left record_regs_of_instr f.(fn_code) RegSet.empty.

Fixpoint slots_of_locs (l: list loc) : list (slot * Z * typ) :=
match l with
| nil => nil
| S sl ofs ty :: l' => (sl, ofs, ty) :: slots_of_locs l'
| R r :: l' => slots_of_locs l'
end.

Definition slots_of_instr (i: instruction) : list (slot * Z * typ) :=
match i with
| Lgetstack sl ofs ty r => (sl, ofs, ty) :: nil
| Lsetstack r sl ofs ty => (sl, ofs, ty) :: nil
| Lbuiltin ef args res => slots_of_locs (params_of_builtin_args args)
| _ => nil
end.

Definition max_over_list {A: Type} (valu: A -> Z) (l: list A) : Z :=
List.fold_left (fun m l => Z.max m (valu l)) l 0.

Definition max_over_instrs (valu: instruction -> Z) : Z :=
max_over_list valu f.(fn_code).

Definition max_over_slots_of_instr (valu: slot * Z * typ -> Z) (i: instruction) : Z :=
max_over_list valu (slots_of_instr i).

Definition max_over_slots_of_funct (valu: slot * Z * typ -> Z) : Z :=
max_over_instrs (max_over_slots_of_instr valu).

Definition local_slot (s: slot * Z * typ) :=
match s with (Local, ofs, ty) => ofs + typesize ty | _ => 0 end.

Definition outgoing_slot (s: slot * Z * typ) :=
match s with (Outgoing, ofs, ty) => ofs + typesize ty | _ => 0 end.

Definition outgoing_space (i: instruction) :=
match i with Lcall sig _ => size_arguments sig | _ => 0 end.

Lemma max_over_list_pos:
forall (A: Type) (valu: A -> Z) (l: list A),
max_over_list valu l >= 0.
Proof. hammer_hook "Bounds" "Bounds.max_over_list_pos".
intros until valu. unfold max_over_list.
assert (forall l z, fold_left (fun x y => Z.max x (valu y)) l z >= z).
induction l; simpl; intros.
omega. apply Zge_trans with (Z.max z (valu a)).
auto. apply Z.le_ge. apply Z.le_max_l. auto.
Qed.

Lemma max_over_slots_of_funct_pos:
forall (valu: slot * Z * typ -> Z), max_over_slots_of_funct valu >= 0.
Proof. hammer_hook "Bounds" "Bounds.max_over_slots_of_funct_pos".
intros. unfold max_over_slots_of_funct.
unfold max_over_instrs. apply max_over_list_pos.
Qed.



Remark fold_left_preserves:
forall (A B: Type) (f: A -> B -> A) (P: A -> Prop),
(forall a b, P a -> P (f a b)) ->
forall l a, P a -> P (fold_left f l a).
Proof. hammer_hook "Bounds" "Bounds.fold_left_preserves".
induction l; simpl; auto.
Qed.

Remark fold_left_ensures:
forall (A B: Type) (f: A -> B -> A) (P: A -> Prop) b0,
(forall a b, P a -> P (f a b)) ->
(forall a, P (f a b0)) ->
forall l a, In b0 l -> P (fold_left f l a).
Proof. hammer_hook "Bounds" "Bounds.fold_left_ensures".
induction l; simpl; intros. contradiction.
destruct H1. subst a. apply fold_left_preserves; auto. apply IHl; auto.
Qed.

Definition only_callee_saves (u: RegSet.t) : Prop :=
forall r, RegSet.In r u -> is_callee_save r = true.

Lemma record_reg_only: forall u r, only_callee_saves u -> only_callee_saves (record_reg u r).
Proof. hammer_hook "Bounds" "Bounds.record_reg_only".
unfold only_callee_saves, record_reg; intros.
destruct (is_callee_save r) eqn:CS; auto.
destruct (mreg_eq r r0). congruence. apply H; eapply RegSet.add_3; eauto.
Qed.

Lemma record_regs_only: forall rl u, only_callee_saves u -> only_callee_saves (record_regs u rl).
Proof. hammer_hook "Bounds" "Bounds.record_regs_only".
intros. unfold record_regs. apply fold_left_preserves; auto using record_reg_only.
Qed.

Lemma record_regs_of_instr_only: forall u i, only_callee_saves u -> only_callee_saves (record_regs_of_instr u i).
Proof. hammer_hook "Bounds" "Bounds.record_regs_of_instr_only".
intros. destruct i; simpl; auto using record_reg_only, record_regs_only.
Qed.

Lemma record_regs_of_function_only:
only_callee_saves record_regs_of_function.
Proof. hammer_hook "Bounds" "Bounds.record_regs_of_function_only".
intros. unfold record_regs_of_function.
apply fold_left_preserves. apply record_regs_of_instr_only.
red; intros. eelim RegSet.empty_1; eauto.
Qed.

Program Definition function_bounds := {|
used_callee_save := RegSet.elements record_regs_of_function;
bound_local := max_over_slots_of_funct local_slot;
bound_outgoing := Z.max (max_over_instrs outgoing_space) (max_over_slots_of_funct outgoing_slot);
bound_stack_data := Z.max f.(fn_stacksize) 0
|}.
Next Obligation.
apply max_over_slots_of_funct_pos.
Qed.
Next Obligation.
apply Z.le_ge. eapply Z.le_trans. 2: apply Z.le_max_r.
apply Z.ge_le. apply max_over_slots_of_funct_pos.
Qed.
Next Obligation.
apply Z.le_ge. apply Z.le_max_r.
Qed.
Next Obligation.
generalize (RegSet.elements_3w record_regs_of_function).
generalize (RegSet.elements record_regs_of_function).
induction 1. constructor. constructor; auto.
red; intros; elim H. apply InA_alt. exists x; auto.
Qed.
Next Obligation.
apply record_regs_of_function_only. apply RegSet.elements_2.
apply InA_alt. exists r; auto.
Qed.



Lemma record_reg_incr: forall u r r', RegSet.In r' u -> RegSet.In r' (record_reg u r).
Proof. hammer_hook "Bounds" "Bounds.record_reg_incr".
unfold record_reg; intros. destruct (is_callee_save r); auto. apply RegSet.add_2; auto.
Qed.

Lemma record_reg_ok: forall u r, is_callee_save r = true -> RegSet.In r (record_reg u r).
Proof. hammer_hook "Bounds" "Bounds.record_reg_ok".
unfold record_reg; intros. rewrite H. apply RegSet.add_1; auto.
Qed.

Lemma record_regs_incr: forall r' rl u, RegSet.In r' u -> RegSet.In r' (record_regs u rl).
Proof. hammer_hook "Bounds" "Bounds.record_regs_incr".
intros. unfold record_regs. apply fold_left_preserves; auto using record_reg_incr.
Qed.

Lemma record_regs_ok: forall r rl u, In r rl -> is_callee_save r = true -> RegSet.In r (record_regs u rl).
Proof. hammer_hook "Bounds" "Bounds.record_regs_ok".
intros. unfold record_regs. eapply fold_left_ensures; eauto using record_reg_incr, record_reg_ok.
Qed.

Lemma record_regs_of_instr_incr: forall r' u i, RegSet.In r' u -> RegSet.In r' (record_regs_of_instr u i).
Proof. hammer_hook "Bounds" "Bounds.record_regs_of_instr_incr".
intros. destruct i; simpl; auto using record_reg_incr, record_regs_incr.
Qed.

Definition defined_by_instr (r': mreg) (i: instruction) :=
match i with
| Lgetstack sl ofs ty r => r' = r
| Lop op args res => r' = res
| Lload chunk addr args dst => r' = dst
| Lbuiltin ef args res => In r' (params_of_builtin_res res) \/ In r' (destroyed_by_builtin ef)
| _ => False
end.

Lemma record_regs_of_instr_ok: forall r' u i, defined_by_instr r' i -> is_callee_save r' = true -> RegSet.In r' (record_regs_of_instr u i).
Proof. hammer_hook "Bounds" "Bounds.record_regs_of_instr_ok".
intros. destruct i; simpl in *; try contradiction; subst; auto using record_reg_ok.
destruct H; auto using record_regs_incr, record_regs_ok.
Qed.

Lemma record_regs_of_function_ok:
forall r i, In i f.(fn_code) -> defined_by_instr r i -> is_callee_save r = true -> RegSet.In r record_regs_of_function.
Proof. hammer_hook "Bounds" "Bounds.record_regs_of_function_ok".
intros. unfold record_regs_of_function.
eapply fold_left_ensures; eauto using record_regs_of_instr_incr, record_regs_of_instr_ok.
Qed.

Lemma max_over_list_bound:
forall (A: Type) (valu: A -> Z) (l: list A) (x: A),
In x l -> valu x <= max_over_list valu l.
Proof. hammer_hook "Bounds" "Bounds.max_over_list_bound".
intros until x. unfold max_over_list.
assert (forall c z,
let f := fold_left (fun x y => Z.max x (valu y)) c z in
z <= f /\ (In x c -> valu x <= f)).
induction c; simpl; intros.
split. omega. tauto.
elim (IHc (Z.max z (valu a))); intros.
split. apply Z.le_trans with (Z.max z (valu a)). apply Z.le_max_l. auto.
intro H1; elim H1; intro.
subst a. apply Z.le_trans with (Z.max z (valu x)).
apply Z.le_max_r. auto. auto.
intro. elim (H l 0); intros. auto.
Qed.

Lemma max_over_instrs_bound:
forall (valu: instruction -> Z) i,
In i f.(fn_code) -> valu i <= max_over_instrs valu.
Proof. hammer_hook "Bounds" "Bounds.max_over_instrs_bound".
intros. unfold max_over_instrs. apply max_over_list_bound; auto.
Qed.

Lemma max_over_slots_of_funct_bound:
forall (valu: slot * Z * typ -> Z) i s,
In i f.(fn_code) -> In s (slots_of_instr i) ->
valu s <= max_over_slots_of_funct valu.
Proof. hammer_hook "Bounds" "Bounds.max_over_slots_of_funct_bound".
intros. unfold max_over_slots_of_funct.
apply Z.le_trans with (max_over_slots_of_instr valu i).
unfold max_over_slots_of_instr. apply max_over_list_bound. auto.
apply max_over_instrs_bound. auto.
Qed.

Lemma local_slot_bound:
forall i ofs ty,
In i f.(fn_code) -> In (Local, ofs, ty) (slots_of_instr i) ->
ofs + typesize ty <= bound_local function_bounds.
Proof. hammer_hook "Bounds" "Bounds.local_slot_bound".
intros.
unfold function_bounds, bound_local.
change (ofs + typesize ty) with (local_slot (Local, ofs, ty)).
eapply max_over_slots_of_funct_bound; eauto.
Qed.

Lemma outgoing_slot_bound:
forall i ofs ty,
In i f.(fn_code) -> In (Outgoing, ofs, ty) (slots_of_instr i) ->
ofs + typesize ty <= bound_outgoing function_bounds.
Proof. hammer_hook "Bounds" "Bounds.outgoing_slot_bound".
intros. change (ofs + typesize ty) with (outgoing_slot (Outgoing, ofs, ty)).
unfold function_bounds, bound_outgoing.
apply Zmax_bound_r. eapply max_over_slots_of_funct_bound; eauto.
Qed.

Lemma size_arguments_bound:
forall sig ros,
In (Lcall sig ros) f.(fn_code) ->
size_arguments sig <= bound_outgoing function_bounds.
Proof. hammer_hook "Bounds" "Bounds.size_arguments_bound".
intros. change (size_arguments sig) with (outgoing_space (Lcall sig ros)).
unfold function_bounds, bound_outgoing.
apply Zmax_bound_l. apply max_over_instrs_bound; auto.
Qed.



Lemma mreg_is_within_bounds:
forall i, In i f.(fn_code) ->
forall r, defined_by_instr r i ->
mreg_within_bounds function_bounds r.
Proof. hammer_hook "Bounds" "Bounds.mreg_is_within_bounds".
intros. unfold mreg_within_bounds. intros.
exploit record_regs_of_function_ok; eauto. intros.
apply RegSet.elements_1 in H2. rewrite InA_alt in H2. destruct H2 as (r' & A & B).
subst r'; auto.
Qed.

Lemma slot_is_within_bounds:
forall i, In i f.(fn_code) ->
forall sl ty ofs, In (sl, ofs, ty) (slots_of_instr i) ->
slot_within_bounds function_bounds sl ofs ty.
Proof. hammer_hook "Bounds" "Bounds.slot_is_within_bounds".
intros. unfold slot_within_bounds.
destruct sl.
eapply local_slot_bound; eauto.
auto.
eapply outgoing_slot_bound; eauto.
Qed.

Lemma slots_of_locs_charact:
forall sl ofs ty l, In (sl, ofs, ty) (slots_of_locs l) <-> In (S sl ofs ty) l.
Proof. hammer_hook "Bounds" "Bounds.slots_of_locs_charact".
induction l; simpl; intros.
tauto.
destruct a; simpl; intuition congruence.
Qed.



Lemma instr_is_within_bounds:
forall i,
In i f.(fn_code) ->
instr_within_bounds function_bounds i.
Proof. hammer_hook "Bounds" "Bounds.instr_is_within_bounds".
intros;
destruct i;
generalize (mreg_is_within_bounds _ H); generalize (slot_is_within_bounds _ H);
simpl; intros; auto.

eapply size_arguments_bound; eauto.

split; intros.
apply H1; auto.
apply H0. rewrite slots_of_locs_charact; auto.
Qed.

Lemma function_is_within_bounds:
function_within_bounds f function_bounds.
Proof. hammer_hook "Bounds" "Bounds.function_is_within_bounds".
intros; red; intros. apply instr_is_within_bounds; auto.
Qed.

End BOUNDS.



Fixpoint size_callee_save_area_rec (l: list mreg) (ofs: Z) : Z :=
match l with
| nil => ofs
| r :: l =>
let ty := mreg_type r in
let sz := AST.typesize ty in
size_callee_save_area_rec l (align ofs sz + sz)
end.

Definition size_callee_save_area (b: bounds) (ofs: Z) : Z :=
size_callee_save_area_rec (used_callee_save b) ofs.

Lemma size_callee_save_area_rec_incr:
forall l ofs, ofs <= size_callee_save_area_rec l ofs.
Proof. hammer_hook "Bounds" "Bounds.size_callee_save_area_rec_incr".
Local Opaque mreg_type.
induction l as [ | r l]; intros; simpl.
- omega.
- eapply Z.le_trans. 2: apply IHl.
generalize (AST.typesize_pos (mreg_type r)); intros.
apply Z.le_trans with (align ofs (AST.typesize (mreg_type r))).
apply align_le; auto.
omega.
Qed.

Lemma size_callee_save_area_incr:
forall b ofs, ofs <= size_callee_save_area b ofs.
Proof. hammer_hook "Bounds" "Bounds.size_callee_save_area_incr".
intros. apply size_callee_save_area_rec_incr.
Qed.



Record frame_env : Type := mk_frame_env {
fe_size: Z;
fe_ofs_link: Z;
fe_ofs_retaddr: Z;
fe_ofs_local: Z;
fe_ofs_callee_save: Z;
fe_stack_data: Z;
fe_used_callee_save: list mreg
}.
