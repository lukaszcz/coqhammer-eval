From Hammer Require Import Hammer.















Require Import Wellfounded.
From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import AST.
From compcert Require Import Linking.
From compcert Require Import Integers.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Events.
From compcert Require Import Smallstep.
From compcert Require Import Globalenvs.
From compcert Require Import Switch.
From compcert Require Import Registers.
From compcert Require Import Cminor.
From compcert Require Import Op.
From compcert Require Import CminorSel.
From compcert Require Import RTL.
From compcert Require Import RTLgen.
From compcert Require Import RTLgenspec.





Record map_wf (m: mapping) : Prop :=
mk_map_wf {
map_wf_inj:
(forall id1 id2 r,
m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
map_wf_disj:
(forall id r,
m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
}.

Lemma init_mapping_wf:
map_wf init_mapping.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.init_mapping_wf".
unfold init_mapping; split; simpl.
intros until r. rewrite PTree.gempty. congruence.
tauto.
Qed.

Lemma add_var_wf:
forall s1 s2 map name r map' i,
add_var map name s1 = OK (r,map') s2 i ->
map_wf map -> map_valid map s1 -> map_wf map'.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.add_var_wf".
intros. monadInv H.
apply mk_map_wf; simpl.
intros until r0. repeat rewrite PTree.gsspec.
destruct (peq id1 name); destruct (peq id2 name).
congruence.
intros. inv H. elimtype False.
apply valid_fresh_absurd with r0 s1.
apply H1. left; exists id2; auto.
eauto with rtlg.
intros. inv H2. elimtype False.
apply valid_fresh_absurd with r0 s1.
apply H1. left; exists id1; auto.
eauto with rtlg.
inv H0. eauto.
intros until r0. rewrite PTree.gsspec.
destruct (peq id name).
intros. inv H.
apply valid_fresh_absurd with r0 s1.
apply H1. right; auto.
eauto with rtlg.
inv H0; eauto.
Qed.

Lemma add_vars_wf:
forall names s1 s2 map map' rl i,
add_vars map names s1 = OK (rl,map') s2 i ->
map_wf map -> map_valid map s1 -> map_wf map'.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.add_vars_wf".
induction names; simpl; intros; monadInv H.
auto.
exploit add_vars_valid; eauto. intros [A B].
eapply add_var_wf; eauto.
Qed.

Lemma add_letvar_wf:
forall map r,
map_wf map -> ~reg_in_map map r -> map_wf (add_letvar map r).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.add_letvar_wf".
intros. inv H. unfold add_letvar; constructor; simpl.
auto.
intros. elim H1; intro. subst r0. elim H0. left; exists id; auto.
eauto.
Qed.



Record match_env
(map: mapping) (e: env) (le: letenv) (rs: regset) : Prop :=
mk_match_env {
me_vars:
(forall id v,
e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ Val.lessdef v rs#r);
me_letvars:
Val.lessdef_list le rs##(map.(map_letvars))
}.

Lemma match_env_find_var:
forall map e le rs id v r,
match_env map e le rs ->
e!id = Some v ->
map.(map_vars)!id = Some r ->
Val.lessdef v rs#r.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_find_var".
intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
replace r with r'. auto. congruence.
Qed.

Lemma match_env_find_letvar:
forall map e le rs idx v r,
match_env map e le rs ->
List.nth_error le idx = Some v ->
List.nth_error map.(map_letvars) idx = Some r ->
Val.lessdef v rs#r.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_find_letvar".
intros. exploit me_letvars; eauto.
clear H. revert le H0 H1. generalize (map_letvars map). clear map.
induction idx; simpl; intros.
inversion H; subst le; inversion H0. subst v1.
destruct l; inversion H1. subst r0.
inversion H2. subst v2. auto.
destruct l; destruct le; try discriminate.
eapply IHidx; eauto.
inversion H. auto.
Qed.

Lemma match_env_invariant:
forall map e le rs rs',
match_env map e le rs ->
(forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
match_env map e le rs'.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_invariant".
intros. inversion H. apply mk_match_env.
intros. exploit me_vars0; eauto. intros [r [A B]].
exists r; split. auto. rewrite H0; auto. left; exists id; auto.
replace (rs'##(map_letvars map)) with (rs ## (map_letvars map)). auto.
apply list_map_exten. intros. apply H0. right; auto.
Qed.



Lemma match_env_update_temp:
forall map e le rs r v,
match_env map e le rs ->
~(reg_in_map map r) ->
match_env map e le (rs#r <- v).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_update_temp".
intros. apply match_env_invariant with rs; auto.
intros. case (Reg.eq r r0); intro.
subst r0; contradiction.
apply Regmap.gso; auto.
Qed.
Hint Resolve match_env_update_temp: rtlg.



Lemma match_env_update_var:
forall map e le rs id r v tv,
Val.lessdef v tv ->
map_wf map ->
map.(map_vars)!id = Some r ->
match_env map e le rs ->
match_env map (PTree.set id v e) le (rs#r <- tv).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_update_var".
intros. inversion H0. inversion H2. apply mk_match_env.
intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
subst id'. inv H3. exists r; split. auto. rewrite PMap.gss. auto.
exploit me_vars0; eauto. intros [r' [A B]].
exists r'; split. auto. rewrite PMap.gso; auto.
red; intros. subst r'. elim n. eauto.
erewrite list_map_exten. eauto.
intros. symmetry. apply PMap.gso. red; intros. subst x. eauto.
Qed.



Lemma match_env_update_dest:
forall map e le rs dst r v tv,
Val.lessdef v tv ->
map_wf map ->
reg_map_ok map r dst ->
match_env map e le rs ->
match_env map (set_optvar dst v e) le (rs#r <- tv).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_update_dest".
intros. inv H1; simpl.
eapply match_env_update_temp; eauto.
eapply match_env_update_var; eauto.
Qed.
Hint Resolve match_env_update_dest: rtlg.



Lemma match_env_update_res:
forall map res v e le tres tv rs,
Val.lessdef v tv ->
map_wf map ->
tr_builtin_res map res tres ->
match_env map e le rs ->
match_env map (set_builtin_res res v e) le (regmap_setres tres tv rs).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_update_res".
intros. inv H1; simpl.
- eapply match_env_update_var; eauto.
- auto.
- eapply match_env_update_temp; eauto.
Qed.



Lemma match_env_bind_letvar:
forall map e le rs r v,
match_env map e le rs ->
Val.lessdef v rs#r ->
match_env (add_letvar map r) e (v :: le) rs.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_bind_letvar".
intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed.

Lemma match_env_unbind_letvar:
forall map e le rs r v,
match_env (add_letvar map r) e (v :: le) rs ->
match_env map e le rs.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_unbind_letvar".
unfold add_letvar; intros. inv H. simpl in *.
constructor. auto. inversion me_letvars0. auto.
Qed.



Lemma match_env_empty:
forall map,
map.(map_letvars) = nil ->
match_env map (PTree.empty val) nil (Regmap.init Vundef).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_env_empty".
intros. apply mk_match_env.
intros. rewrite PTree.gempty in H0. discriminate.
rewrite H. constructor.
Qed.



Lemma match_set_params_init_regs:
forall il rl s1 map2 s2 vl tvl i,
add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
Val.lessdef_list vl tvl ->
match_env map2 (set_params vl il) nil (init_regs tvl rl)
/\ (forall r, reg_fresh r s2 -> (init_regs tvl rl)#r = Vundef).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_set_params_init_regs".
induction il; intros.

inv H. split. apply match_env_empty. auto. intros.
simpl. apply Regmap.gi.

monadInv H. simpl.
exploit add_vars_valid; eauto. apply init_mapping_valid. intros [A B].
exploit add_var_valid; eauto. intros [A' B']. clear B'.
monadInv EQ1.
destruct H0 as [ | v1 tv1 vs tvs].

destruct (IHil _ _ _ _ nil nil _ EQ) as [ME UNDEF]. constructor. inv ME. split.
replace (init_regs nil x) with (Regmap.init Vundef) in me_vars0, me_letvars0.
constructor; simpl.
intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
subst a. inv H. exists x1; split. auto. constructor.
eauto.
eauto.
destruct x; reflexivity.
intros. apply Regmap.gi.

destruct (IHil _ _ _ _ _ _ _ EQ H0) as [ME UNDEF]. inv ME. split.
constructor; simpl.
intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
subst a. inv H. inv H1. exists x1; split. auto. rewrite Regmap.gss. constructor.
inv H1. eexists; eauto.
exploit me_vars0; eauto. intros [r' [C D]].
exists r'; split. auto. rewrite Regmap.gso. auto.
apply valid_fresh_different with s.
apply B. left; exists id; auto.
eauto with rtlg.
destruct (map_letvars x0). auto. simpl in me_letvars0. inversion me_letvars0.
intros. rewrite Regmap.gso. apply UNDEF.
apply reg_fresh_decr with s2; eauto with rtlg.
apply not_eq_sym. apply valid_fresh_different with s2; auto.
Qed.

Lemma match_set_locals:
forall map1 s1,
map_wf map1 ->
forall il rl map2 s2 e le rs i,
match_env map1 e le rs ->
(forall r, reg_fresh r s1 -> rs#r = Vundef) ->
add_vars map1 il s1 = OK (rl, map2) s2 i ->
match_env map2 (set_locals il e) le rs.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_set_locals".
induction il; simpl in *; intros.

inv H2. auto.

monadInv H2.
exploit IHil; eauto. intro.
monadInv EQ1.
constructor.
intros id v. simpl. repeat rewrite PTree.gsspec.
destruct (peq id a). subst a. intro.
exists x1. split. auto. inv H3. constructor.
eauto with rtlg.
intros. eapply me_vars; eauto.
simpl. eapply me_letvars; eauto.
Qed.

Lemma match_init_env_init_reg:
forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
Val.lessdef_list vparams tvparams ->
match_env map2 (set_locals vars (set_params vparams params))
nil (init_regs tvparams rparams).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_init_env_init_reg".
intros.
exploit match_set_params_init_regs; eauto. intros [A B].
eapply match_set_locals; eauto.
eapply add_vars_wf; eauto. apply init_mapping_wf.
apply init_mapping_valid.
Qed.



From compcert Require Import Errors.

Definition match_prog (p: CminorSel.program) (tp: RTL.program) :=
match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

Lemma transf_program_match:
forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transf_program_match".
intros. apply match_transform_partial_program; auto.
Qed.

Section CORRECTNESS.

Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.



Lemma symbols_preserved:
forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof
(Genv.find_symbol_transf_partial TRANSL).

Lemma function_ptr_translated:
forall (b: block) (f: CminorSel.fundef),
Genv.find_funct_ptr ge b = Some f ->
exists tf,
Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof
(Genv.find_funct_ptr_transf_partial TRANSL).

Lemma functions_translated:
forall (v: val) (f: CminorSel.fundef),
Genv.find_funct ge v = Some f ->
exists tf,
Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof
(Genv.find_funct_transf_partial TRANSL).

Lemma sig_transl_function:
forall (f: CminorSel.fundef) (tf: RTL.fundef),
transl_fundef f = OK tf ->
RTL.funsig tf = CminorSel.funsig f.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.sig_transl_function".
intros until tf. unfold transl_fundef, transf_partial_fundef.
case f; intro.
unfold transl_function.
destruct (reserve_labels (fn_body f0) (PTree.empty node, init_state)) as [ngoto s0].
case (transl_fun f0 ngoto s0); simpl; intros.
discriminate.
destruct p. simpl in H. inversion H. reflexivity.
intro. inversion H. reflexivity.
Qed.

Lemma senv_preserved:
Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof
(Genv.senv_transf_partial TRANSL).



Lemma tr_move_correct:
forall r1 ns r2 nd cs f sp rs m,
tr_move f.(fn_code) ns r1 nd r2 ->
exists rs',
star step tge (State cs f sp ns rs m) E0 (State cs f sp nd rs' m) /\
rs'#r2 = rs#r1 /\
(forall r, r <> r2 -> rs'#r = rs#r).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.tr_move_correct".
intros. inv H.
exists rs; split. constructor. auto.
exists (rs#r2 <- (rs#r1)); split.
apply star_one. eapply exec_Iop. eauto. auto.
split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.



Section CORRECTNESS_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.



Definition transl_expr_prop
(le: letenv) (a: expr) (v: val) : Prop :=
forall tm cs f map pr ns nd rd rs dst
(MWF: map_wf map)
(TE: tr_expr f.(fn_code) map pr a ns nd rd dst)
(ME: match_env map e le rs)
(EXT: Mem.extends m tm),
exists rs', exists tm',
star step tge (State cs f sp ns rs tm) E0 (State cs f sp nd rs' tm')
/\ match_env map (set_optvar dst v e) le rs'
/\ Val.lessdef v rs'#rd
/\ (forall r, In r pr -> rs'#r = rs#r)
/\ Mem.extends m tm'.

Definition transl_exprlist_prop
(le: letenv) (al: exprlist) (vl: list val) : Prop :=
forall tm cs f map pr ns nd rl rs
(MWF: map_wf map)
(TE: tr_exprlist f.(fn_code) map pr al ns nd rl)
(ME: match_env map e le rs)
(EXT: Mem.extends m tm),
exists rs', exists tm',
star step tge (State cs f sp ns rs tm) E0 (State cs f sp nd rs' tm')
/\ match_env map e le rs'
/\ Val.lessdef_list vl rs'##rl
/\ (forall r, In r pr -> rs'#r = rs#r)
/\ Mem.extends m tm'.

Definition transl_condexpr_prop
(le: letenv) (a: condexpr) (v: bool) : Prop :=
forall tm cs f map pr ns ntrue nfalse rs
(MWF: map_wf map)
(TE: tr_condition f.(fn_code) map pr a ns ntrue nfalse)
(ME: match_env map e le rs)
(EXT: Mem.extends m tm),
exists rs', exists tm',
plus step tge (State cs f sp ns rs tm) E0 (State cs f sp (if v then ntrue else nfalse) rs' tm')
/\ match_env map e le rs'
/\ (forall r, In r pr -> rs'#r = rs#r)
/\ Mem.extends m tm'.



Lemma transl_expr_Evar_correct:
forall (le : letenv) (id : positive) (v: val),
e ! id = Some v ->
transl_expr_prop le (Evar id) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Evar_correct".
intros; red; intros. inv TE.
exploit match_env_find_var; eauto. intro EQ.
exploit tr_move_correct; eauto. intros [rs' [A [B C]]].
exists rs'; exists tm; split. eauto.
destruct H2 as [[D E] | [D E]].

subst r dst. simpl.
assert (forall r, rs'#r = rs#r).
intros. destruct (Reg.eq r rd). subst r. auto. auto.
split. eapply match_env_invariant; eauto.
split. congruence.
split; auto.

split.
apply match_env_invariant with (rs#rd <- (rs#r)).
apply match_env_update_dest; auto.
intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto.
split. congruence.
split. intros. apply C. intuition congruence.
auto.
Qed.

Lemma transl_expr_Eop_correct:
forall (le : letenv) (op : operation) (args : exprlist)
(vargs : list val) (v : val),
eval_exprlist ge sp e m le args vargs ->
transl_exprlist_prop le args vargs ->
eval_operation ge sp op vargs m = Some v ->
transl_expr_prop le (Eop op args) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Eop_correct".
intros; red; intros. inv TE.

exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
edestruct eval_operation_lessdef as [v' []]; eauto.
exists (rs1#rd <- v'); exists tm1.

split. eapply star_right. eexact EX1.
eapply exec_Iop; eauto.
rewrite (@eval_operation_preserved CminorSel.fundef _ _ _ ge tge). eauto.
exact symbols_preserved. traceEq.

split. eauto with rtlg.

split. rewrite Regmap.gss. auto.

split. intros. rewrite Regmap.gso. auto. intuition congruence.

auto.
Qed.

Lemma transl_expr_Eload_correct:
forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
(args : exprlist) (vargs : list val) (vaddr v : val),
eval_exprlist ge sp e m le args vargs ->
transl_exprlist_prop le args vargs ->
Op.eval_addressing ge sp addr vargs = Some vaddr ->
Mem.loadv chunk m vaddr = Some v ->
transl_expr_prop le (Eload chunk addr args) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Eload_correct".
intros; red; intros. inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
edestruct Mem.loadv_extends as [v' []]; eauto.
exists (rs1#rd <- v'); exists tm1.

split. eapply star_right. eexact EX1. eapply exec_Iload. eauto.
instantiate (1 := vaddr'). rewrite <- H3.
apply eval_addressing_preserved. exact symbols_preserved.
auto. traceEq.

split. eauto with rtlg.

split. rewrite Regmap.gss. auto.

split. intros. rewrite Regmap.gso. auto. intuition congruence.

auto.
Qed.

Lemma transl_expr_Econdition_correct:
forall (le : letenv) (a: condexpr) (ifso ifnot : expr)
(va : bool) (v : val),
eval_condexpr ge sp e m le a va ->
transl_condexpr_prop le a va ->
eval_expr ge sp e m le (if va then ifso else ifnot) v ->
transl_expr_prop le (if va then ifso else ifnot) v ->
transl_expr_prop le (Econdition a ifso ifnot) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Econdition_correct".
intros; red; intros; inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 EXT1]]]]].
assert (tr_expr f.(fn_code) map pr (if va then ifso else ifnot) (if va then ntrue else nfalse) nd rd dst).
destruct va; auto.
exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]].
exists rs2; exists tm2.

split. eapply star_trans. apply plus_star. eexact EX1. eexact EX2. traceEq.

split. assumption.

split. assumption.

split. intros. transitivity (rs1#r); auto.

auto.
Qed.

Lemma transl_expr_Elet_correct:
forall (le : letenv) (a1 a2 : expr) (v1 v2 : val),
eval_expr ge sp e m le a1 v1 ->
transl_expr_prop le a1 v1 ->
eval_expr ge sp e m (v1 :: le) a2 v2 ->
transl_expr_prop (v1 :: le) a2 v2 ->
transl_expr_prop le (Elet a1 a2) v2.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Elet_correct".
intros; red; intros; inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
assert (map_wf (add_letvar map r)).
eapply add_letvar_wf; eauto.
exploit H2; eauto. eapply match_env_bind_letvar; eauto.
intros [rs2 [tm2 [EX2 [ME3 [RES2 [OTHER2 EXT2]]]]]].
exists rs2; exists tm2.

split. eapply star_trans. eexact EX1. eexact EX2. auto.

split. eapply match_env_unbind_letvar; eauto.

split. assumption.

split. intros. transitivity (rs1#r0); auto.

auto.
Qed.

Lemma transl_expr_Eletvar_correct:
forall (le : list val) (n : nat) (v : val),
nth_error le n = Some v ->
transl_expr_prop le (Eletvar n) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Eletvar_correct".
intros; red; intros; inv TE.
exploit tr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
exists rs1; exists tm.

split. eexact EX1.

split.
destruct H2 as [[A B] | [A B]].
subst r dst; simpl.
apply match_env_invariant with rs. auto.
intros. destruct (Reg.eq r rd). subst r. auto. auto.
apply match_env_invariant with (rs#rd <- (rs#r)).
apply match_env_update_dest; auto.
eapply match_env_find_letvar; eauto.
intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
congruence.

split. rewrite RES1. eapply match_env_find_letvar; eauto.

split. intros.
destruct H2 as [[A B] | [A B]].
destruct (Reg.eq r0 rd); subst; auto.
apply OTHER1. intuition congruence.

auto.
Qed.

Remark eval_builtin_args_trivial:
forall (ge: RTL.genv) (rs: regset) sp m rl,
eval_builtin_args ge (fun r => rs#r) sp m (List.map (@BA reg) rl) rs##rl.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.eval_builtin_args_trivial".
induction rl; simpl.
- constructor.
- constructor; auto. constructor.
Qed.

Lemma transl_expr_Ebuiltin_correct:
forall le ef al vl v,
eval_exprlist ge sp e m le al vl ->
transl_exprlist_prop le al vl ->
external_call ef ge vl m E0 v m ->
transl_expr_prop le (Ebuiltin ef al) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Ebuiltin_correct".
intros; red; intros. inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
exploit external_call_mem_extends; eauto.
intros [v' [tm2 [A [B [C D]]]]].
exists (rs1#rd <- v'); exists tm2.

split. eapply star_right. eexact EX1.
change (rs1#rd <- v') with (regmap_setres (BR rd) v' rs1).
eapply exec_Ibuiltin; eauto.
eapply eval_builtin_args_trivial.
eapply external_call_symbols_preserved; eauto. apply senv_preserved.
reflexivity.

split. eauto with rtlg.

split. rewrite Regmap.gss. auto.

split. intros. rewrite Regmap.gso. auto. intuition congruence.

auto.
Qed.

Lemma transl_expr_Eexternal_correct:
forall le id sg al b ef vl v,
Genv.find_symbol ge id = Some b ->
Genv.find_funct_ptr ge b = Some (External ef) ->
ef_sig ef = sg ->
eval_exprlist ge sp e m le al vl ->
transl_exprlist_prop le al vl ->
external_call ef ge vl m E0 v m ->
transl_expr_prop le (Eexternal id sg al) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_expr_Eexternal_correct".
intros; red; intros. inv TE.
exploit H3; eauto. intros [rs1 [tm1 [EX1 [ME1 [RR1 [RO1 EXT1]]]]]].
exploit external_call_mem_extends; eauto.
intros [v' [tm2 [A [B [C D]]]]].
exploit function_ptr_translated; eauto. simpl. intros [tf [P Q]]. inv Q.
exists (rs1#rd <- v'); exists tm2.

split. eapply star_trans. eexact EX1.
eapply star_left. eapply exec_Icall; eauto.
simpl. rewrite symbols_preserved. rewrite H. eauto. auto.
eapply star_left. eapply exec_function_external.
eapply external_call_symbols_preserved; eauto. apply senv_preserved.
apply star_one. apply exec_return.
reflexivity. reflexivity. reflexivity.

split. eauto with rtlg.

split. rewrite Regmap.gss. auto.

split. intros. rewrite Regmap.gso. auto. intuition congruence.

auto.
Qed.

Lemma transl_exprlist_Enil_correct:
forall (le : letenv),
transl_exprlist_prop le Enil nil.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_exprlist_Enil_correct".
intros; red; intros; inv TE.
exists rs; exists tm.
split. apply star_refl.
split. assumption.
split. constructor.
auto.
Qed.

Lemma transl_exprlist_Econs_correct:
forall (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
(vl : list val),
eval_expr ge sp e m le a1 v1 ->
transl_expr_prop le a1 v1 ->
eval_exprlist ge sp e m le al vl ->
transl_exprlist_prop le al vl ->
transl_exprlist_prop le (Econs a1 al) (v1 :: vl).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_exprlist_Econs_correct".
intros; red; intros; inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]].
exists rs2; exists tm2.

split. eapply star_trans. eexact EX1. eexact EX2. auto.

split. assumption.

split. simpl. constructor. rewrite OTHER2. auto.
simpl; tauto.
auto.

split. intros. transitivity (rs1#r).
apply OTHER2; auto. simpl; tauto.
apply OTHER1; auto.

auto.
Qed.

Lemma transl_condexpr_CEcond_correct:
forall le cond al vl vb,
eval_exprlist ge sp e m le al vl ->
transl_exprlist_prop le al vl ->
eval_condition cond vl m = Some vb ->
transl_condexpr_prop le (CEcond cond al) vb.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_condexpr_CEcond_correct".
intros; red; intros. inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
exists rs1; exists tm1.

split. eapply plus_right. eexact EX1. eapply exec_Icond. eauto.
eapply eval_condition_lessdef; eauto. auto. traceEq.

split. assumption.

split. assumption.

auto.
Qed.

Lemma transl_condexpr_CEcondition_correct:
forall le a b c va v,
eval_condexpr ge sp e m le a va ->
transl_condexpr_prop le a va ->
eval_condexpr ge sp e m le (if va then b else c) v ->
transl_condexpr_prop le (if va then b else c) v ->
transl_condexpr_prop le (CEcondition a b c) v.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_condexpr_CEcondition_correct".
intros; red; intros. inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [OTHER1 EXT1]]]]].
assert (tr_condition (fn_code f) map pr (if va then b else c) (if va then n2 else n3) ntrue nfalse).
destruct va; auto.
exploit H2; eauto. intros [rs2 [tm2 [EX2 [ME2 [OTHER2 EXT2]]]]].
exists rs2; exists tm2.

split. eapply plus_trans. eexact EX1. eexact EX2. traceEq.

split. assumption.

split. intros. rewrite OTHER2; auto.

auto.
Qed.

Lemma transl_condexpr_CElet_correct:
forall le a b v1 v2,
eval_expr ge sp e m le a v1 ->
transl_expr_prop le a v1 ->
eval_condexpr ge sp e m (v1 :: le) b v2 ->
transl_condexpr_prop (v1 :: le) b v2 ->
transl_condexpr_prop le (CElet a b) v2.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_condexpr_CElet_correct".
intros; red; intros. inv TE.
exploit H0; eauto. intros [rs1 [tm1 [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]].
assert (map_wf (add_letvar map r)).
eapply add_letvar_wf; eauto.
exploit H2; eauto. eapply match_env_bind_letvar; eauto.
intros [rs2 [tm2 [EX2 [ME3 [OTHER2 EXT2]]]]].
exists rs2; exists tm2.

split. eapply star_plus_trans. eexact EX1. eexact EX2. traceEq.

split. eapply match_env_unbind_letvar; eauto.

split. intros. rewrite OTHER2; auto.

auto.
Qed.

Theorem transl_expr_correct:
forall le a v,
eval_expr ge sp e m le a v ->
transl_expr_prop le a v.
Proof
(eval_expr_ind3 ge sp e m
transl_expr_prop
transl_exprlist_prop
transl_condexpr_prop
transl_expr_Evar_correct
transl_expr_Eop_correct
transl_expr_Eload_correct
transl_expr_Econdition_correct
transl_expr_Elet_correct
transl_expr_Eletvar_correct
transl_expr_Ebuiltin_correct
transl_expr_Eexternal_correct
transl_exprlist_Enil_correct
transl_exprlist_Econs_correct
transl_condexpr_CEcond_correct
transl_condexpr_CEcondition_correct
transl_condexpr_CElet_correct).

Theorem transl_exprlist_correct:
forall le a v,
eval_exprlist ge sp e m le a v ->
transl_exprlist_prop le a v.
Proof
(eval_exprlist_ind3 ge sp e m
transl_expr_prop
transl_exprlist_prop
transl_condexpr_prop
transl_expr_Evar_correct
transl_expr_Eop_correct
transl_expr_Eload_correct
transl_expr_Econdition_correct
transl_expr_Elet_correct
transl_expr_Eletvar_correct
transl_expr_Ebuiltin_correct
transl_expr_Eexternal_correct
transl_exprlist_Enil_correct
transl_exprlist_Econs_correct
transl_condexpr_CEcond_correct
transl_condexpr_CEcondition_correct
transl_condexpr_CElet_correct).

Theorem transl_condexpr_correct:
forall le a v,
eval_condexpr ge sp e m le a v ->
transl_condexpr_prop le a v.
Proof
(eval_condexpr_ind3 ge sp e m
transl_expr_prop
transl_exprlist_prop
transl_condexpr_prop
transl_expr_Evar_correct
transl_expr_Eop_correct
transl_expr_Eload_correct
transl_expr_Econdition_correct
transl_expr_Elet_correct
transl_expr_Eletvar_correct
transl_expr_Ebuiltin_correct
transl_expr_Eexternal_correct
transl_exprlist_Enil_correct
transl_exprlist_Econs_correct
transl_condexpr_CEcond_correct
transl_condexpr_CEcondition_correct
transl_condexpr_CElet_correct).



Definition transl_exitexpr_prop
(le: letenv) (a: exitexpr) (x: nat) : Prop :=
forall tm cs f map ns nexits rs
(MWF: map_wf map)
(TE: tr_exitexpr f.(fn_code) map a ns nexits)
(ME: match_env map e le rs)
(EXT: Mem.extends m tm),
exists nd, exists rs', exists tm',
star step tge (State cs f sp ns rs tm) E0 (State cs f sp nd rs' tm')
/\ nth_error nexits x = Some nd
/\ match_env map e le rs'
/\ Mem.extends m tm'.

Theorem transl_exitexpr_correct:
forall le a x,
eval_exitexpr ge sp e m le a x ->
transl_exitexpr_prop le a x.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_exitexpr_correct".
induction 1; red; intros; inv TE.
-
exists ns, rs, tm.
split. apply star_refl.
auto.
-
exploit H3; eauto. intros (nd & A & B).
exploit transl_expr_correct; eauto. intros (rs1 & tm1 & EXEC1 & ME1 & RES1 & PRES1 & EXT1).
exists nd, rs1, tm1.
split. eapply star_right. eexact EXEC1. eapply exec_Ijumptable; eauto. inv RES1; auto. traceEq.
auto.
-
exploit transl_condexpr_correct; eauto. intros (rs1 & tm1 & EXEC1 & ME1 & RES1 & EXT1).
exploit IHeval_exitexpr; eauto.
instantiate (2 := if va then n2 else n3). destruct va; eauto.
intros (nd & rs2 & tm2 & EXEC2 & EXIT2 & ME2 & EXT2).
exists nd, rs2, tm2.
split. eapply star_trans. apply plus_star. eexact EXEC1. eexact EXEC2. traceEq.
auto.
-
exploit transl_expr_correct; eauto. intros (rs1 & tm1 & EXEC1 & ME1 & RES1 & PRES1 & EXT1).
assert (map_wf (add_letvar map r)).
eapply add_letvar_wf; eauto.
exploit IHeval_exitexpr; eauto. eapply match_env_bind_letvar; eauto.
intros (nd & rs2 & tm2 & EXEC2 & EXIT2 & ME2 & EXT2).
exists nd, rs2, tm2.
split. eapply star_trans. eexact EXEC1. eexact EXEC2. traceEq.
split. auto.
split. eapply match_env_unbind_letvar; eauto.
auto.
Qed.



Lemma eval_exprlist_append:
forall le al1 vl1 al2 vl2,
eval_exprlist ge sp e m le (exprlist_of_expr_list al1) vl1 ->
eval_exprlist ge sp e m le (exprlist_of_expr_list al2) vl2 ->
eval_exprlist ge sp e m le (exprlist_of_expr_list (al1 ++ al2)) (vl1 ++ vl2).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.eval_exprlist_append".
induction al1; simpl; intros vl1 al2 vl2 E1 E2; inv E1.
- auto.
- simpl. constructor; eauto.
Qed.

Lemma invert_eval_builtin_arg:
forall a v,
eval_builtin_arg ge sp e m a v ->
exists vl,
eval_exprlist ge sp e m nil (exprlist_of_expr_list (params_of_builtin_arg a)) vl
/\ Events.eval_builtin_arg ge (fun v => v) sp m (fst (convert_builtin_arg a vl)) v
/\ (forall vl', convert_builtin_arg a (vl ++ vl') = (fst (convert_builtin_arg a vl), vl')).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.invert_eval_builtin_arg".
induction 1; simpl; try (econstructor; intuition eauto with evalexpr barg; fail).
- econstructor; split; eauto with evalexpr. split. constructor. auto.
- econstructor; split; eauto with evalexpr. split. constructor. auto.
- econstructor; split; eauto with evalexpr. split. repeat constructor. auto.
- destruct IHeval_builtin_arg1 as (vl1 & A1 & B1 & C1).
destruct IHeval_builtin_arg2 as (vl2 & A2 & B2 & C2).
destruct (convert_builtin_arg a1 vl1) as [a1' rl1] eqn:E1; simpl in *.
destruct (convert_builtin_arg a2 vl2) as [a2' rl2] eqn:E2; simpl in *.
exists (vl1 ++ vl2); split.
apply eval_exprlist_append; auto.
split. rewrite C1, E2. constructor; auto.
intros. rewrite app_ass, !C1, C2, E2. auto.
Qed.

Lemma invert_eval_builtin_args:
forall al vl,
list_forall2 (eval_builtin_arg ge sp e m) al vl ->
exists vl',
eval_exprlist ge sp e m nil (exprlist_of_expr_list (params_of_builtin_args al)) vl'
/\ Events.eval_builtin_args ge (fun v => v) sp m (convert_builtin_args al vl') vl.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.invert_eval_builtin_args".
induction 1; simpl.
- exists (@nil val); split; constructor.
- exploit invert_eval_builtin_arg; eauto. intros (vl1 & A & B & C).
destruct IHlist_forall2 as (vl2 & D & E).
exists (vl1 ++ vl2); split.
apply eval_exprlist_append; auto.
rewrite C; simpl. constructor; auto.
Qed.

Lemma transl_eval_builtin_arg:
forall rs a vl rl v,
Val.lessdef_list vl rs##rl ->
Events.eval_builtin_arg ge (fun v => v) sp m (fst (convert_builtin_arg a vl)) v ->
exists v',
Events.eval_builtin_arg ge (fun r => rs#r) sp m (fst (convert_builtin_arg a rl)) v'
/\ Val.lessdef v v'
/\ Val.lessdef_list (snd (convert_builtin_arg a vl)) rs##(snd (convert_builtin_arg a rl)).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_eval_builtin_arg".
induction a; simpl; intros until v; intros LD EV;
try (now (inv EV; econstructor; eauto with barg)).
- destruct rl; simpl in LD; inv LD; inv EV; simpl.
econstructor; eauto with barg.
exists (rs#p); intuition auto. constructor.
- destruct (convert_builtin_arg a1 vl) as [a1' vl1] eqn:CV1; simpl in *.
destruct (convert_builtin_arg a2 vl1) as [a2' vl2] eqn:CV2; simpl in *.
destruct (convert_builtin_arg a1 rl) as [a1'' rl1] eqn:CV3; simpl in *.
destruct (convert_builtin_arg a2 rl1) as [a2'' rl2] eqn:CV4; simpl in *.
inv EV.
exploit IHa1; eauto. rewrite CV1; simpl; eauto.
rewrite CV1, CV3; simpl. intros (v1' & A1 & B1 & C1).
exploit IHa2. eexact C1. rewrite CV2; simpl; eauto.
rewrite CV2, CV4; simpl. intros (v2' & A2 & B2 & C2).
exists (Val.longofwords v1' v2'); split. constructor; auto.
split; auto. apply Val.longofwords_lessdef; auto.
- destruct (convert_builtin_arg a1 vl) as [a1' vl1] eqn:CV1; simpl in *.
destruct (convert_builtin_arg a2 vl1) as [a2' vl2] eqn:CV2; simpl in *.
destruct (convert_builtin_arg a1 rl) as [a1'' rl1] eqn:CV3; simpl in *.
destruct (convert_builtin_arg a2 rl1) as [a2'' rl2] eqn:CV4; simpl in *.
inv EV.
exploit IHa1; eauto. rewrite CV1; simpl; eauto.
rewrite CV1, CV3; simpl. intros (v1' & A1 & B1 & C1).
exploit IHa2. eexact C1. rewrite CV2; simpl; eauto.
rewrite CV2, CV4; simpl. intros (v2' & A2 & B2 & C2).
econstructor; split. constructor; eauto.
split; auto. destruct Archi.ptr64; auto using Val.add_lessdef, Val.addl_lessdef.
Qed.

Lemma transl_eval_builtin_args:
forall rs al vl1 rl vl,
Val.lessdef_list vl1 rs##rl ->
Events.eval_builtin_args ge (fun v => v) sp m (convert_builtin_args al vl1) vl ->
exists vl',
Events.eval_builtin_args ge (fun r => rs#r) sp m (convert_builtin_args al rl) vl'
/\ Val.lessdef_list vl vl'.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_eval_builtin_args".
induction al; simpl; intros until vl; intros LD EV.
- inv EV. exists (@nil val); split; constructor.
- destruct (convert_builtin_arg a vl1) as [a1' vl2] eqn:CV1; simpl in *.
inv EV.
exploit transl_eval_builtin_arg. eauto. instantiate (2 := a). rewrite CV1; simpl; eauto.
rewrite CV1; simpl. intros (v1' & A1 & B1 & C1).
exploit IHal. eexact C1. eauto. intros (vl' & A2 & B2).
destruct (convert_builtin_arg a rl) as [a1'' rl2]; simpl in *.
exists (v1' :: vl'); split; constructor; auto.
Qed.

End CORRECTNESS_EXPR.



Local Open Scope nat_scope.

Fixpoint size_stmt (s: stmt) : nat :=
match s with
| Sskip => 0
| Sseq s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
| Sifthenelse c s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
| Sloop s1 => (size_stmt s1 + 1)
| Sblock s1 => (size_stmt s1 + 1)
| Sexit n => 0
| Slabel lbl s1 => (size_stmt s1 + 1)
| _ => 1
end.

Fixpoint size_cont (k: cont) : nat :=
match k with
| Kseq s k1 => (size_stmt s + size_cont k1 + 1)
| Kblock k1 => (size_cont k1 + 1)
| _ => 0%nat
end.

Definition measure_state (S: CminorSel.state) :=
match S with
| CminorSel.State _ s k _ _ _ => (size_stmt s + size_cont k, size_stmt s)
| _                           => (0, 0)
end.

Definition lt_state (S1 S2: CminorSel.state) :=
lex_ord lt lt (measure_state S1) (measure_state S2).

Lemma lt_state_intro:
forall f1 s1 k1 sp1 e1 m1 f2 s2 k2 sp2 e2 m2,
size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
\/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
/\ size_stmt s1 < size_stmt s2) ->
lt_state (CminorSel.State f1 s1 k1 sp1 e1 m1)
(CminorSel.State f2 s2 k2 sp2 e2 m2).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.lt_state_intro".
intros. unfold lt_state. simpl. destruct H as [A | [A B]].
left. auto.
rewrite A. right. auto.
Qed.

Ltac Lt_state :=
apply lt_state_intro; simpl; try omega.

Lemma lt_state_wf:
well_founded lt_state.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.lt_state_wf".
unfold lt_state. apply wf_inverse_image with (f := measure_state).
apply wf_lex_ord. apply lt_wf. apply lt_wf.
Qed.





Inductive tr_fun (tf: function) (map: mapping) (f: CminorSel.function)
(ngoto: labelmap) (nret: node) (rret: option reg) : Prop :=
| tr_fun_intro: forall nentry r,
rret = ret_reg f.(CminorSel.fn_sig) r ->
tr_stmt tf.(fn_code) map f.(fn_body) nentry nret nil ngoto nret rret ->
tf.(fn_stacksize) = f.(fn_stackspace) ->
tr_fun tf map f ngoto nret rret.

Inductive tr_cont: RTL.code -> mapping ->
CminorSel.cont -> node -> list node -> labelmap -> node -> option reg ->
list RTL.stackframe -> Prop :=
| tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
tr_stmt c map s nd n nexits ngoto nret rret ->
tr_cont c map k n nexits ngoto nret rret cs ->
tr_cont c map (Kseq s k) nd nexits ngoto nret rret cs
| tr_Kblock: forall c map k nd nexits ngoto nret rret cs,
tr_cont c map k nd nexits ngoto nret rret cs ->
tr_cont c map (Kblock k) nd (nd :: nexits) ngoto nret rret cs
| tr_Kstop: forall c map ngoto nret rret cs,
c!nret = Some(Ireturn rret) ->
match_stacks Kstop cs ->
tr_cont c map Kstop nret nil ngoto nret rret cs
| tr_Kcall: forall c map optid f sp e k ngoto nret rret cs,
c!nret = Some(Ireturn rret) ->
match_stacks (Kcall optid f sp e k) cs ->
tr_cont c map (Kcall optid f sp e k) nret nil ngoto nret rret cs

with match_stacks: CminorSel.cont -> list RTL.stackframe -> Prop :=
| match_stacks_stop:
match_stacks Kstop nil
| match_stacks_call: forall optid f sp e k r tf n rs cs map nexits ngoto nret rret,
map_wf map ->
tr_fun tf map f ngoto nret rret ->
match_env map e nil rs ->
reg_map_ok map r optid ->
tr_cont tf.(fn_code) map k n nexits ngoto nret rret cs ->
match_stacks (Kcall optid f sp e k) (Stackframe r tf sp n rs :: cs).

Inductive match_states: CminorSel.state -> RTL.state -> Prop :=
| match_state:
forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret
(MWF: map_wf map)
(TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)
(TF: tr_fun tf map f ngoto nret rret)
(TK: tr_cont tf.(fn_code) map k ncont nexits ngoto nret rret cs)
(ME: match_env map e nil rs)
(MEXT: Mem.extends m tm),
match_states (CminorSel.State f s k sp e m)
(RTL.State cs tf sp ns rs tm)
| match_callstate:
forall f args targs k m tm cs tf
(TF: transl_fundef f = OK tf)
(MS: match_stacks k cs)
(LD: Val.lessdef_list args targs)
(MEXT: Mem.extends m tm),
match_states (CminorSel.Callstate f args k m)
(RTL.Callstate cs tf targs tm)
| match_returnstate:
forall v tv k m tm cs
(MS: match_stacks k cs)
(LD: Val.lessdef v tv)
(MEXT: Mem.extends m tm),
match_states (CminorSel.Returnstate v k m)
(RTL.Returnstate cs tv tm).

Lemma match_stacks_call_cont:
forall c map k ncont nexits ngoto nret rret cs,
tr_cont c map k ncont nexits ngoto nret rret cs ->
match_stacks (call_cont k) cs /\ c!nret = Some(Ireturn rret).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.match_stacks_call_cont".
induction 1; simpl; auto.
Qed.

Lemma tr_cont_call_cont:
forall c map k ncont nexits ngoto nret rret cs,
tr_cont c map k ncont nexits ngoto nret rret cs ->
tr_cont c map (call_cont k) nret nil ngoto nret rret cs.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.tr_cont_call_cont".
induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma tr_find_label:
forall c map lbl n (ngoto: labelmap) nret rret s' k' cs,
ngoto!lbl = Some n ->
forall s k ns1 nd1 nexits1,
find_label lbl s k = Some (s', k') ->
tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
tr_cont c map k nd1 nexits1 ngoto nret rret cs ->
exists ns2, exists nd2, exists nexits2,
c!n = Some(Inop ns2)
/\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
/\ tr_cont c map k' nd2 nexits2 ngoto nret rret cs.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.tr_find_label".
induction s; intros until nexits1; simpl; try congruence.

caseEq (find_label lbl s1 (Kseq s2 k)); intros.
inv H1. inv H2. eapply IHs1; eauto. econstructor; eauto.
inv H2. eapply IHs2; eauto.

caseEq (find_label lbl s1 k); intros.
inv H1. inv H2. eapply IHs1; eauto.
inv H2. eapply IHs2; eauto.

intros. inversion H1; subst.
eapply IHs; eauto. econstructor; eauto. econstructor; eauto.

intros. inv H1.
eapply IHs; eauto. econstructor; eauto.

destruct (ident_eq lbl l); intros.
inv H0. inv H1.
assert (n0 = n). change positive with node in H4. congruence. subst n0.
exists ns1; exists nd1; exists nexits1; auto.
inv H1. eapply IHs; eauto.
Qed.

Theorem transl_step_correct:
forall S1 t S2, CminorSel.step ge S1 t S2 ->
forall R1, match_states S1 R1 ->
exists R2,
(plus RTL.step tge R1 t R2 \/ (star RTL.step tge R1 t R2 /\ lt_state S2 S1))
/\ match_states S2 R2.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_step_correct".
induction 1; intros R1 MSTATE; inv MSTATE.


inv TS. inv TK. econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto.


inv TS. inv TK. econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto. constructor.


inv TS.
assert ((fn_code tf)!ncont = Some(Ireturn rret)
/\ match_stacks k cs).
inv TK; simpl in H; try contradiction; auto.
destruct H1.
assert (fn_stacksize tf = fn_stackspace f).
inv TF. auto.
edestruct Mem.free_parallel_extends as [tm' []]; eauto.
econstructor; split.
left; apply plus_one. eapply exec_Ireturn. eauto.
rewrite H3. eauto.
constructor; auto.


inv TS.
exploit transl_expr_correct; eauto.
intros [rs' [tm' [A [B [C [D E]]]]]].
econstructor; split.
right; split. eauto. Lt_state.
econstructor; eauto. constructor.


inv TS.
exploit transl_exprlist_correct; eauto.
intros [rs' [tm' [A [B [C [D E]]]]]].
exploit transl_expr_correct; eauto.
intros [rs'' [tm'' [F [G [J [K L]]]]]].
assert (Val.lessdef_list vl rs''##rl).
replace (rs'' ## rl) with (rs' ## rl). auto.
apply list_map_exten. intros. apply K. auto.
edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
edestruct Mem.storev_extends as [tm''' []]; eauto.
econstructor; split.
left; eapply plus_right. eapply star_trans. eexact A. eexact F. reflexivity.
eapply exec_Istore with (a := vaddr'). eauto.
rewrite <- H4. apply eval_addressing_preserved. exact symbols_preserved.
eauto. traceEq.
econstructor; eauto. constructor.


inv TS; inv H.

exploit transl_expr_correct; eauto.
intros [rs' [tm' [A [B [C [D X]]]]]].
exploit transl_exprlist_correct; eauto.
intros [rs'' [tm'' [E [F [G [J Y]]]]]].
exploit functions_translated; eauto. intros [tf' [P Q]].
econstructor; split.
left; eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
eapply exec_Icall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
apply sig_transl_function; auto.
traceEq.
constructor; auto. econstructor; eauto.

exploit transl_exprlist_correct; eauto.
intros [rs'' [tm'' [E [F [G [J Y]]]]]].
exploit functions_translated; eauto. intros [tf' [P Q]].
econstructor; split.
left; eapply plus_right. eexact E.
eapply exec_Icall; eauto. simpl. rewrite symbols_preserved. rewrite H4.
rewrite Genv.find_funct_find_funct_ptr in P. eauto.
apply sig_transl_function; auto.
traceEq.
constructor; auto. econstructor; eauto.


inv TS; inv H.

exploit transl_expr_correct; eauto.
intros [rs' [tm' [A [B [C [D X]]]]]].
exploit transl_exprlist_correct; eauto.
intros [rs'' [tm'' [E [F [G [J Y]]]]]].
exploit functions_translated; eauto. intros [tf' [P Q]].
exploit match_stacks_call_cont; eauto. intros [U V].
assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
edestruct Mem.free_parallel_extends as [tm''' []]; eauto.
econstructor; split.
left; eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
eapply exec_Itailcall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
apply sig_transl_function; auto.
rewrite H; eauto.
traceEq.
constructor; auto.

exploit transl_exprlist_correct; eauto.
intros [rs'' [tm'' [E [F [G [J Y]]]]]].
exploit functions_translated; eauto. intros [tf' [P Q]].
exploit match_stacks_call_cont; eauto. intros [U V].
assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
edestruct Mem.free_parallel_extends as [tm''' []]; eauto.
econstructor; split.
left; eapply plus_right. eexact E.
eapply exec_Itailcall; eauto. simpl. rewrite symbols_preserved. rewrite H5.
rewrite Genv.find_funct_find_funct_ptr in P. eauto.
apply sig_transl_function; auto.
rewrite H; eauto.
traceEq.
constructor; auto.


inv TS.
exploit invert_eval_builtin_args; eauto. intros (vparams & P & Q).
exploit transl_exprlist_correct; eauto.
intros [rs' [tm' [E [F [G [J K]]]]]].
exploit transl_eval_builtin_args; eauto.
intros (vargs' & U & V).
exploit (@eval_builtin_args_lessdef _ ge (fun r => rs'#r) (fun r => rs'#r)); eauto.
intros (vargs'' & X & Y).
assert (Z: Val.lessdef_list vl vargs'') by (eapply Val.lessdef_list_trans; eauto).
edestruct external_call_mem_extends as [tv [tm'' [A [B [C D]]]]]; eauto.
econstructor; split.
left. eapply plus_right. eexact E.
eapply exec_Ibuiltin. eauto.
eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
eapply external_call_symbols_preserved. apply senv_preserved. eauto.
traceEq.
econstructor; eauto. constructor.
eapply match_env_update_res; eauto.


inv TS.
econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto. econstructor; eauto.


inv TS.
exploit transl_condexpr_correct; eauto. intros [rs' [tm' [A [B [C D]]]]].
econstructor; split.
left. eexact A.
destruct b; econstructor; eauto.


inversion TS; subst.
econstructor; split.
left. apply plus_one. eapply exec_Inop; eauto.
econstructor; eauto.
econstructor; eauto.
econstructor; eauto.


inv TS.
econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto. econstructor; eauto.


inv TS. inv TK.
econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto. econstructor; eauto.


inv TS. inv TK. simpl in H0. inv H0.
econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto. econstructor; eauto.


inv TS. inv TK. simpl in H0.
econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto. econstructor; eauto.


inv TS.
exploit transl_exitexpr_correct; eauto.
intros (nd & rs' & tm' & A & B & C & D).
econstructor; split.
right; split. eexact A. Lt_state.
econstructor; eauto. constructor; auto.


inv TS.
exploit match_stacks_call_cont; eauto. intros [U V].
inversion TF.
edestruct Mem.free_parallel_extends as [tm' []]; eauto.
econstructor; split.
left; apply plus_one. eapply exec_Ireturn; eauto.
rewrite H2; eauto.
constructor; auto.


inv TS.
exploit transl_expr_correct; eauto.
intros [rs' [tm' [A [B [C [D E]]]]]].
exploit match_stacks_call_cont; eauto. intros [U V].
inversion TF.
edestruct Mem.free_parallel_extends as [tm'' []]; eauto.
econstructor; split.
left; eapply plus_right. eexact A. eapply exec_Ireturn; eauto.
rewrite H4; eauto. traceEq.
simpl. constructor; auto.


inv TS.
econstructor; split.
right; split. apply star_refl. Lt_state.
econstructor; eauto.


inv TS. inversion TF; subst.
exploit tr_find_label; eauto. eapply tr_cont_call_cont; eauto.
intros [ns2 [nd2 [nexits2 [A [B C]]]]].
econstructor; split.
left; apply plus_one. eapply exec_Inop; eauto.
econstructor; eauto.


monadInv TF. exploit transl_function_charact; eauto. intro TRF.
inversion TRF. subst f0.
pose (e := set_locals (fn_vars f) (set_params vargs (CminorSel.fn_params f))).
pose (rs := init_regs targs rparams).
assert (ME: match_env map2 e nil rs).
unfold rs, e. eapply match_init_env_init_reg; eauto.
assert (MWF: map_wf map2).
assert (map_valid init_mapping s0) by apply init_mapping_valid.
exploit (add_vars_valid (CminorSel.fn_params f)); eauto. intros [A B].
eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.
edestruct Mem.alloc_extends as [tm' []]; eauto; try apply Z.le_refl.
econstructor; split.
left; apply plus_one. eapply exec_function_internal; simpl; eauto.
simpl. econstructor; eauto.
econstructor; eauto.
inversion MS; subst; econstructor; eauto.


monadInv TF.
edestruct external_call_mem_extends as [tvres [tm' [A [B [C D]]]]]; eauto.
econstructor; split.
left; apply plus_one. eapply exec_function_external; eauto.
eapply external_call_symbols_preserved; eauto. apply senv_preserved.
constructor; auto.


inv MS.
econstructor; split.
left; apply plus_one; constructor.
econstructor; eauto. constructor.
eapply match_env_update_dest; eauto.
Qed.

Lemma transl_initial_states:
forall S, CminorSel.initial_state prog S ->
exists R, RTL.initial_state tprog R /\ match_states S R.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_initial_states".
induction 1.
exploit function_ptr_translated; eauto. intros [tf [A B]].
econstructor; split.
econstructor. apply (Genv.init_mem_transf_partial TRANSL); eauto.
replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
symmetry; eapply match_program_main; eauto.
eexact A.
rewrite <- H2. apply sig_transl_function; auto.
constructor. auto. constructor.
constructor. apply Mem.extends_refl.
Qed.

Lemma transl_final_states:
forall S R r,
match_states S R -> CminorSel.final_state S r -> RTL.final_state R r.
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transl_final_states".
intros. inv H0. inv H. inv MS. inv LD. constructor.
Qed.

Theorem transf_program_correct:
forward_simulation (CminorSel.semantics prog) (RTL.semantics tprog).
Proof. hammer_hook "RTLgenproof" "RTLgenproof.transf_program_correct".
eapply forward_simulation_star_wf with (order := lt_state).
apply senv_preserved.
eexact transl_initial_states.
eexact transl_final_states.
apply lt_state_wf.
exact transl_step_correct.
Qed.

End CORRECTNESS.
