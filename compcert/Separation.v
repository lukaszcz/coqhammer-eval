From Hammer Require Import Hammer.




















Require Import Setoid.
Require Import Program.Basics.
From compcert Require Import Coqlib.
From compcert Require Import Decidableplus.
From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Events.
From compcert Require Import Globalenvs.





Record massert : Type := {
m_pred : mem -> Prop;
m_footprint: block -> Z -> Prop;
m_invar: forall m m', m_pred m -> Mem.unchanged_on m_footprint m m' -> m_pred m';
m_valid: forall m b ofs, m_pred m -> m_footprint b ofs -> Mem.valid_block m b
}.

Notation "m |= p" := (m_pred p m) (at level 74, no associativity) : sep_scope.



Definition massert_imp (P Q: massert) : Prop :=
(forall m, m_pred P m -> m_pred Q m) /\ (forall b ofs, m_footprint Q b ofs -> m_footprint P b ofs).
Definition massert_eqv (P Q: massert) : Prop :=
massert_imp P Q /\ massert_imp Q P.

Remark massert_imp_refl: forall p, massert_imp p p.
Proof. hammer_hook "Separation" "Separation.massert_imp_refl".
unfold massert_imp; auto.
Qed.

Remark massert_imp_trans: forall p q r, massert_imp p q -> massert_imp q r -> massert_imp p r.
Proof. hammer_hook "Separation" "Separation.massert_imp_trans".
unfold massert_imp; intros; firstorder auto.
Qed.

Remark massert_eqv_refl: forall p, massert_eqv p p.
Proof. hammer_hook "Separation" "Separation.massert_eqv_refl".
unfold massert_eqv, massert_imp; intros. tauto.
Qed.

Remark massert_eqv_sym: forall p q, massert_eqv p q -> massert_eqv q p.
Proof. hammer_hook "Separation" "Separation.massert_eqv_sym".
unfold massert_eqv, massert_imp; intros. tauto.
Qed.

Remark massert_eqv_trans: forall p q r, massert_eqv p q -> massert_eqv q r -> massert_eqv p r.
Proof. hammer_hook "Separation" "Separation.massert_eqv_trans".
unfold massert_eqv, massert_imp; intros. firstorder auto.
Qed.


Add Relation massert massert_imp
reflexivity proved by massert_imp_refl
transitivity proved by massert_imp_trans
as massert_imp_prel.

Add Relation massert massert_eqv
reflexivity proved by massert_eqv_refl
symmetry proved by massert_eqv_sym
transitivity proved by massert_eqv_trans
as massert_eqv_prel.

Add Morphism m_pred
with signature massert_imp ==> eq ==> impl
as m_pred_morph_1.
Proof.
intros P Q [A B]. auto.
Qed.

Add Morphism m_pred
with signature massert_eqv ==> eq ==> iff
as m_pred_morph_2.
Proof.
intros P Q [[A B] [C D]]. split; auto.
Qed.

Hint Resolve massert_imp_refl massert_eqv_refl : core.



Definition disjoint_footprint (P Q: massert) : Prop :=
forall b ofs, m_footprint P b ofs -> m_footprint Q b ofs -> False.

Program Definition sepconj (P Q: massert) : massert := {|
m_pred := fun m => m_pred P m /\ m_pred Q m /\ disjoint_footprint P Q;
m_footprint := fun b ofs => m_footprint P b ofs \/ m_footprint Q b ofs
|}.
Next Obligation.
repeat split; auto.
apply (m_invar P) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
apply (m_invar Q) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
Qed.
Next Obligation.
destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
Qed.

Add Morphism sepconj
with signature massert_imp ==> massert_imp ==> massert_imp
as sepconj_morph_1.
Proof. hammer_hook "Separation" "Separation.sepconj".
intros P1 P2 [A B] Q1 Q2 [C D].
red; simpl; split; intros.
- intuition auto. red; intros. apply (H2 b ofs); auto.
- intuition auto.
Qed.

Add Morphism sepconj
with signature massert_eqv ==> massert_eqv ==> massert_eqv
as sepconj_morph_2.
Proof.
intros. destruct H, H0. split; apply sepconj_morph_1; auto.
Qed.

Infix "**" := sepconj (at level 60, right associativity) : sep_scope.

Local Open Scope sep_scope.

Lemma sep_imp:
forall P P' Q Q' m,
m |= P ** Q -> massert_imp P P' -> massert_imp Q Q' -> m |= P' ** Q'.
Proof. hammer_hook "Separation" "Separation.sep_imp".
intros. rewrite <- H0, <- H1; auto.
Qed.

Lemma sep_comm_1:
forall P Q,  massert_imp (P ** Q) (Q ** P).
Proof. hammer_hook "Separation" "Separation.sep_comm_1".
unfold massert_imp; simpl; split; intros.
- intuition auto. red; intros; eapply H2; eauto.
- intuition auto.
Qed.

Lemma sep_comm:
forall P Q, massert_eqv (P ** Q) (Q ** P).
Proof. hammer_hook "Separation" "Separation.sep_comm".
intros; split; apply sep_comm_1.
Qed.

Lemma sep_assoc_1:
forall P Q R, massert_imp ((P ** Q) ** R) (P ** (Q ** R)).
Proof. hammer_hook "Separation" "Separation.sep_assoc_1".
intros. unfold massert_imp, sepconj, disjoint_footprint; simpl; firstorder auto.
Qed.

Lemma sep_assoc_2:
forall P Q R, massert_imp (P ** (Q ** R)) ((P ** Q) ** R).
Proof. hammer_hook "Separation" "Separation.sep_assoc_2".
intros. unfold massert_imp, sepconj, disjoint_footprint; simpl; firstorder auto.
Qed.

Lemma sep_assoc:
forall P Q R, massert_eqv ((P ** Q) ** R) (P ** (Q ** R)).
Proof. hammer_hook "Separation" "Separation.sep_assoc".
intros; split. apply sep_assoc_1. apply sep_assoc_2.
Qed.

Lemma sep_swap:
forall P Q R, massert_eqv (P ** Q ** R) (Q ** P ** R).
Proof. hammer_hook "Separation" "Separation.sep_swap".
intros. rewrite <- sep_assoc. rewrite (sep_comm P). rewrite sep_assoc. reflexivity.
Qed.

Definition sep_swap12 := sep_swap.

Lemma sep_swap23:
forall P Q R S, massert_eqv (P ** Q ** R ** S) (P ** R ** Q ** S).
Proof. hammer_hook "Separation" "Separation.sep_swap23".
intros. rewrite (sep_swap Q). reflexivity.
Qed.

Lemma sep_swap34:
forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (P ** Q ** S ** R ** T).
Proof. hammer_hook "Separation" "Separation.sep_swap34".
intros. rewrite (sep_swap R). reflexivity.
Qed.

Lemma sep_swap45:
forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (P ** Q ** R ** T ** S ** U).
Proof. hammer_hook "Separation" "Separation.sep_swap45".
intros. rewrite (sep_swap S). reflexivity.
Qed.

Definition sep_swap2 := sep_swap.

Lemma sep_swap3:
forall P Q R S, massert_eqv (P ** Q ** R ** S) (R ** Q ** P ** S).
Proof. hammer_hook "Separation" "Separation.sep_swap3".
intros. rewrite sep_swap. rewrite (sep_swap P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_swap4:
forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (S ** Q ** R ** P ** T).
Proof. hammer_hook "Separation" "Separation.sep_swap4".
intros. rewrite sep_swap. rewrite (sep_swap3 P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_swap5:
forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (T ** Q ** R ** S ** P ** U).
Proof. hammer_hook "Separation" "Separation.sep_swap5".
intros. rewrite sep_swap. rewrite (sep_swap4 P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_drop:
forall P Q m, m |= P ** Q -> m |= Q.
Proof. hammer_hook "Separation" "Separation.sep_drop".
simpl; intros. tauto.
Qed.

Lemma sep_drop2:
forall P Q R m, m |= P ** Q ** R -> m |= P ** R.
Proof. hammer_hook "Separation" "Separation.sep_drop2".
intros. rewrite sep_swap in H. eapply sep_drop; eauto.
Qed.

Lemma sep_proj1:
forall Q P m, m |= P ** Q -> m |= P.
Proof. hammer_hook "Separation" "Separation.sep_proj1".
intros. destruct H; auto.
Qed.

Lemma sep_proj2:
forall P Q m, m |= P ** Q -> m |= Q.
Proof. hammer_hook "Separation" "Separation.sep_proj2". exact (sep_drop). Qed.

Definition sep_pick1 := sep_proj1.

Lemma sep_pick2:
forall P Q R m, m |= P ** Q ** R -> m |= Q.
Proof. hammer_hook "Separation" "Separation.sep_pick2".
intros. eapply sep_proj1; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick3:
forall P Q R S m, m |= P ** Q ** R ** S -> m |= R.
Proof. hammer_hook "Separation" "Separation.sep_pick3".
intros. eapply sep_pick2; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick4:
forall P Q R S T m, m |= P ** Q ** R ** S ** T -> m |= S.
Proof. hammer_hook "Separation" "Separation.sep_pick4".
intros. eapply sep_pick3; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick5:
forall P Q R S T U m, m |= P ** Q ** R ** S ** T ** U -> m |= T.
Proof. hammer_hook "Separation" "Separation.sep_pick5".
intros. eapply sep_pick4; eapply sep_proj2; eauto.
Qed.

Lemma sep_preserved:
forall m m' P Q,
m |= P ** Q ->
(m |= P -> m' |= P) ->
(m |= Q -> m' |= Q) ->
m' |= P ** Q.
Proof. hammer_hook "Separation" "Separation.sep_preserved".
simpl; intros. intuition auto.
Qed.





Program Definition pure (P: Prop) : massert := {|
m_pred := fun m => P;
m_footprint := fun b ofs => False
|}.
Next Obligation.
tauto.
Qed.

Lemma sep_pure:
forall P Q m, m |= pure P ** Q <-> P /\ m |= Q.
Proof. hammer_hook "Separation" "Separation.sep_pure".
simpl; intros. intuition auto. red; simpl; tauto.
Qed.



Program Definition range (b: block) (lo hi: Z) : massert := {|
m_pred := fun m =>
0 <= lo /\ hi <= Ptrofs.modulus
/\ (forall i k p, lo <= i < hi -> Mem.perm m b i k p);
m_footprint := fun b' ofs' => b' = b /\ lo <= ofs' < hi
|}.
Next Obligation.
split; auto. split; auto. intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
Qed.
Next Obligation.
apply Mem.perm_valid_block with ofs Cur Freeable; auto.
Qed.

Lemma alloc_rule:
forall m lo hi b m' P,
Mem.alloc m lo hi = (m', b) ->
0 <= lo -> hi <= Ptrofs.modulus ->
m |= P ->
m' |= range b lo hi ** P.
Proof. hammer_hook "Separation" "Separation.alloc_rule".
intros; simpl. split; [|split].
- split; auto. split; auto. intros.
apply Mem.perm_implies with Freeable; auto with mem.
eapply Mem.perm_alloc_2; eauto.
- apply (m_invar P) with m; auto. eapply Mem.alloc_unchanged_on; eauto.
- red; simpl. intros. destruct H3; subst b0.
eelim Mem.fresh_block_alloc; eauto. eapply (m_valid P); eauto.
Qed.

Lemma range_split:
forall b lo hi P mid m,
lo <= mid <= hi ->
m |= range b lo hi ** P ->
m |= range b lo mid ** range b mid hi ** P.
Proof. hammer_hook "Separation" "Separation.range_split".
intros. rewrite <- sep_assoc. eapply sep_imp; eauto.
split; simpl; intros.
- intuition auto.
+ omega.
+ apply H5; omega.
+ omega.
+ apply H5; omega.
+ red; simpl; intros; omega.
- intuition omega.
Qed.

Lemma range_drop_left:
forall b lo hi P mid m,
lo <= mid <= hi ->
m |= range b lo hi ** P ->
m |= range b mid hi ** P.
Proof. hammer_hook "Separation" "Separation.range_drop_left".
intros. apply sep_drop with (range b lo mid). apply range_split; auto.
Qed.

Lemma range_drop_right:
forall b lo hi P mid m,
lo <= mid <= hi ->
m |= range b lo hi ** P ->
m |= range b lo mid ** P.
Proof. hammer_hook "Separation" "Separation.range_drop_right".
intros. apply sep_drop2 with (range b mid hi). apply range_split; auto.
Qed.

Lemma range_split_2:
forall b lo hi P mid al m,
lo <= align mid al <= hi ->
al > 0 ->
m |= range b lo hi ** P ->
m |= range b lo mid ** range b (align mid al) hi ** P.
Proof. hammer_hook "Separation" "Separation.range_split_2".
intros. rewrite <- sep_assoc. eapply sep_imp; eauto.
assert (mid <= align mid al) by (apply align_le; auto).
split; simpl; intros.
- intuition auto.
+ omega.
+ apply H7; omega.
+ omega.
+ apply H7; omega.
+ red; simpl; intros; omega.
- intuition omega.
Qed.

Lemma range_preserved:
forall m m' b lo hi,
m |= range b lo hi ->
(forall i k p, lo <= i < hi -> Mem.perm m b i k p -> Mem.perm m' b i k p) ->
m' |= range b lo hi.
Proof. hammer_hook "Separation" "Separation.range_preserved".
intros. destruct H as (A & B & C). simpl; intuition auto.
Qed.



Program Definition contains (chunk: memory_chunk) (b: block) (ofs: Z) (spec: val -> Prop) : massert := {|
m_pred := fun m =>
0 <= ofs <= Ptrofs.max_unsigned
/\ Mem.valid_access m chunk b ofs Freeable
/\ exists v, Mem.load chunk m b ofs = Some v /\ spec v;
m_footprint := fun b' ofs' => b' = b /\ ofs <= ofs' < ofs + size_chunk chunk
|}.
Next Obligation.
rename H2 into v. split;[|split].
- auto.
- destruct H1; split; auto. red; intros; eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exists v. split; auto. eapply Mem.load_unchanged_on; eauto. simpl; auto.
Qed.
Next Obligation.
eauto with mem.
Qed.

Lemma contains_no_overflow:
forall spec m chunk b ofs,
m |= contains chunk b ofs spec ->
0 <= ofs <= Ptrofs.max_unsigned.
Proof. hammer_hook "Separation" "Separation.contains_no_overflow".
intros. simpl in H. tauto.
Qed.

Lemma load_rule:
forall spec m chunk b ofs,
m |= contains chunk b ofs spec ->
exists v, Mem.load chunk m b ofs = Some v /\ spec v.
Proof. hammer_hook "Separation" "Separation.load_rule".
intros. destruct H as (D & E & v & F & G).
exists v; auto.
Qed.

Lemma loadv_rule:
forall spec m chunk b ofs,
m |= contains chunk b ofs spec ->
exists v, Mem.loadv chunk m (Vptr b (Ptrofs.repr ofs)) = Some v /\ spec v.
Proof. hammer_hook "Separation" "Separation.loadv_rule".
intros. exploit load_rule; eauto. intros (v & A & B). exists v; split; auto.
simpl. rewrite Ptrofs.unsigned_repr; auto. eapply contains_no_overflow; eauto.
Qed.

Lemma store_rule:
forall chunk m b ofs v (spec1 spec: val -> Prop) P,
m |= contains chunk b ofs spec1 ** P ->
spec (Val.load_result chunk v) ->
exists m',
Mem.store chunk m b ofs v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof. hammer_hook "Separation" "Separation.store_rule".
intros. destruct H as (A & B & C). destruct A as (D & E & v0 & F & G).
assert (H: Mem.valid_access m chunk b ofs Writable) by eauto with mem.
destruct (Mem.valid_access_store _ _ _ _ v H) as [m' STORE].
exists m'; split; auto. simpl. intuition auto.
- eapply Mem.store_valid_access_1; eauto.
- exists (Val.load_result chunk v); split; auto. eapply Mem.load_store_same; eauto.
- apply (m_invar P) with m; auto.
eapply Mem.store_unchanged_on; eauto.
intros; red; intros. apply (C b i); simpl; auto.
Qed.

Lemma storev_rule:
forall chunk m b ofs v (spec1 spec: val -> Prop) P,
m |= contains chunk b ofs spec1 ** P ->
spec (Val.load_result chunk v) ->
exists m',
Mem.storev chunk m (Vptr b (Ptrofs.repr ofs)) v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof. hammer_hook "Separation" "Separation.storev_rule".
intros. exploit store_rule; eauto. intros (m' & A & B). exists m'; split; auto.
simpl. rewrite Ptrofs.unsigned_repr; auto. eapply contains_no_overflow. eapply sep_pick1; eauto.
Qed.

Lemma range_contains:
forall chunk b ofs P m,
m |= range b ofs (ofs + size_chunk chunk) ** P ->
(align_chunk chunk | ofs) ->
m |= contains chunk b ofs (fun v => True) ** P.
Proof. hammer_hook "Separation" "Separation.range_contains".
intros. destruct H as (A & B & C). destruct A as (D & E & F).
split; [|split].
- assert (Mem.valid_access m chunk b ofs Freeable).
{ split; auto. red; auto. }
split. generalize (size_chunk_pos chunk). unfold Ptrofs.max_unsigned. omega.
split. auto.
+ destruct (Mem.valid_access_load m chunk b ofs) as [v LOAD].
eauto with mem.
exists v; auto.
- auto.
- auto.
Qed.

Lemma contains_imp:
forall (spec1 spec2: val -> Prop) chunk b ofs,
(forall v, spec1 v -> spec2 v) ->
massert_imp (contains chunk b ofs spec1) (contains chunk b ofs spec2).
Proof. hammer_hook "Separation" "Separation.contains_imp".
intros; split; simpl; intros.
- intuition auto. destruct H4 as (v & A & B). exists v; auto.
- auto.
Qed.



Definition hasvalue (chunk: memory_chunk) (b: block) (ofs: Z) (v: val) : massert :=
contains chunk b ofs (fun v' => v' = v).

Lemma store_rule':
forall chunk m b ofs v (spec1: val -> Prop) P,
m |= contains chunk b ofs spec1 ** P ->
exists m',
Mem.store chunk m b ofs v = Some m' /\ m' |= hasvalue chunk b ofs (Val.load_result chunk v) ** P.
Proof. hammer_hook "Separation" "Separation.store_rule'".
intros. eapply store_rule; eauto.
Qed.

Lemma storev_rule':
forall chunk m b ofs v (spec1: val -> Prop) P,
m |= contains chunk b ofs spec1 ** P ->
exists m',
Mem.storev chunk m (Vptr b (Ptrofs.repr ofs)) v = Some m' /\ m' |= hasvalue chunk b ofs (Val.load_result chunk v) ** P.
Proof. hammer_hook "Separation" "Separation.storev_rule'".
intros. eapply storev_rule; eauto.
Qed.



Program Definition mconj (P Q: massert) : massert := {|
m_pred := fun m => m_pred P m /\ m_pred Q m;
m_footprint := fun b ofs => m_footprint P b ofs \/ m_footprint Q b ofs
|}.
Next Obligation.
split.
apply (m_invar P) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
apply (m_invar Q) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
Qed.
Next Obligation.
destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
Qed.

Lemma mconj_intro:
forall P Q R m,
m |= P ** R -> m |= Q ** R -> m |= mconj P Q ** R.
Proof. hammer_hook "Separation" "Separation.mconj_intro".
intros. destruct H as (A & B & C). destruct H0 as (D & E & F).
split; [|split].
- simpl; auto.
- auto.
- red; simpl; intros. destruct H; [eelim C | eelim F]; eauto.
Qed.

Lemma mconj_proj1:
forall P Q R m, m |= mconj P Q ** R -> m |= P ** R.
Proof. hammer_hook "Separation" "Separation.mconj_proj1".
intros. destruct H as (A & B & C); simpl in A.
simpl. intuition auto.
red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma mconj_proj2:
forall P Q R m, m |= mconj P Q ** R -> m |= Q ** R.
Proof. hammer_hook "Separation" "Separation.mconj_proj2".
intros. destruct H as (A & B & C); simpl in A.
simpl. intuition auto.
red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma frame_mconj:
forall P P' Q R m m',
m |= mconj P Q ** R ->
m' |= P' ** R ->
m' |= Q ->
m' |= mconj P' Q ** R.
Proof. hammer_hook "Separation" "Separation.frame_mconj".
intros. destruct H as (A & B & C); simpl in A.
destruct H0 as (D & E & F).
simpl. intuition auto.
red; simpl; intros. destruct H2. eapply F; eauto. eapply C; simpl; eauto.
Qed.

Add Morphism mconj
with signature massert_imp ==> massert_imp ==> massert_imp
as mconj_morph_1.
Proof.
intros P1 P2 [A B] Q1 Q2 [C D].
red; simpl; intuition auto.
Qed.

Add Morphism mconj
with signature massert_eqv ==> massert_eqv ==> massert_eqv
as mconj_morph_2.
Proof.
intros. destruct H, H0. split; apply mconj_morph_1; auto.
Qed.



Program Definition minjection (j: meminj) (m0: mem) : massert := {|
m_pred := fun m => Mem.inject j m0 m;
m_footprint := fun b ofs => exists b0 delta, j b0 = Some(b, delta) /\ Mem.perm m0 b0 (ofs - delta) Max Nonempty
|}.
Next Obligation.
set (img := fun b' ofs => exists b delta, j b = Some(b', delta) /\ Mem.perm m0 b (ofs - delta) Max Nonempty) in *.
assert (IMG: forall b1 b2 delta ofs k p,
j b1 = Some (b2, delta) -> Mem.perm m0 b1 ofs k p -> img b2 (ofs + delta)).
{ intros. red. exists b1, delta; split; auto.
replace (ofs + delta - delta) with ofs by omega.
eauto with mem. }
destruct H. constructor.
- destruct mi_inj. constructor; intros.
+ eapply Mem.perm_unchanged_on; eauto.
+ eauto.
+ rewrite (Mem.unchanged_on_contents _ _ _ H0); eauto.
- assumption.
- intros. eapply Mem.valid_block_unchanged_on; eauto.
- assumption.
- assumption.
- intros. destruct (Mem.perm_dec m0 b1 ofs Max Nonempty); auto.
eapply mi_perm_inv; eauto.
eapply Mem.perm_unchanged_on_2; eauto.
Qed.
Next Obligation.
eapply Mem.valid_block_inject_2; eauto.
Qed.

Lemma loadv_parallel_rule:
forall j m1 m2 chunk addr1 v1 addr2,
m2 |= minjection j m1 ->
Mem.loadv chunk m1 addr1 = Some v1 ->
Val.inject j addr1 addr2 ->
exists v2, Mem.loadv chunk m2 addr2 = Some v2 /\ Val.inject j v1 v2.
Proof. hammer_hook "Separation" "Separation.loadv_parallel_rule".
intros. simpl in H. eapply Mem.loadv_inject; eauto.
Qed.

Lemma storev_parallel_rule:
forall j m1 m2 P chunk addr1 v1 m1' addr2 v2,
m2 |= minjection j m1 ** P ->
Mem.storev chunk m1 addr1 v1 = Some m1' ->
Val.inject j addr1 addr2 ->
Val.inject j v1 v2 ->
exists m2', Mem.storev chunk m2 addr2 v2 = Some m2' /\ m2' |= minjection j m1' ** P.
Proof. hammer_hook "Separation" "Separation.storev_parallel_rule".
intros. destruct H as (A & B & C). simpl in A.
exploit Mem.storev_mapped_inject; eauto. intros (m2' & STORE & INJ).
inv H1; simpl in STORE; try discriminate.
assert (VALID: Mem.valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Writable)
by eauto with mem.
assert (EQ: Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta).
{ eapply Mem.address_inject'; eauto with mem. }
exists m2'; split; auto.
split; [|split].
- exact INJ.
- apply (m_invar P) with m2; auto.
eapply Mem.store_unchanged_on; eauto.
intros; red; intros. eelim C; eauto. simpl.
exists b1, delta; split; auto. destruct VALID as [V1 V2].
apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
apply V1. omega.
- red; simpl; intros. destruct H1 as (b0 & delta0 & U & V).
eelim C; eauto. simpl. exists b0, delta0; eauto with mem.
Qed.

Lemma alloc_parallel_rule:
forall m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
m2 |= minjection j m1 ** P ->
Mem.alloc m1 0 sz1 = (m1', b1) ->
Mem.alloc m2 0 sz2 = (m2', b2) ->
(8 | delta) ->
lo = delta ->
hi = delta + Z.max 0 sz1 ->
0 <= sz2 <= Ptrofs.max_unsigned ->
0 <= delta -> hi <= sz2 ->
exists j',
m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' m1' ** P
/\ inject_incr j j'
/\ j' b1 = Some(b2, delta)
/\ (forall b, b <> b1 -> j' b = j b).
Proof. hammer_hook "Separation" "Separation.alloc_parallel_rule".
intros until delta; intros SEP ALLOC1 ALLOC2 ALIGN LO HI RANGE1 RANGE2 RANGE3.
assert (RANGE4: lo <= hi) by xomega.
assert (FRESH1: ~Mem.valid_block m1 b1) by (eapply Mem.fresh_block_alloc; eauto).
assert (FRESH2: ~Mem.valid_block m2 b2) by (eapply Mem.fresh_block_alloc; eauto).
destruct SEP as (INJ & SP & DISJ). simpl in INJ.
exploit Mem.alloc_left_mapped_inject.
- eapply Mem.alloc_right_inject; eauto.
- eexact ALLOC1.
- instantiate (1 := b2). eauto with mem.
- instantiate (1 := delta). xomega.
- intros. assert (0 <= ofs < sz2) by (eapply Mem.perm_alloc_3; eauto). omega.
- intros. apply Mem.perm_implies with Freeable; auto with mem.
eapply Mem.perm_alloc_2; eauto. xomega.
- red; intros. apply Z.divide_trans with 8; auto.
exists (8 / align_chunk chunk). destruct chunk; reflexivity.
- intros. elim FRESH2. eapply Mem.valid_block_inject_2; eauto.
- intros (j' & INJ' & J1 & J2 & J3).
exists j'; split; auto.
rewrite <- ! sep_assoc.
split; [|split].
+ simpl. intuition auto; try (unfold Ptrofs.max_unsigned in *; omega).
* apply Mem.perm_implies with Freeable; auto with mem.
eapply Mem.perm_alloc_2; eauto. omega.
* apply Mem.perm_implies with Freeable; auto with mem.
eapply Mem.perm_alloc_2; eauto. omega.
* red; simpl; intros. destruct H1, H2. omega.
* red; simpl; intros.
assert (b = b2) by tauto. subst b.
assert (0 <= ofs < lo \/ hi <= ofs < sz2) by tauto. clear H1.
destruct H2 as (b0 & delta0 & D & E).
eapply Mem.perm_alloc_inv in E; eauto.
destruct (eq_block b0 b1).
subst b0. rewrite J2 in D. inversion D; clear D; subst delta0. xomega.
rewrite J3 in D by auto. elim FRESH2. eapply Mem.valid_block_inject_2; eauto.
+ apply (m_invar P) with m2; auto. eapply Mem.alloc_unchanged_on; eauto.
+ red; simpl; intros.
assert (VALID: Mem.valid_block m2 b) by (eapply (m_valid P); eauto).
destruct H as [A | (b0 & delta0 & A & B)].
* assert (b = b2) by tauto. subst b. contradiction.
* eelim DISJ; eauto. simpl.
eapply Mem.perm_alloc_inv in B; eauto.
destruct (eq_block b0 b1).
subst b0. rewrite J2 in A. inversion A; clear A; subst b delta0. contradiction.
rewrite J3 in A by auto. exists b0, delta0; auto.
Qed.

Lemma free_parallel_rule:
forall j m1 b1 sz1 m1' m2 b2 sz2 lo hi delta P,
m2 |= range b2 0 lo ** range b2 hi sz2 ** minjection j m1 ** P ->
Mem.free m1 b1 0 sz1 = Some m1' ->
j b1 = Some (b2, delta) ->
lo = delta -> hi = delta + Z.max 0 sz1 ->
exists m2',
Mem.free m2 b2 0 sz2 = Some m2'
/\ m2' |= minjection j m1' ** P.
Proof. hammer_hook "Separation" "Separation.free_parallel_rule".
intros. rewrite <- ! sep_assoc in H.
destruct H as (A & B & C).
destruct A as (D & E & F).
destruct D as (J & K & L).
destruct J as (_ & _ & J). destruct K as (_ & _ & K).
simpl in E.
assert (PERM: Mem.range_perm m2 b2 0 sz2 Cur Freeable).
{ red; intros.
destruct (zlt ofs lo). apply J; omega.
destruct (zle hi ofs). apply K; omega.
replace ofs with ((ofs - delta) + delta) by omega.
eapply Mem.perm_inject; eauto.
eapply Mem.free_range_perm; eauto. xomega.
}
destruct (Mem.range_perm_free _ _ _ _ PERM) as [m2' FREE].
exists m2'; split; auto. split; [|split].
- simpl. eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
intros. apply (F b2 (ofs + delta0)).
+ simpl.
destruct (zlt (ofs + delta0) lo). intuition auto.
destruct (zle hi (ofs + delta0)). intuition auto.
destruct (eq_block b0 b1).
* subst b0. rewrite H1 in H; inversion H; clear H; subst delta0.
eelim (Mem.perm_free_2 m1); eauto. xomega.
* exploit Mem.mi_no_overlap; eauto.
apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
eapply Mem.perm_free_3; eauto.
apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
eapply (Mem.free_range_perm m1); eauto.
instantiate (1 := ofs + delta0 - delta). xomega.
intros [X|X]. congruence. omega.
+ simpl. exists b0, delta0; split; auto.
replace (ofs + delta0 - delta0) with ofs by omega.
apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
eapply Mem.perm_free_3; eauto.
- apply (m_invar P) with m2; auto.
eapply Mem.free_unchanged_on; eauto.
intros; red; intros. eelim C; eauto. simpl.
destruct (zlt i lo). intuition auto.
destruct (zle hi i). intuition auto.
right; exists b1, delta; split; auto.
apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
eapply Mem.free_range_perm; eauto. xomega.
- red; simpl; intros. eelim C; eauto.
simpl. right. destruct H as (b0 & delta0 & U & V).
exists b0, delta0; split; auto.
eapply Mem.perm_free_3; eauto.
Qed.



Inductive globalenv_preserved {F V: Type} (ge: Genv.t F V) (j: meminj) (bound: block) : Prop :=
| globalenv_preserved_intro
(DOMAIN: forall b, Plt b bound -> j b = Some(b, 0))
(IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
(SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
(FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
(VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Program Definition globalenv_inject {F V: Type} (ge: Genv.t F V) (j: meminj) : massert := {|
m_pred := fun m => exists bound, Ple bound (Mem.nextblock m) /\ globalenv_preserved ge j bound;
m_footprint := fun b ofs => False
|}.
Next Obligation.
rename H into bound. exists bound; split; auto. eapply Ple_trans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
Qed.
Next Obligation.
tauto.
Qed.

Lemma globalenv_inject_preserves_globals:
forall (F V: Type) (ge: Genv.t F V) j m,
m |= globalenv_inject ge j ->
meminj_preserves_globals ge j.
Proof. hammer_hook "Separation" "Separation.globalenv_inject_preserves_globals".
intros. destruct H as (bound & A & B). destruct B.
split; [|split]; intros.
- eauto.
- eauto.
- symmetry; eauto.
Qed.

Lemma globalenv_inject_incr:
forall j m0 (F V: Type) (ge: Genv.t F V) m j' P,
inject_incr j j' ->
inject_separated j j' m0 m ->
m |= globalenv_inject ge j ** P ->
m |= globalenv_inject ge j' ** P.
Proof. hammer_hook "Separation" "Separation.globalenv_inject_incr".
intros. destruct H1 as (A & B & C). destruct A as (bound & D & E).
split; [|split]; auto.
exists bound; split; auto.
inv E; constructor; intros.
- eauto.
- destruct (j b1) as [[b0 delta0]|] eqn:JB1.
+ erewrite H in H1 by eauto. inv H1. eauto.
+ exploit H0; eauto. intros (X & Y). elim Y. apply Pos.lt_le_trans with bound; auto.
- eauto.
- eauto.
- eauto.
Qed.

Lemma external_call_parallel_rule:
forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres1 m1' m2 j P vargs2,
external_call ef ge vargs1 m1 t vres1 m1' ->
m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
Val.inject_list j vargs1 vargs2 ->
exists j' vres2 m2',
external_call ef ge vargs2 m2 t vres2 m2'
/\ Val.inject j' vres1 vres2
/\ m2' |= minjection j' m1' ** globalenv_inject ge j' ** P
/\ inject_incr j j'
/\ inject_separated j j' m1 m2.
Proof. hammer_hook "Separation" "Separation.external_call_parallel_rule".
intros until vargs2; intros CALL SEP ARGS.
destruct SEP as (A & B & C). simpl in A.
exploit external_call_mem_inject; eauto.
eapply globalenv_inject_preserves_globals. eapply sep_pick1; eauto.
intros (j' & vres2 & m2' & CALL' & RES & INJ' & UNCH1 & UNCH2 & INCR & ISEP).
assert (MAXPERMS: forall b ofs p,
Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
{ intros. eapply external_call_max_perm; eauto. }
exists j', vres2, m2'; intuition auto.
split; [|split].
- exact INJ'.
- apply m_invar with (m0 := m2).
+ apply globalenv_inject_incr with j m1; auto.
+ eapply Mem.unchanged_on_implies; eauto.
intros; red; intros; red; intros.
eelim C; eauto. simpl. exists b0, delta; auto.
- red; intros. destruct H as (b0 & delta & J' & E).
destruct (j b0) as [[b' delta'] | ] eqn:J.
+ erewrite INCR in J' by eauto. inv J'.
eelim C; eauto. simpl. exists b0, delta; split; auto. apply MAXPERMS; auto.
eapply Mem.valid_block_inject_1; eauto.
+ exploit ISEP; eauto. intros (X & Y). elim Y. eapply m_valid; eauto.
Qed.

Lemma alloc_parallel_rule_2:
forall (F V: Type) (ge: Genv.t F V) m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
Mem.alloc m1 0 sz1 = (m1', b1) ->
Mem.alloc m2 0 sz2 = (m2', b2) ->
(8 | delta) ->
lo = delta ->
hi = delta + Z.max 0 sz1 ->
0 <= sz2 <= Ptrofs.max_unsigned ->
0 <= delta -> hi <= sz2 ->
exists j',
m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' m1' ** globalenv_inject ge j' ** P
/\ inject_incr j j'
/\ j' b1 = Some(b2, delta).
Proof. hammer_hook "Separation" "Separation.alloc_parallel_rule_2".
intros.
set (j1 := fun b => if eq_block b b1 then Some(b2, delta) else j b).
assert (X: inject_incr j j1).
{ unfold j1; red; intros. destruct (eq_block b b1); auto.
subst b. eelim Mem.fresh_block_alloc. eexact H0.
eapply Mem.valid_block_inject_1. eauto. apply sep_proj1 in H. eexact H. }
assert (Y: inject_separated j j1 m1 m2).
{ unfold j1; red; intros. destruct (eq_block b0 b1).
- inversion H9; clear H9; subst b3 delta0 b0. split; eapply Mem.fresh_block_alloc; eauto.
- congruence. }
rewrite sep_swap in H. eapply globalenv_inject_incr with (j' := j1) in H; eauto. rewrite sep_swap in H.
clear X Y.
exploit alloc_parallel_rule; eauto.
intros (j' & A & B & C & D).
exists j'; split; auto.
rewrite sep_swap4 in A. rewrite sep_swap4. apply globalenv_inject_incr with j1 m1; auto.
- red; unfold j1; intros. destruct (eq_block b b1). congruence. rewrite D; auto.
- red; unfold j1; intros. destruct (eq_block b0 b1). congruence. rewrite D in H9 by auto. congruence.
Qed.
