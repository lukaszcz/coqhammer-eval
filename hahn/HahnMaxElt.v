From Hammer Require Import Hammer.





From hahn Require Import HahnBase HahnList HahnSets HahnRelationsBasic.
From hahn Require Import HahnEquational HahnRewrite.
Require Import NPeano Omega Setoid.

Set Implicit Arguments.


Definition max_elt A (r: relation A) (a : A) :=
forall b (REL: r a b), False.

Definition wmax_elt A (r: relation A) (a : A) :=
forall b (REL: r a b), a = b.


Section BasicProperties.

Variable A : Type.
Variables r r' r'' : relation A.
Variable a : A.

Lemma set_subset_max_elt (S: r' ⊆ r) : max_elt r ⊆₁ max_elt r'.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.set_subset_max_elt". unfold max_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_subset_wmax_elt (S: r' ⊆ r) : wmax_elt r ⊆₁ wmax_elt r'.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.set_subset_wmax_elt". unfold wmax_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_max_elt (S: r ≡ r') : max_elt r ≡₁ max_elt r'.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.set_equiv_max_elt". unfold max_elt, same_relation, set_equiv, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_wmax_elt (S: r ≡ r') : wmax_elt r ≡₁ wmax_elt r'.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.set_equiv_wmax_elt". unfold wmax_elt, same_relation, set_equiv in *; intuition; eauto. Qed.

Lemma max_elt_weaken : max_elt r a -> wmax_elt r a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.max_elt_weaken".
red; ins; exfalso; eauto.
Qed.

Lemma max_elt_union : max_elt r a -> max_elt r' a -> max_elt (r +++ r') a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.max_elt_union".
unfold union; red; ins; desf; eauto.
Qed.

Lemma wmax_elt_union : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r +++ r') a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_union".
unfold union; red; ins; desf; eauto.
Qed.

Lemma max_elt_t : max_elt r a -> max_elt (r⁺) a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.max_elt_t".
red; ins; apply clos_trans_t1n in REL; induction REL; eauto.
Qed.

Lemma wmax_elt_rt : wmax_elt r a -> wmax_elt (r＊) a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_rt".
red; ins; apply clos_rt_rtn1 in REL; induction REL; desf; eauto.
Qed.

Lemma wmax_elt_t : wmax_elt r a -> wmax_elt (r⁺) a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_t".
by red; ins; eapply wmax_elt_rt, inclusion_t_rt.
Qed.

Lemma wmax_elt_eqv (f: A -> Prop) : wmax_elt (eqv_rel f) a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_eqv".
unfold eqv_rel; red; ins; desf.
Qed.

Lemma wmax_elt_restr_eq B (f: A -> B) :
wmax_elt r a -> wmax_elt (restr_eq_rel f r) a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_restr_eq".
unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma max_elt_restr_eq B (f: A -> B) :
max_elt r a -> max_elt (restr_eq_rel f r) a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.max_elt_restr_eq".
unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma wmax_elt_r :
wmax_elt r a -> wmax_elt (r^?) a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_r".
unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma max_elt_seq1 : max_elt r a -> max_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.max_elt_seq1".
unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma wmax_elt_seq2 : wmax_elt r a -> wmax_elt r' a -> wmax_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_seq2".
unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma wmax_elt_seq1 : max_elt r a -> wmax_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_seq1".
unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

Lemma max_elt_seq2 : wmax_elt r a -> max_elt r' a -> max_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.max_elt_seq2".
unfold seq; red; ins; desf; apply H in REL; desf; eauto.
Qed.

End BasicProperties.

Hint Immediate max_elt_weaken : hahn.
Hint Resolve wmax_elt_union max_elt_union : hahn.
Hint Resolve wmax_elt_t wmax_elt_r wmax_elt_rt max_elt_t : hahn.
Hint Resolve max_elt_restr_eq wmax_elt_restr_eq : hahn.
Hint Resolve max_elt_seq1 max_elt_seq2 wmax_elt_seq1 wmax_elt_seq2 : hahn.

Section MoreProperties.

Variable A : Type.
Implicit Type r : relation A.

Lemma seq_max r r' b
(MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
r ⨾ r' ≡ ∅₂.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_max".
unfold seq; split; red; ins; desf.
apply COD in H; desf; eauto.
Qed.

Lemma seq_max_t r r' b
(MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
r⨾ r' ⁺ ≡ ∅₂.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_max_t".
eauto using seq_max with hahn.
Qed.

Lemma seq_max_rt r r' b
(MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
r ⨾ r'＊ ≡ r.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_max_rt".
rewrite rtE; relsf; rewrite seq_max_t; relsf.
Qed.

Lemma seq_max_r r r' b
(MAX: max_elt r' b) (COD: forall x y, r x y -> y = b) :
r ⨾ r'^? ≡ r.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_max_r".
rewrite crE; relsf; rewrite seq_max; relsf.
Qed.

Lemma seq_eq_max r b (MAX: max_elt r b) :
⦗eq b⦘ ⨾ r ≡ ∅₂.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_max".
eapply seq_max; unfold eqv_rel; ins; desf; eauto.
Qed.

Lemma seq_eq_max_t r b (MAX: max_elt r b) :
⦗eq b⦘ ⨾ r⁺ ≡ ∅₂.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_max_t".
eauto using seq_eq_max with hahn.
Qed.

Lemma seq_eq_max_rt r b (MAX: max_elt r b) :
⦗eq b⦘ ⨾ r＊ ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_max_rt".
rewrite rtE; relsf; rewrite seq_eq_max_t; relsf.
Qed.

Lemma seq_eq_max_r r b (MAX: max_elt r b) :
⦗eq b⦘ ⨾ r^? ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_max_r".
rewrite crE; relsf; rewrite seq_eq_max; relsf.
Qed.

Lemma seq_singl_max r a b (MAX: max_elt r b) :
singl_rel a b ⨾ r ≡ ∅₂.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_max".
unfold singl_rel, seq; split; red; ins; desf; eauto.
Qed.

Lemma seq_singl_max_t r a b (MAX: max_elt r b) :
singl_rel a b ⨾ r⁺ ≡ ∅₂.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_max_t".
eauto using seq_singl_max with hahn.
Qed.

Lemma seq_singl_max_rt r a b (MAX: max_elt r b) :
singl_rel a b ⨾ r＊ ≡ singl_rel a b.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_max_rt".
rewrite rtE; relsf; rewrite seq_singl_max_t; relsf.
Qed.

Lemma seq_singl_max_r r a b (MAX: max_elt r b) :
singl_rel a b ⨾ r^? ≡ singl_rel a b.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_max_r".
rewrite crE; relsf; rewrite seq_singl_max; relsf.
Qed.

Lemma seq_eqv_max r :
⦗max_elt r⦘ ⨾ r ≡ (∅₂).
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eqv_max".
basic_solver.
Qed.

Lemma seq_eqv_max_t r :
⦗max_elt r⦘ ⨾ r⁺ ≡ (∅₂).
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eqv_max_t".
rewrite ct_begin; seq_rewrite seq_eqv_max; basic_solver.
Qed.

Lemma seq_eqv_max_rt r :
⦗max_elt r⦘ ⨾ r＊ ≡ ⦗max_elt r⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eqv_max_rt".
rewrite rtE; relsf; rewrite seq_eqv_max_t; relsf.
Qed.

Lemma seq_eqv_max_r r :
⦗max_elt r⦘ ⨾ r^? ≡ ⦗max_elt r⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eqv_max_r".
rewrite crE; relsf; rewrite seq_eqv_max; relsf.
Qed.

Lemma transp_seq_eqv_max r :
r⁻¹ ⨾ ⦗max_elt r⦘ ≡ (∅₂).
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.transp_seq_eqv_max".
basic_solver.
Qed.

Lemma transp_seq_eqv_max_t r :
(r⁻¹)⁺ ⨾ ⦗max_elt r⦘ ≡ (∅₂).
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.transp_seq_eqv_max_t".
rewrite ct_end, !seqA; seq_rewrite transp_seq_eqv_max; basic_solver.
Qed.

Lemma transp_seq_eqv_max_rt r :
(r⁻¹)＊ ⨾ ⦗max_elt r⦘  ≡ ⦗max_elt r⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.transp_seq_eqv_max_rt".
rewrite rtE; relsf; rewrite transp_seq_eqv_max_t; relsf.
Qed.

Lemma transp_seq_eqv_max_r r :
(r⁻¹)^? ⨾ ⦗max_elt r⦘ ≡ ⦗max_elt r⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.transp_seq_eqv_max_r".
rewrite crE; relsf; rewrite transp_seq_eqv_max; relsf.
Qed.

Lemma seq_wmax r r' b
(MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
r⨾ r' ⊆ r.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_wmax".
unfold seq; red; ins; desf; eauto.
specialize (COD _ _ H); desf; apply MAX in H0; desf.
Qed.

Lemma seq_wmax_t r r' b
(MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
r⨾ r' ⁺ ⊆ r.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_wmax_t".
eauto using seq_wmax with hahn.
Qed.

Lemma seq_wmax_rt r r' b
(MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
r⨾ r' ＊ ≡ r.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_wmax_rt".
rewrite rtE; split; relsf; rewrite seq_wmax_t; relsf.
Qed.

Lemma seq_wmax_r r r' b
(MAX: wmax_elt r' b) (COD: forall x y, r x y -> y = b) :
r⨾ r' ^? ≡ r.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_wmax_r".
rewrite crE; split; relsf; rewrite seq_wmax; relsf.
Qed.

Lemma seq_eq_wmax r b (MAX: wmax_elt r b) :
⦗eq b⦘⨾ r ⊆ ⦗eq b⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_wmax".
eapply seq_wmax; unfold eqv_rel; ins; desf.
Qed.

Lemma seq_eq_wmax_t r b (MAX: wmax_elt r b) :
⦗eq b⦘⨾ r ⁺ ⊆ ⦗eq b⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_wmax_t".
eauto using seq_eq_wmax with hahn.
Qed.

Lemma seq_eq_wmax_rt r b (MAX: wmax_elt r b) :
⦗eq b⦘⨾ r ＊ ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_wmax_rt".
rewrite rtE; split; relsf; rewrite seq_eq_wmax_t; relsf.
Qed.

Lemma seq_eq_wmax_r r b (MAX: wmax_elt r b) :
⦗eq b⦘⨾ r ^? ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_eq_wmax_r".
rewrite crE; split; relsf; rewrite seq_eq_wmax; relsf.
Qed.

Lemma seq_singl_wmax r a b (MAX: wmax_elt r b) :
singl_rel a b⨾ r ⊆ singl_rel a b.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_wmax".
unfold singl_rel, seq; red; ins; desf; eauto.
apply MAX in H0; desf.
Qed.

Lemma seq_singl_wmax_t r a b (MAX: wmax_elt r b) :
singl_rel a b⨾ r ⁺ ⊆ singl_rel a b.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_wmax_t".
eauto using seq_singl_wmax with hahn.
Qed.

Lemma seq_singl_wmax_rt r a b (MAX: wmax_elt r b) :
singl_rel a b⨾ r ＊ ≡ singl_rel a b.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_wmax_rt".
rewrite rtE; split; relsf; rewrite seq_singl_wmax_t; relsf.
Qed.

Lemma seq_singl_wmax_r r a b (MAX: wmax_elt r b) :
singl_rel a b⨾ r ^? ≡ singl_rel a b.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.seq_singl_wmax_r".
rewrite crE; split; relsf; rewrite seq_singl_wmax; relsf.
Qed.

End MoreProperties.

Hint Unfold max_elt wmax_elt : unfolderDb.

Require Import Morphisms.

Instance max_elt_Proper A : Proper (_ --> _) _ := set_subset_max_elt (A:=A).
Instance wmax_elt_Proper A : Proper (_ --> _) _ := set_subset_wmax_elt (A:=A).
Instance max_elt_Propere A : Proper (_ ==> _) _ := set_equiv_max_elt (A:=A).
Instance wmax_elt_Propere A : Proper (_ ==> _) _ := set_equiv_wmax_elt (A:=A).


Add Parametric Morphism A : (@max_elt A) with signature
inclusion --> eq ==> Basics.impl as max_elt_mori.
Proof. hammer_hook "HahnMaxElt" "HahnMaxElt.wmax_elt_Propere".
unfold inclusion, max_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@wmax_elt A) with signature
inclusion --> eq ==> Basics.impl as wmax_elt_mori.
Proof.
unfold inclusion, wmax_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@max_elt A) with signature
same_relation --> eq ==> iff as max_elt_more.
Proof.
unfold same_relation, inclusion, max_elt; firstorder.
Qed.

Add Parametric Morphism A : (@wmax_elt A) with signature
same_relation --> eq ==> iff as wmax_elt_more.
Proof.
unfold same_relation, inclusion, wmax_elt; firstorder.
Qed.
