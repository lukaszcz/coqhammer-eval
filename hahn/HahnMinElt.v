From Hammer Require Import Hammer.





From hahn Require Import HahnBase HahnList HahnSets HahnRelationsBasic.
From hahn Require Import HahnEquational HahnRewrite HahnMaxElt.
Require Import NPeano Omega Setoid.

Set Implicit Arguments.


Definition min_elt A (r: relation A) (a : A) :=
forall b (REL: r b a), False.

Definition wmin_elt A (r: relation A) (a : A) :=
forall b (REL: r b a), a = b.


Section BasicProperties.

Variable A : Type.
Variables r r' r'' : relation A.
Variable a : A.

Lemma min_transp : min_elt r⁻¹ ≡₁ max_elt r.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.min_transp".
split; unfold min_elt, max_elt, transp, set_subset; ins; desf.
Qed.

Lemma max_transp : max_elt r⁻¹ ≡₁ min_elt r.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.max_transp".
split; unfold min_elt, max_elt, transp, set_subset; ins; desf.
Qed.

Lemma set_subset_min_elt (S: r' ⊆ r) : min_elt r ⊆₁ min_elt r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.set_subset_min_elt". unfold min_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_subset_wmin_elt (S: r' ⊆ r) : wmin_elt r ⊆₁ wmin_elt r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.set_subset_wmin_elt". unfold wmin_elt, inclusion, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_min_elt (S: r ≡ r') : min_elt r ≡₁ min_elt r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.set_equiv_min_elt". unfold min_elt, same_relation, set_equiv, set_subset in *; intuition; eauto. Qed.

Lemma set_equiv_wmin_elt (S: r ≡ r') : wmin_elt r ≡₁ wmin_elt r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.set_equiv_wmin_elt". unfold wmin_elt, same_relation, set_equiv in *; intuition; eauto. Qed.

Lemma min_elt_weaken : min_elt r a -> wmin_elt r a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.min_elt_weaken".
red; ins; exfalso; eauto.
Qed.

Lemma min_elt_union : min_elt r a -> min_elt r' a -> min_elt (r +++ r') a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.min_elt_union".
unfold union; red; ins; desf; eauto.
Qed.

Lemma wmin_elt_union : wmin_elt r a -> wmin_elt r' a -> wmin_elt (r +++ r') a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_union".
unfold union; red; ins; desf; eauto.
Qed.

Lemma min_elt_t : min_elt r a -> min_elt (r⁺) a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.min_elt_t".
red; ins; apply clos_trans_t1n in REL; induction REL; eauto.
Qed.

Lemma wmin_elt_rt : wmin_elt r a -> wmin_elt (r＊) a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_rt".
red; ins; apply clos_rt_rt1n in REL; induction REL; intuition; desf; eauto.
Qed.

Lemma wmin_elt_t : wmin_elt r a -> wmin_elt (r⁺) a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_t".
by red; ins; eapply wmin_elt_rt, inclusion_t_rt.
Qed.

Lemma wmin_elt_eqv (f: A -> Prop) : wmin_elt (eqv_rel f) a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_eqv".
unfold eqv_rel; red; ins; desf.
Qed.

Lemma wmin_elt_restr_eq B (f: A -> B) :
wmin_elt r a -> wmin_elt (restr_eq_rel f r) a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_restr_eq".
unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma min_elt_restr_eq B (f: A -> B) :
min_elt r a -> min_elt (restr_eq_rel f r) a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.min_elt_restr_eq".
unfold restr_eq_rel in *; red; ins; desf; eauto.
Qed.

Lemma wmin_elt_r :
wmin_elt r a -> wmin_elt (r^?) a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_r".
unfold clos_refl; red; ins; desf; eauto.
Qed.

Lemma min_elt_seq1 : min_elt r' a -> min_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.min_elt_seq1".
unfold seq; red; ins; desf; apply H in REL0; desf; eauto.
Qed.

Lemma wmin_elt_seq2 : wmin_elt r a -> wmin_elt r' a -> wmin_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_seq2".
unfold seq; red; ins; desf; apply H0 in REL0; desf; eauto.
Qed.

Lemma wmin_elt_seq1 : min_elt r' a -> wmin_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_seq1".
unfold seq; red; ins; desf; apply H in REL0; desf; eauto.
Qed.

Lemma min_elt_seq2 : min_elt r a -> wmin_elt r' a -> min_elt (r ⨾ r') a.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.min_elt_seq2".
unfold seq; red; ins; desf; apply H0 in REL0; desf; eauto.
Qed.

End BasicProperties.

Hint Immediate min_elt_weaken : hahn.
Hint Resolve wmin_elt_union min_elt_union : hahn.
Hint Resolve wmin_elt_t wmin_elt_r wmin_elt_rt min_elt_t : hahn.
Hint Resolve min_elt_restr_eq wmin_elt_restr_eq : hahn.
Hint Resolve min_elt_seq1 min_elt_seq2 wmin_elt_seq1 wmin_elt_seq2 : hahn.

Section MoreProperties.

Variable A : Type.
Implicit Type r : relation A.

Lemma seq_min r r' b
(MAX: min_elt r b) (DOM: forall x y, r' x y -> x = b) :
r ⨾ r' ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min".
unfold seq; split; red; ins; desf.
apply DOM in H0; desf; eauto.
Qed.

Lemma seq_min_t r r' b
(MAX: min_elt r b) (DOM: forall x y, r' x y -> x = b) :
r ⁺ ⨾ r'  ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_t".
eauto using seq_min with hahn.
Qed.

Lemma seq_min_rt r r' b
(MAX: min_elt r b) (COD: forall x y, r' x y -> x = b) :
r ＊ ⨾ r' ≡ r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_rt".
rewrite rtE; relsf; rewrite seq_min_t; relsf.
Qed.

Lemma seq_min_r r r' b
(MAX: min_elt r b) (COD: forall x y, r' x y -> x = b) :
r ^? ⨾ r' ≡ r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_r".
rewrite crE; relsf; rewrite seq_min; relsf.
Qed.

Lemma seq_min_eq r b (MAX: min_elt r b) :
r ⨾⦗eq b⦘ ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_eq".
eapply seq_min; unfold eqv_rel; ins; desf; eauto.
Qed.

Lemma seq_min_t_eq r b (MAX: min_elt r b) :
r⁺ ⨾⦗eq b⦘ ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_t_eq".
eauto using seq_min_eq with hahn.
Qed.

Lemma seq_min_rt_eq r b (MAX: min_elt r b) :
r＊ ⨾⦗eq b⦘ ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_rt_eq".
rewrite rtE; relsf; rewrite seq_min_t_eq; relsf.
Qed.

Lemma seq_min_r_eq r b (MAX: min_elt r b) :
r^? ⨾⦗eq b⦘ ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_r_eq".
rewrite crE; relsf; rewrite seq_min_eq; relsf.
Qed.

Lemma seq_min_singl r a b (MAX: min_elt r a) :
r ⨾ singl_rel a b ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_singl".
unfold singl_rel, seq; split; red; ins; desf; eauto.
Qed.

Lemma seq_min_t_singl r a b (MAX: min_elt r a) :
r⁺ ⨾ singl_rel a b ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_t_singl".
eauto using seq_min_singl with hahn.
Qed.

Lemma seq_min_rt_singl r a b (MAX: min_elt r a) :
r＊ ⨾ singl_rel a b ≡ singl_rel a b.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_rt_singl".
rewrite rtE; relsf; rewrite seq_min_t_singl; relsf.
Qed.

Lemma seq_min_r_singl r a b (MAX: min_elt r a) :
r^? ⨾ singl_rel a b ≡ singl_rel a b.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_min_r_singl".
rewrite crE; relsf; rewrite seq_min_singl; relsf.
Qed.

Lemma seq_eqv_min r :
r ⨾ ⦗min_elt r⦘ ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_eqv_min".
basic_solver.
Qed.

Lemma seq_t_eqv_min r :
r⁺ ⨾ ⦗min_elt r⦘ ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_t_eqv_min".
rewrite ct_end, seqA; seq_rewrite seq_eqv_min; basic_solver.
Qed.

Lemma seq_rt_eqv_min r :
r＊ ⨾ ⦗min_elt r⦘ ≡ ⦗min_elt r⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_rt_eqv_min".
rewrite rtE; relsf; rewrite seq_t_eqv_min; relsf.
Qed.

Lemma seq_r_eqv_min r :
r^? ⨾ ⦗min_elt r⦘ ≡ ⦗min_elt r⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_r_eqv_min".
rewrite crE; relsf; rewrite seq_eqv_min; relsf.
Qed.

Lemma seq_eqv_min_transp r :
⦗min_elt r⦘ ⨾ r⁻¹  ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_eqv_min_transp".
basic_solver.
Qed.

Lemma seq_eqv_min_transp_t r :
⦗min_elt r⦘ ⨾ (r⁻¹)⁺ ≡ ∅₂.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_eqv_min_transp_t".
rewrite ct_begin; seq_rewrite seq_eqv_min_transp; basic_solver.
Qed.

Lemma seq_eqv_min_transp_rt r :
⦗min_elt r⦘ ⨾ (r⁻¹)＊  ≡ ⦗min_elt r⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_eqv_min_transp_rt".
rewrite rtE; relsf; rewrite seq_eqv_min_transp_t; relsf.
Qed.

Lemma seq_eqv_min_transp_r r :
⦗min_elt r⦘ ⨾ (r⁻¹)^?  ≡ ⦗min_elt r⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_eqv_min_transp_r".
rewrite crE; relsf; rewrite seq_eqv_min_transp; relsf.
Qed.

Lemma seq_wmin r r' b
(MAX: wmin_elt r b) (D: forall x y, r' x y -> x = b) :
r⨾ r' ⊆ r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin".
unfold seq; red; ins; desf; eauto.
specialize (D _ _ H0); desf; apply MAX in H; desf.
Qed.

Lemma seq_wmin_t r r' b
(MAX: wmin_elt r b) (D: forall x y, r' x y -> x = b) :
r ⁺⨾ r' ⊆ r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_t".
eauto using seq_wmin with hahn.
Qed.

Lemma seq_wmin_rt r r' b
(MAX: wmin_elt r b) (COD: forall x y, r' x y -> x = b) :
r ＊⨾ r' ≡ r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_rt".
rewrite rtE; split; relsf; rewrite seq_wmin_t; relsf.
Qed.

Lemma seq_wmin_r r r' b
(MAX: wmin_elt r b) (COD: forall x y, r' x y -> x = b) :
r ^?⨾ r' ≡ r'.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_r".
rewrite crE; split; relsf; rewrite seq_wmin; relsf.
Qed.

Lemma seq_wmin_eq r b (MAX: wmin_elt r b) :
r ⨾ ⦗eq b⦘ ⊆ ⦗eq b⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_eq".
eapply seq_wmin; unfold eqv_rel; ins; desf.
Qed.

Lemma seq_wmin_t_eq r b (MAX: wmin_elt r b) :
r ⁺ ⨾ ⦗eq b⦘ ⊆ ⦗eq b⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_t_eq".
eauto using seq_wmin_eq with hahn.
Qed.

Lemma seq_wmin_rt_eq r b (MAX: wmin_elt r b) :
r ＊ ⨾ ⦗eq b⦘ ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_rt_eq".
rewrite rtE; split; relsf; rewrite seq_wmin_t_eq; relsf.
Qed.

Lemma seq_wmin_r_eq r b (MAX: wmin_elt r b) :
r ^? ⨾ ⦗eq b⦘ ≡ ⦗eq b⦘.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_r_eq".
rewrite crE; split; relsf; rewrite seq_wmin_eq; relsf.
Qed.

Lemma seq_wmin_singl r a b (MAX: wmin_elt r a) :
r ⨾ singl_rel a b ⊆ singl_rel a b.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_singl".
unfold singl_rel, seq; red; ins; desf; eauto.
apply MAX in H; desf.
Qed.

Lemma seq_wmin_t_singl r a b (MAX: wmin_elt r a) :
r ⁺ ⨾ singl_rel a b ⊆ singl_rel a b.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_t_singl".
eauto using seq_wmin_singl with hahn.
Qed.

Lemma seq_wmin_rt_singl r a b (MAX: wmin_elt r a) :
r ＊ ⨾ singl_rel a b ≡ singl_rel a b.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_rt_singl".
rewrite rtE; split; relsf; rewrite seq_wmin_t_singl; relsf.
Qed.

Lemma seq_wmin_r_singl r a b (MAX: wmin_elt r a) :
r ^? ⨾ singl_rel a b ≡ singl_rel a b.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.seq_wmin_r_singl".
rewrite crE; split; relsf; rewrite seq_wmin_singl; relsf.
Qed.

End MoreProperties.

Hint Unfold min_elt wmin_elt : unfolderDb.

Require Import Morphisms.

Instance min_elt_Proper A : Proper (inclusion --> set_subset) _ := set_subset_min_elt (A:=A).
Instance wmin_elt_Proper A : Proper (inclusion --> set_subset) _ := set_subset_wmin_elt (A:=A).
Instance min_elt_Propere A : Proper (same_relation ==> set_equiv) _ := set_equiv_min_elt (A:=A).
Instance wmin_elt_Propere A : Proper (same_relation ==> set_equiv) _ := set_equiv_wmin_elt (A:=A).

Add Parametric Morphism A : (@min_elt A) with signature
inclusion --> eq ==> Basics.impl as min_elt_mori.
Proof. hammer_hook "HahnMinElt" "HahnMinElt.wmin_elt_Propere".
unfold inclusion, min_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@wmin_elt A) with signature
inclusion --> eq ==> Basics.impl as wmin_elt_mori.
Proof.
unfold inclusion, wmin_elt, Basics.impl; eauto.
Qed.

Add Parametric Morphism A : (@min_elt A) with signature
same_relation --> eq ==> iff as min_elt_more.
Proof.
unfold same_relation, inclusion, min_elt; firstorder.
Qed.

Add Parametric Morphism A : (@wmin_elt A) with signature
same_relation --> eq ==> iff as wmin_elt_more.
Proof.
unfold same_relation, inclusion, wmin_elt; firstorder.
Qed.
