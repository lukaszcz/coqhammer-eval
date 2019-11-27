From Hammer Require Import Hammer.





Require Import NPeano Omega Permutation List Setoid.
From hahn Require Import HahnBase HahnList HahnRelationsBasic HahnSets.

Set Implicit Arguments.





Hint Unfold Basics.impl : unfolderDb.
Local Ltac u := autounfold with unfolderDb in *; splits; ins; desf;
try solve [intuition; desf; eauto].



Add Parametric Relation (A : Type) : (relation A) (@inclusion A)
reflexivity proved by (@inclusion_refl _)
transitivity proved by (@inclusion_trans _)
as inclusion_rel.

Add Parametric Morphism A : (@inclusion A) with signature
inclusion --> inclusion ++> Basics.impl as inclusion_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@union A) with signature
inclusion ==> inclusion ==> inclusion as union_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@inter_rel A) with signature
inclusion ==> inclusion ==> inclusion as inter_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@minus_rel A) with signature
inclusion ++> inclusion --> inclusion as minus_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@seq A) with signature
inclusion ==> inclusion ==> inclusion as seq_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@irreflexive A) with signature
inclusion --> Basics.impl as irreflexive_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@clos_trans A) with signature
inclusion ==> inclusion as clos_trans_mori.
Proof. u; eauto using clos_trans_mon. Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with signature
inclusion ==> inclusion as clos_refl_trans_mori.
Proof. u; eauto using clos_refl_trans_mon. Qed.

Add Parametric Morphism A : (@clos_refl A) with signature
inclusion ==> inclusion as clos_refl_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@restr_rel A) with signature
set_subset ==> inclusion ==> inclusion as restr_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
eq ==> inclusion ==> inclusion as restr_eq_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@map_rel A B) with signature
eq ==> inclusion ==> inclusion as map_rel_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@acyclic A) with signature
inclusion --> Basics.impl as acyclic_mori.
Proof.
unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism A : (@is_total A) with signature
set_subset --> inclusion ++> Basics.impl as is_total_mori.
Proof. u; ins; desf; eapply H1 in NEQ; desf; eauto. Qed.

Add Parametric Morphism A : (@transp A) with signature
inclusion ==> inclusion as transp_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@functional A) with signature
inclusion --> Basics.impl as functional_mori.
Proof. u. Qed.

Add Parametric Morphism A : (@eqv_rel A) with signature
set_subset ==> inclusion as eqv_rel_mori.
Proof. u. Qed.

Add Parametric Morphism X : (@pow_rel X) with signature
inclusion ==> eq ==> inclusion as pow_rel_mori.
Proof.
ins. induction y0 as [| y' IH].
by simpl; eauto with hahn.
by simpl; rewrite IH, H.
Qed.

Add Parametric Morphism A : (@well_founded A) with signature
inclusion --> Basics.impl as well_founded_mori.
Proof.
repeat red; ins; induction (H0 a); econs; eauto.
Qed.

Add Parametric Morphism A : (@cross_rel A) with signature
set_subset ==> set_subset ==> inclusion as cross_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@bunion A B) with signature
set_subset ==> eq ==> inclusion as bunion_mori.
Proof. u. Qed.

Add Parametric Morphism A B : (@collect_rel A B) with signature
eq ==> inclusion ==> inclusion as collect_rel_mori.
Proof. u; eauto 8. Qed.



Lemma same_relation_exp A (r r' : relation A) (EQ: r ≡ r') :
forall x y, r x y <-> r' x y.
Proof. hammer_hook "HahnEquational" "HahnEquational.same_relation_exp". split; apply EQ. Qed.

Lemma same_relation_refl A : reflexive (@same_relation A).
Proof. hammer_hook "HahnEquational" "HahnEquational.same_relation_refl". u. Qed.

Lemma same_relation_sym A : symmetric (@same_relation A).
Proof. hammer_hook "HahnEquational" "HahnEquational.same_relation_sym". u. Qed.

Lemma same_relation_trans A : transitive (@same_relation A).
Proof. hammer_hook "HahnEquational" "HahnEquational.same_relation_trans". u. Qed.

Add Parametric Relation (A : Type) : (relation A) (@same_relation A)
reflexivity proved by (@same_relation_refl A)
symmetry proved by (@same_relation_sym A)
transitivity proved by (@same_relation_trans A)
as same_rel.

Add Parametric Morphism A : (@inclusion A) with signature
same_relation ==> same_relation ==> iff as inclusion_more.
Proof. u. Qed.

Add Parametric Morphism A : (@union A) with signature
same_relation ==> same_relation ==> same_relation as union_more.
Proof. u. Qed.

Add Parametric Morphism A : (@inter_rel A) with signature
same_relation ==> same_relation ==> same_relation as inter_rel_more.
Proof. u. Qed.

Add Parametric Morphism A : (@minus_rel A) with signature
same_relation ==> same_relation ==> same_relation as minus_rel_more.
Proof. u. Qed.

Add Parametric Morphism A : (@seq A) with signature
same_relation ==> same_relation ==> same_relation as seq_more.
Proof. u. Qed.

Add Parametric Morphism A : (@immediate A) with signature
same_relation ==> same_relation as immediate_more.
Proof. u. Qed.

Add Parametric Morphism A : (@eqv_dom_rel A) with signature
(@Permutation _) ==> same_relation as eqv_dom_rel_more.
Proof. by u; rewrite H in *. Qed.

Add Parametric Morphism A : (@restr_rel A) with signature
set_equiv ==> same_relation ==> same_relation as restr_rel_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@restr_eq_rel A B) with signature
eq ==> same_relation ==> same_relation as restr_eq_rel_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@map_rel A B) with signature
eq ==> same_relation ==> same_relation as map_rel_more.
Proof. u. Qed.

Add Parametric Morphism A : (@clos_trans A) with signature
same_relation ==> same_relation as clos_trans_more.
Proof. u; eauto using clos_trans_mon. Qed.

Add Parametric Morphism A : (@clos_refl_trans A) with signature
same_relation ==> same_relation as clos_refl_trans_more.
Proof. u; eauto using clos_refl_trans_mon. Qed.

Add Parametric Morphism A : (@clos_refl A) with signature
same_relation ==> same_relation as clos_relf_more.
Proof. u. Qed.

Add Parametric Morphism A : (@irreflexive A) with signature
same_relation ==> iff as irreflexive_more.
Proof. u. Qed.

Add Parametric Morphism A : (@acyclic A) with signature
same_relation ==> iff as acyclic_more.
Proof.
unfold acyclic; ins; rewrite H; reflexivity.
Qed.

Add Parametric Morphism A : (@transitive A) with signature
same_relation ==> iff as transitive_more.
Proof. u. Qed.

Add Parametric Morphism A : (@is_total A) with signature
@set_equiv _ ==> same_relation ==> iff as is_total_more.
Proof.
u; split; ins; desf; apply H3 in NEQ; desf; eauto.
Qed.

Add Parametric Morphism A : (@transp A) with signature
same_relation ==> same_relation as transp_more.
Proof. u. Qed.

Add Parametric Morphism A : (@functional A) with signature
same_relation ==> Basics.impl as functional_more.
Proof. u. Qed.

Add Parametric Morphism A : (@eqv_rel A) with signature
@set_equiv _ ==> same_relation as eqv_rel_more.
Proof. u. Qed.

Add Parametric Morphism X : (@pow_rel X) with signature
same_relation ==> eq ==> same_relation as pow_rel_more.
Proof.
by ins; induction y0 as [| y' IH]; ins; rewrite IH, H.
Qed.

Add Parametric Morphism A : (@well_founded A) with signature
same_relation ==> iff as well_founded_more.
Proof.
unfold same_relation; split; eapply well_founded_mori; desf.
Qed.

Add Parametric Morphism A : (@cross_rel A) with signature
set_equiv ==> set_equiv ==> same_relation as cross_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@bunion A B) with signature
set_equiv ==> eq ==> same_relation as bunion_more.
Proof. u. Qed.

Add Parametric Morphism A B : (@collect_rel A B) with signature
eq ==> same_relation ==> same_relation as collect_rel_more.
Proof. u; eauto 8. Qed.







Section PropertiesSeqUnion.

Variables B A : Type.
Implicit Type r : relation A.
Implicit Type rr : B -> relation A.
Ltac uu := autounfold with unfolderDb in *;
try solve [intuition; ins; desf; eauto; firstorder].

Lemma seqA r1 r2 r3 : (r1 ⨾ r2) ⨾ r3 ≡ r1 ⨾ (r2 ⨾ r3).
Proof. hammer_hook "HahnEquational" "HahnEquational.seqA". uu. Qed.

Lemma seq_false_l r : ∅₂ ⨾ r ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_false_l". uu. Qed.

Lemma seq_false_r r : r ⨾ ∅₂ ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_false_r". uu. Qed.

Lemma seq_id_l r :  ⦗fun _ => True⦘ ⨾ r ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_id_l". uu. Qed.

Lemma seq_id_r r : r ⨾ ⦗fun _ => True⦘ ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_id_r". uu. Qed.

Lemma unionA r1 r2 r3 : (r1 ∪ r2) ∪ r3 ≡ r1 ∪ (r2 ∪ r3).
Proof. hammer_hook "HahnEquational" "HahnEquational.unionA". uu. Qed.

Lemma unionC r1 r2 : r1 ∪ r2 ≡ r2 ∪ r1.
Proof. hammer_hook "HahnEquational" "HahnEquational.unionC". uu. Qed.

Lemma unionAC r r' r'' : r ∪ (r' ∪ r'') ≡ r' ∪ (r ∪ r'').
Proof. hammer_hook "HahnEquational" "HahnEquational.unionAC". uu. Qed.

Lemma unionK r : r ∪ r ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.unionK". uu. Qed.

Lemma union_false_r r : r ∪ ∅₂ ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.union_false_r". uu. Qed.

Lemma union_false_l r : ∅₂ ∪ r ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.union_false_l". uu. Qed.

Lemma seq_union_l r1 r2 r : (r1 ∪ r2) ⨾ r ≡ (r1 ⨾ r) ∪ (r2 ⨾ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_union_l". uu. Qed.

Lemma seq_union_r r r1 r2 : r ⨾ (r1 ∪ r2) ≡ (r ⨾ r1) ∪ (r ⨾ r2).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_union_r". uu. Qed.

Lemma seq_bunion_l P rr r : bunion P rr ⨾ r ≡ (⋃n ∈ P, rr n ⨾ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_bunion_l". uu. Qed.

Lemma seq_bunion_r r P rr : r ⨾ bunion P rr ≡ (⋃n ∈ P, r ⨾ rr n).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_bunion_r". uu. Qed.

Lemma minus_union_l r1 r2 r : (r1 ∪ r2) \ r ≡ (r1 \ r) ∪ (r2 \ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.minus_union_l". uu. Qed.

Lemma seq_eqvK (dom : A -> Prop) : ⦗dom⦘ ⨾ ⦗dom⦘ ≡ ⦗dom⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqvK". uu. Qed.

Lemma seq_eqvK_l (dom1 dom2 : A -> Prop) (IMP: forall x, dom2 x -> dom1 x) :
⦗dom1⦘ ⨾ ⦗dom2⦘ ≡ ⦗dom2⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqvK_l". uu. Qed.

Lemma seq_eqvK_r (dom1 dom2 : A -> Prop) (IMP: forall x, dom1 x -> dom2 x) :
⦗dom1⦘ ⨾ ⦗dom2⦘ ≡ ⦗dom1⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqvK_r". uu. Qed.

Lemma seq_eqvC (doma domb : A -> Prop) :
⦗doma⦘ ⨾ ⦗domb⦘ ≡ ⦗domb⦘ ⨾ ⦗doma⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqvC". uu. Qed.

Lemma seq_eqv (doma domb : A -> Prop) :
⦗doma⦘ ⨾ ⦗domb⦘ ≡ ⦗fun x => doma x /\ domb x⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv". uu. Qed.

Lemma union_absorb_l r r' (SUB: r ⊆ r') : r ∪ r' ≡ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.union_absorb_l". uu. Qed.

Lemma union_absorb_r r r' (SUB: r ⊆ r') : r' ∪ r ≡ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.union_absorb_r". uu. Qed.

Lemma id_union (s s': A -> Prop) : ⦗s ∪₁ s'⦘ ≡ ⦗s⦘ ∪ ⦗s'⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.id_union". uu. Qed.

End PropertiesSeqUnion.

Hint Rewrite seq_false_l seq_false_r union_false_l union_false_r unionK : hahn.
Hint Rewrite seq_id_l seq_id_r seq_eqvK : hahn.

Hint Rewrite seq_bunion_l seq_bunion_r seq_union_l seq_union_r : hahn_full.





Section PropertiesBigUnion.

Variables B A : Type.
Implicit Type r : relation A.
Implicit Type rr : B -> relation A.
Ltac uuu := autounfold with unfolderDb in *;
try solve [intuition; ins; desf; eauto; firstorder].

Lemma bunion_empty rr : bunion ∅ rr ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_empty". uuu. Qed.

Lemma bunion_eq a rr : bunion (eq a) rr ≡ rr a.
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_eq". u; splits; ins; desf; eauto. Qed.

Lemma bunion_union_l s s' rr :
bunion (s ∪₁ s') rr ≡ bunion s rr ∪ bunion s' rr.
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_union_l". uuu. Qed.

Lemma bunion_union_r s rr rr' :
bunion s (fun x => rr x ∪ rr' x) ≡ bunion s rr ∪ bunion s rr'.
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_union_r". uuu. Qed.

Lemma bunion_inter_compat_l s r rr :
bunion s (fun x => r ∩ rr x) ≡ r ∩ bunion s rr.
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_inter_compat_l". uuu; split; ins; desf; eauto 8. Qed.

Lemma bunion_inter_compat_r s r rr :
bunion s (fun x => rr x ∩ r) ≡ bunion s rr ∩ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_inter_compat_r". uuu; split; ins; desf; eauto 8. Qed.

Lemma bunion_minus_compat_r s r rr :
bunion s (fun x => rr x \ r) ≡ bunion s rr \ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_minus_compat_r". uuu; split; ins; desf; eauto 8. Qed.

End PropertiesBigUnion.






Section PropertiesInter.

Variable A : Type.
Implicit Type r : relation A.

Lemma interA r1 r2 r3 : (r1 ∩ r2) ∩ r3 ≡ r1 ∩ (r2 ∩ r3).
Proof. hammer_hook "HahnEquational" "HahnEquational.interA". u. Qed.

Lemma interC r1 r2 : r1 ∩ r2 ≡ r2 ∩ r1.
Proof. hammer_hook "HahnEquational" "HahnEquational.interC". u. Qed.

Lemma interAC r r' r'' : r ∩ (r' ∩ r'') ≡ r' ∩ (r ∩ r'').
Proof. hammer_hook "HahnEquational" "HahnEquational.interAC". u. Qed.

Lemma interK r : r ∩ r ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.interK". u. Qed.

Lemma inter_false_r r : r ∩ ∅₂ ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_false_r". u. Qed.

Lemma inter_false_l r : ∅₂ ∩ r ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_false_l". u. Qed.

Lemma inter_union_r r r1 r2 : r ∩ (r1 ∪ r2) ≡ (r ∩ r1) ∪ (r ∩ r2).
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_union_r". u. Qed.

Lemma inter_union_l r r1 r2 : (r1 ∪ r2) ∩ r ≡ (r1 ∩ r) ∪ (r2 ∩ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_union_l". u. Qed.

Lemma inter_absorb_l r r' (SUB: r ⊆ r') : r' ∩ r ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_absorb_l". u. Qed.

Lemma inter_absorb_r r r' (SUB: r ⊆ r') : r ∩ r' ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_absorb_r". u. Qed.

Lemma inter_trans (r r' i : relation A) (T: transitive i) :
(r ∩ i) ⨾ (r' ∩ i) ⊆ (r ⨾ r') ∩ i.
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_trans". u. Qed.

Lemma inter_inclusion (r i : relation A) : r ∩ i ⊆ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_inclusion". u. Qed.

Lemma id_inter (s s' : A -> Prop) : ⦗s ∩₁ s'⦘ ≡ ⦗s⦘ ⨾ ⦗s'⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.id_inter". u. Qed.
End PropertiesInter.

Hint Rewrite inter_false_l inter_false_r interK : hahn.





Section PropertiesMinus.

Variable A : Type.
Implicit Type r : relation A.

Lemma minus_false_r r : r \ ∅₂ ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.minus_false_r". u. Qed.

Lemma minus_false_l r : ∅₂ \ r ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.minus_false_l". u. Qed.

Lemma minusK r : r \ r ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.minusK". u. Qed.

Lemma minus_absorb r r' (SUB: r ⊆ r') : r \ r' ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.minus_absorb". u. Qed.

End PropertiesMinus.

Hint Rewrite minus_false_l minus_false_r minusK : hahn.





Section PropertiesClos.

Variable A : Type.
Implicit Types r : relation A.

Lemma rtE r : r ＊ ≡ ⦗fun _ => True⦘ ∪ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.rtE".
u; rewrite clos_refl_transE in *; tauto.
Qed.

Lemma crE r : r ^? ≡ ⦗fun _ => True⦘ ∪ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.crE". u. Qed.

Lemma rtEE r : r＊ ≡ ⋃n, r ^^ n.
Proof. hammer_hook "HahnEquational" "HahnEquational.rtEE".
split; ins; desc.
u.
induction H using clos_refl_trans_ind_left; desc.
by exists 0.
by exists (S a); vauto.
apply inclusion_bunion_l; ins.
induction x; ins; [|rewrite IHx];
unfold eqv_rel, seq; red; ins; desf; vauto.
Qed.

Lemma ct_begin r : r⁺ ≡ r ⨾ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_begin".
unfold seq; split; red; ins; desf; rewrite t_step_rt in *; eauto.
Qed.

Lemma ct_end r : r⁺ ≡ r ＊ ⨾ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_end".
unfold seq; split; red; ins; desf; rewrite t_rt_step in *; eauto.
Qed.

Lemma ctEE r : r⁺ ≡ ⋃ n, r ^^ (S n).
Proof. hammer_hook "HahnEquational" "HahnEquational.ctEE".
by rewrite ct_end, rtEE, seq_bunion_l.
Qed.

Lemma rt_begin r :
r ＊ ≡ ⦗fun _ => True⦘ ∪ r ⨾ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_begin".
rewrite <- ct_begin, <- rtE; vauto.
Qed.

Lemma rt_end r :
r ＊ ≡ ⦗fun _ => True⦘ ∪ r ＊ ⨾ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_end".
rewrite <- ct_end, <- rtE; vauto.
Qed.

Lemma ct_of_trans r (T: transitive r) : r⁺ ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_of_trans".
split; eauto with hahn.
Qed.

Lemma rt_of_trans r (T: transitive r) : r ＊ ≡ r ^?.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_of_trans".
rewrite rtE, crE, ct_of_trans; vauto.
Qed.

Lemma cr_ct r : r ^? ⨾ r⁺ ≡ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_ct".
unfold seq, clos_refl; split; red; ins; desf; eauto using t_trans, t_step.
Qed.

Lemma cr_rt r : r ^? ⨾ r ＊ ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_rt".
unfold seq, clos_refl; split; red; ins; desf; eauto using rt_trans, rt_step.
Qed.

Lemma ct_rt r : r⁺ ⨾ r ＊ ≡ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_rt".
unfold seq; split; red; ins; desf; eauto using t_rt_trans, rt_refl.
Qed.

Lemma ct_ct r : r⁺ ⨾ r⁺ ⊆ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_ct".
unfold seq; red; ins; desf; eauto using t_trans.
Qed.

Lemma ct_cr r : r⁺ ⨾ r ^? ≡ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_cr".
unfold seq, clos_refl; split; red; ins; desf; eauto using t_trans, t_step.
Qed.

Lemma rt_rt r : r ＊ ⨾ r ＊ ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_rt".
unfold seq; split; red; ins; desf; eauto using rt_trans, rt_refl.
Qed.

Lemma rt_ct r : r ＊ ⨾ r⁺ ≡ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_ct".
unfold seq; split; red; ins; desf; eauto using rt_t_trans, rt_refl.
Qed.

Lemma rt_cr r : r ＊ ⨾ r ^? ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_cr".
unfold seq, clos_refl; split; red; ins; desf; eauto using rt_trans, rt_step.
Qed.

Lemma cr_of_ct r : (r⁺) ^? ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_of_ct".
by rewrite rt_begin, ct_begin, crE.
Qed.

Lemma cr_of_cr r : (r ^?) ^? ≡ r ^?.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_of_cr".
by rewrite !crE, <- unionA, unionK.
Qed.

Lemma cr_of_rt r : (r ＊) ^? ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_of_rt".
by rewrite rtE, <- crE, cr_of_cr.
Qed.

Lemma ct_of_ct r: (r⁺)⁺ ≡ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_of_ct".
split; eauto with hahn.
Qed.

Lemma ct_of_union_ct_l r r' : (r⁺ ∪ r')⁺ ≡ (r ∪ r')⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_of_union_ct_l".
split; eauto 8 with hahn.
Qed.

Lemma ct_of_union_ct_r r r' : (r ∪ r'⁺)⁺ ≡ (r ∪ r')⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_of_union_ct_r".
split; eauto 8 with hahn.
Qed.

Lemma ct_of_cr r: (r ^?)⁺ ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_of_cr".
split; eauto with hahn.
apply inclusion_rt_ind_left; vauto.
rewrite ct_begin at 2; eauto with hahn.
Qed.

Lemma ct_of_rt r: (r ＊)⁺ ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_of_rt".
split; eauto with hahn.
Qed.

Lemma rt_of_ct r : (r⁺) ＊ ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_of_ct".
split; eauto using inclusion_rt_rt2 with hahn.
Qed.

Lemma rt_of_cr r : (r ^?) ＊ ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_of_cr".
split; eauto using inclusion_rt_rt2 with hahn.
Qed.

Lemma rt_of_rt r : (r ＊) ＊ ≡ r ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_of_rt".
split; eauto using inclusion_rt_rt2 with hahn.
Qed.

Lemma cr_union_l r r' : (r ∪ r') ^? ≡ r ^? ∪ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_union_l".
by rewrite !crE, unionA.
Qed.

Lemma cr_union_r r r' : (r ∪ r') ^? ≡ r ∪ r' ^?.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_union_r".
by rewrite unionC, cr_union_l, unionC.
Qed.

Lemma seq_rtE_r r r' : r ⨾ r' ＊ ≡ r ∪ (r ⨾ r') ⨾ r' ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_rtE_r".
by rewrite rt_begin at 1; rewrite ?seq_union_r, ?seq_id_r, ?seqA.
Qed.

Lemma seq_rtE_l r r' : r' ＊ ⨾ r ≡ r ∪ (r' ＊ ⨾ r' ⨾ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_rtE_l".
by rewrite rt_end at 1; rewrite ?seq_union_l, ?seq_id_l, ?seqA.
Qed.

Lemma ct_step r : r ⊆ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_step".
firstorder.
Qed.

Lemma rt_unit r : r＊ ⨾ r ⊆ r＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_unit".
rewrite <- ct_end; apply inclusion_t_rt.
Qed.

Lemma ct_unit r : r⁺ ⨾ r ⊆ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_unit".
unfold seq, inclusion; ins; desf; vauto.
Qed.

Lemma trailing_refl r r' e : r ⊆ r' -> r ⊆ r' ⨾ e^?.
Proof. hammer_hook "HahnEquational" "HahnEquational.trailing_refl".
firstorder.
Qed.

Lemma cr_seq (r r' : relation A) : r^? ⨾ r' ≡ r' ∪ r ⨾ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_seq". split; autounfold with unfolderDb; ins; desf; eauto. Qed.

Lemma cr_helper (r r' : relation A) d (H: r ⨾ ⦗d⦘ ⊆ ⦗d⦘ ⨾ r') : r^? ⨾ ⦗d⦘ ⊆ ⦗d⦘ ⨾ r'^? .
Proof. hammer_hook "HahnEquational" "HahnEquational.cr_helper".
rewrite crE.
autounfold with unfolderDb in *; ins; desf; eauto.
edestruct H; eauto. desf. eauto.
Qed.
End PropertiesClos.

Hint Rewrite cr_of_ct cr_of_cr cr_of_rt
ct_of_ct ct_of_cr ct_of_rt
rt_of_ct rt_of_cr rt_of_rt : hahn.

Definition good_ctx A (P: relation A -> relation A) :=
<< MON: Morphisms.Proper (inclusion ==> inclusion) P >> /\
<< CUN: forall (rr : nat -> relation A), P (⋃ n, rr n) ⊆ ⋃ n, P (rr n) >>.

Section good_ctx_lemmas.

Variables A : Type.
Implicit Types P Q : relation A -> relation A.
Implicit Types r : relation A.

Lemma good_ctx_id : good_ctx (fun x : relation A => x).
Proof. hammer_hook "HahnEquational" "HahnEquational.good_ctx_id".
split; unnw; ins; vauto.
Qed.

Lemma good_ctx_const r : good_ctx (fun x : relation A => r).
Proof. hammer_hook "HahnEquational" "HahnEquational.good_ctx_const".
split; unnw; ins; repeat red; ins; vauto.
Qed.

Lemma good_ctx_seq_l P (GP : good_ctx P) r :
good_ctx (fun x => P x ⨾ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.good_ctx_seq_l".
cdes GP; split; unnw; ins; [by do 2 red; ins; rewrite H|].
by rewrite CUN, seq_bunion_l.
Qed.

Lemma good_ctx_seq_r P (GP : good_ctx P) r :
good_ctx (fun x => r ⨾ P x).
Proof. hammer_hook "HahnEquational" "HahnEquational.good_ctx_seq_r".
cdes GP; split; unnw; ins; [by do 2 red; ins; rewrite H|].
by rewrite CUN, seq_bunion_r.
Qed.

Lemma good_ctx_union P (GP : good_ctx P) Q (GQ : good_ctx Q) :
good_ctx (fun x => P x ∪ Q x).
Proof. hammer_hook "HahnEquational" "HahnEquational.good_ctx_union".
cdes GP; cdes GQ; split; unnw; ins; [by do 2 red; ins; rewrite H|].
rewrite CUN, CUN0; firstorder.
Qed.

Lemma good_ctx_compose P (GP : good_ctx P) Q (GQ : good_ctx Q) :
good_ctx (fun x => P (Q x)).
Proof. hammer_hook "HahnEquational" "HahnEquational.good_ctx_compose".
cdes GP; cdes GQ; split; unnw; ins; [by do 2 red; ins; rewrite H|].
rewrite CUN0, CUN; apply inclusion_bunion_l; vauto.
Qed.

Lemma seq_pow_l r n : r ^^ n ⨾ r ≡ r ⨾ r ^^ n.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_pow_l".
induction n; ins; autorewrite with hahn; try done.
by rewrite IHn at 1; rewrite seqA.
Qed.

Lemma rt_ind_left P (G: good_ctx P) r r' :
P ⦗fun _ => True⦘ ⊆ r' ->
(forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') ->
P r＊ ⊆ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_ind_left".
ins; cdes G; rewrite (proj1 (rtEE _)).
etransitivity; [eapply CUN|apply inclusion_bunion_l]; ins.
induction x; ins; rewrite (proj1 (seq_pow_l _ _)); eauto.
Qed.

Lemma rt_ind_right P (G: good_ctx P) r r' :
P ⦗fun _ => True⦘ ⊆ r' ->
(forall k, P k ⊆ r' -> P (k ⨾ r) ⊆ r') ->
P r＊ ⊆ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_ind_right".
ins; cdes G; rewrite (proj1 (rtEE _)).
etransitivity; [eapply CUN|apply inclusion_bunion_l]; ins.
induction x; ins; eauto.
Qed.

Lemma ct_ind_left P (G: good_ctx P) r r' :
P r ⊆ r' -> (forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') -> P ( r⁺ ) ⊆ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_ind_left".
ins; cdes G; rewrite (proj1 (ct_end _)).
apply rt_ind_left with (P := fun x => P (x ⨾ r)); ins;
eauto using good_ctx_compose, good_ctx_seq_l, good_ctx_id.
by rewrite (proj1 (seq_id_l _)).
by rewrite (proj1 (seqA _ _ _)); eauto.
Qed.

Lemma ct_ind_right P (G: good_ctx P) r r' :
P r ⊆ r' -> (forall k, P k ⊆ r' -> P (k ⨾ r) ⊆ r') -> P ( r⁺ ) ⊆ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_ind_right".
ins; cdes G; rewrite (proj1 (ctEE _)).
etransitivity; [eapply CUN|apply inclusion_bunion_l]; ins.
induction x; ins; eauto.
by rewrite (proj1 (seq_id_l _)).
Qed.

Lemma ct_ind_left_helper P (G: good_ctx P) x r (EQ: x = r⁺) r' :
P r ⊆ r' -> (forall k, P k ⊆ r' -> P (r ⨾ k) ⊆ r') -> P x ⊆ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_ind_left_helper".
by subst; apply ct_ind_left.
Qed.

End good_ctx_lemmas.

Hint Resolve good_ctx_id good_ctx_const good_ctx_seq_l
good_ctx_seq_r good_ctx_union good_ctx_compose : hahn.

Section ExtraPropertiesClos.

Variable A : Type.
Implicit Types r : relation A.

Lemma ct_seq_swap r r' :
(r ⨾ r')⁺ ⨾ r ≡ r ⨾ (r' ⨾ r)⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_seq_swap".
split.
{ apply ct_ind_left with (P := fun x => x ⨾ _); auto with hahn;
ins; rewrite seqA; eauto with hahn.
rewrite ct_begin, H, ?seqA; eauto with hahn. }
apply ct_ind_right with (P := fun x => _ ⨾ x); auto with hahn;
ins; rewrite <- seqA; eauto with hahn.
rewrite ct_end, H, <- ?seqA; eauto with hahn.
Qed.

Lemma rt_seq_swap r r' :
(r ⨾ r') ＊ ⨾ r ≡ r ⨾ (r' ⨾ r) ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.rt_seq_swap".
by rewrite !rtE; autorewrite with hahn hahn_full; rewrite ct_seq_swap.
Qed.

Lemma ct_rotl r r' :
(r ⨾ r')⁺ ≡ r ⨾ (r' ⨾ r) ＊ ⨾ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_rotl".
by rewrite rt_seq_swap, ct_begin, seqA.
Qed.

Lemma crt_double r :
r ＊ ≡ r ^? ⨾ (r ⨾ r) ＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.crt_double".
split; [|by eauto 7 using inclusion_seq_trans, inclusion_rt_rt2 with hahn].
apply inclusion_rt_ind_left; eauto with hahn.
rewrite !crE; autorewrite with hahn hahn_full.
rewrite <- seqA, <- ct_begin; eauto with hahn.
Qed.

End ExtraPropertiesClos.





Lemma eqv_empty A : ⦗@set_empty A⦘ ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.eqv_empty".
autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma seq_eqv_r A (r : relation A) dom :
r ⨾ ⦗dom⦘ ≡ (fun x y => r x y /\ dom y).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv_r".
autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma seq_eqv_l A (r : relation A) dom :
⦗dom⦘ ⨾ r ≡ (fun x y => dom x /\ r x y).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv_l".
autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_l A (r : relation A) dom :
⦗dom⦘ ⨾ r ⊆ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_seq_eqv_l".
autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma inclusion_seq_eqv_r A (r : relation A) dom :
r ⨾ ⦗dom⦘ ⊆ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_seq_eqv_r".
autounfold with unfolderDb; intuition; desf; eauto.
Qed.

Lemma seq_eqv_lr A (r : relation A) dom1 dom2 :
⦗dom1⦘ ⨾ r ⨾ ⦗dom2⦘ ≡ (fun x y : A => dom1 x /\ r x y /\ dom2 y).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv_lr".
autounfold with unfolderDb; intuition; desf; eauto 10.
Qed.

Lemma seq_eqv_inter_ll A S (r r' : relation A) :
(⦗S⦘ ⨾ r) ∩ r' ≡ ⦗S⦘ ⨾ r ∩ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv_inter_ll". autounfold with unfolderDb; intuition; desf; eauto. Qed.

Lemma seq_eqv_inter_lr A S (r r' : relation A) :
(r ⨾ ⦗S⦘) ∩ r' ≡ r ∩ r' ⨾ ⦗S⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv_inter_lr". autounfold with unfolderDb; intuition; desf; eauto. Qed.

Lemma seq_eqv_minus_lr A (s : A -> Prop) (r r' : relation A) :
(r ⨾ ⦗s⦘) \ r' ≡ (r \ r') ⨾ ⦗s⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv_minus_lr". autounfold with unfolderDb; intuition; desf; eauto. Qed.

Lemma seq_eqv_minus_ll A (s : A -> Prop) (r r' : relation A) :
(⦗s⦘ ⨾ r) \ r' ≡ ⦗s⦘ ⨾ (r \ r').
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_eqv_minus_ll". autounfold with unfolderDb; intuition; desf; eauto. Qed.

Hint Rewrite eqv_empty : hahn.





Lemma same_relation_restr A (f : A -> Prop) r r' :
(forall x (CONDx: f x) y (CONDy: f y), r x y <-> r' x y) ->
(restr_rel f r ≡ restr_rel f r').
Proof. hammer_hook "HahnEquational" "HahnEquational.same_relation_restr". u; firstorder. Qed.

Lemma restr_restr A (d d' : A -> Prop) r :
restr_rel d (restr_rel d' r) ≡ restr_rel (d' ∩₁ d) r.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_restr". u. Qed.

Lemma restrC A (d d': A -> Prop) r :
restr_rel d (restr_rel d' r) ≡ restr_rel d' (restr_rel d r).
Proof. hammer_hook "HahnEquational" "HahnEquational.restrC". u. Qed.

Lemma restr_relE A (d : A -> Prop) r :
restr_rel d r ≡ <| d |> ;; r ;; <| d |>.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_relE". rewrite seq_eqv_lr; u. Qed.

Lemma restr_union A (f : A -> Prop) r r' :
restr_rel f (r ∪ r') ≡ restr_rel f r ∪ restr_rel f r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_union". u. Qed.

Lemma restr_inter A (f : A -> Prop) r r' :
restr_rel f (r ∩ r') ≡ restr_rel f r ∩ restr_rel f r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_inter". u. Qed.

Lemma restr_minus A (f : A -> Prop) r r' :
restr_rel f (r \ r') ≡ restr_rel f r \ restr_rel f r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_minus". u. Qed.

Lemma restr_minus_alt A (f : A -> Prop) r r' :
restr_rel f (r \ r') ≡ restr_rel f r \ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_minus_alt". u. Qed.

Lemma restr_bunion A B (f : B -> Prop) (s: A -> Prop) rr :
restr_rel f (⋃x ∈ s, rr x) ≡ ⋃x ∈ s, restr_rel f (rr x).
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_bunion". u. Qed.

Lemma union_restr A (f : A -> Prop) r r' :
restr_rel f r ∪ restr_rel f r' ≡ restr_rel f (r ∪ r').
Proof. hammer_hook "HahnEquational" "HahnEquational.union_restr". u. Qed.

Lemma bunion_restr A B (f : B -> Prop) (s: A -> Prop) rr :
(⋃x ∈ s, restr_rel f (rr x)) ≡ restr_rel f (⋃x ∈ s, rr x).
Proof. hammer_hook "HahnEquational" "HahnEquational.bunion_restr". u. Qed.

Lemma restr_ct A (d: A -> Prop) r :
(restr_rel d r)⁺ ⊆ restr_rel d r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_ct". u; induction H; desf; eauto using clos_trans. Qed.

Lemma restr_seq_eqv_l A (f : A -> Prop) d r :
restr_rel f (⦗d⦘⨾ r) ≡ ⦗d⦘⨾ restr_rel f r.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_seq_eqv_l". u; eauto 6. Qed.

Lemma restr_seq_eqv_r A (f : A -> Prop) r d :
restr_rel f (r⨾ ⦗d⦘) ≡ restr_rel f r⨾ ⦗d⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_seq_eqv_r". u; eauto 6. Qed.

Lemma restr_eq_union A r r' B (f : A -> B) :
restr_eq_rel f (r ∪ r') ≡ restr_eq_rel f r ∪ restr_eq_rel f r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_eq_union". u. Qed.

Lemma restr_eq_bunion A (s : A -> Prop) B (rr: A -> relation B) C (f : B -> C) :
restr_eq_rel f (⋃x ∈ s, rr x) ≡ ⋃x ∈ s, restr_eq_rel f (rr x).
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_eq_bunion". u. Qed.

Lemma restr_eq_elim A (r : relation A) B (f: A -> B)
(R: forall x y, r x y -> f x = f y) :
restr_eq_rel f r ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_eq_elim". u. Qed.

Lemma restr_eq_seq_eqv_l A (r : relation A) B (f : A -> B) dom :
restr_eq_rel f (⦗dom⦘⨾ r) ≡ ⦗dom⦘⨾ restr_eq_rel f r.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_eq_seq_eqv_l". u. Qed.

Lemma restr_eq_seq_eqv_r A (r : relation A) B (f : A -> B) dom :
restr_eq_rel f (r⨾ ⦗dom⦘) ≡ restr_eq_rel f r⨾ ⦗dom⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_eq_seq_eqv_r". u. Qed.

Lemma restr_full {A} (r : relation A) :
restr_rel (fun _ : A => True) r ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_full". u. Qed.





Section TranspProperties.

Variable A : Type.
Implicit Type r : relation A.
Implicit Type d : A -> Prop.

Lemma transp_inv r : r⁻¹ ⁻¹ ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_inv". u. Qed.

Lemma transp_eqv_rel d : ⦗d⦘⁻¹ ≡ ⦗d⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_eqv_rel". u. Qed.

Lemma transp_cross d d' : (d × d')⁻¹ ≡ (d' × d).
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_cross". u. Qed.

Lemma transp_union r1 r2 : (r1 ∪ r2)⁻¹ ≡ r1⁻¹ ∪ r2⁻¹.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_union". u. Qed.

Lemma transp_seq r1 r2 : (r1 ⨾ r2)⁻¹ ≡ r2⁻¹ ⨾ r1⁻¹.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_seq". u. Qed.

Lemma transp_inter r1 r2 : (r1 ∩ r2)⁻¹ ≡ r1⁻¹ ∩ r2⁻¹.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_inter". u. Qed.

Lemma transp_minus r1 r2 : (r1 \ r2)⁻¹ ≡ r1⁻¹ \ r2⁻¹.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_minus". u. Qed.

Lemma transp_rt r : (r＊) ⁻¹ ≡ (r⁻¹)＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_rt". u; induction H; vauto. Qed.

Lemma transp_ct r : (r⁺)⁻¹ ≡ (r⁻¹)⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_ct". u; induction H; vauto. Qed.

Lemma transp_cr r : (r^?)⁻¹ ≡ (r⁻¹)^?.
Proof. hammer_hook "HahnEquational" "HahnEquational.transp_cr". u. Qed.

Lemma transitive_transp r : transitive r -> transitive (r⁻¹).
Proof. hammer_hook "HahnEquational" "HahnEquational.transitive_transp". u. Qed.

Lemma inclusion_transpE r r' : r⁻¹ ⊆ r'⁻¹ -> r ⊆ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_transpE". u. Qed.

Lemma same_relation_transpE r r' : transp r ≡ transp r' -> r ≡ r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.same_relation_transpE". u. Qed.

End TranspProperties.

Hint Rewrite transp_inv transp_cross transp_eqv_rel : hahn.
Hint Rewrite transp_inv transp_cross transp_eqv_rel transp_union transp_seq
transp_inter transp_minus transp_rt transp_ct transp_cr : rel_transp.

Ltac rel_transp :=
first [apply inclusion_transpE | apply same_relation_transpE ];
autorewrite with rel_transp.





Lemma map_rel_false A B (f : A -> B) :
map_rel f ∅₂ ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.map_rel_false". u. Qed.

Lemma map_rel_cross A B (f : A -> B) s s' :
map_rel f (s × s') ≡ (fun x => s (f x)) × (fun x => s' (f x)).
Proof. hammer_hook "HahnEquational" "HahnEquational.map_rel_cross". u. Qed.

Lemma map_rel_union A B (f : A -> B) r r' :
map_rel f (r ∪ r') ≡ map_rel f r ∪ map_rel f r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.map_rel_union". u. Qed.

Lemma map_rel_inter A B (f : A -> B) r r' :
map_rel f (r ∩ r') ≡ map_rel f r ∩ map_rel f r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.map_rel_inter". u. Qed.

Lemma map_rel_minus A B (f : A -> B) r r' :
map_rel f (r \ r') ≡ map_rel f r \ map_rel f r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.map_rel_minus". u. Qed.

Lemma map_rel_restr A B (f : A -> B) d r :
map_rel f (restr_rel d r) ≡ restr_rel (fun x => d (f x)) (map_rel f r).
Proof. hammer_hook "HahnEquational" "HahnEquational.map_rel_restr". u. Qed.





Lemma pow_t A n (r: relation A) : transitive r -> r ⨾ r^^n ⊆ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.pow_t".
ins; induction n; simpl.
by rewrite seq_id_r.
by rewrite <- seqA, IHn; unfold inclusion, seq; ins; desf; eauto.
Qed.

Lemma pow_seq A n (r: relation A): r^^n ⨾ r ≡ r^^(S n).
Proof. hammer_hook "HahnEquational" "HahnEquational.pow_seq". by simpl. Qed.

Lemma pow_nm A (n m : nat) (r : relation A) : r^^n ⨾ r^^m ≡ r^^(n + m).
Proof. hammer_hook "HahnEquational" "HahnEquational.pow_nm".
induction m; simpl.
by rewrite <- plus_n_O; rewrite seq_id_r.
by rewrite <- seqA, IHm, pow_seq, plus_n_Sm.
Qed.

Lemma pow_unit A (r : relation A) : r^^1 ≡ r.
Proof. hammer_hook "HahnEquational" "HahnEquational.pow_unit". by simpl; rewrite seq_id_l. Qed.

Lemma pow_inclusion (n : nat ) A (r r' : relation A): r ≡ r' -> r^^n ≡ r'^^n.
Proof. hammer_hook "HahnEquational" "HahnEquational.pow_inclusion". by ins; rewrite H. Qed.

Lemma pow_rt (n : nat) A (r: relation A) : r^^n ⊆ r＊.
Proof. hammer_hook "HahnEquational" "HahnEquational.pow_rt".
induction n; simpl; eauto with hahn.
rewrite IHn.
assert (r ⊆ r＊) by eauto with hahn.
rewrite H at 2.
by rewrite rt_rt.
Qed.







Section PropertiesCross.

Variable A : Type.
Implicit Type s : A -> Prop.

Lemma cross_false_r s : s × ∅ ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.cross_false_r". u. Qed.

Lemma cross_false_l s : ∅ × s ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.cross_false_l". u. Qed.

Lemma ct_of_cross s s' : (s × s')⁺ ≡ s × s'.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_of_cross". u; induction H; desf; eauto. Qed.

End PropertiesCross.

Hint Rewrite cross_false_l cross_false_r : hahn.





Lemma collect_rel_empty A B (f : A -> B) : collect_rel f ∅₂ ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.collect_rel_empty". u. Qed.

Lemma collect_rel_cross A B (f : A -> B) s s' :
collect_rel f (s × s') ≡ set_collect f s × set_collect f s'.
Proof. hammer_hook "HahnEquational" "HahnEquational.collect_rel_cross". u; eauto 8. Qed.

Lemma collect_rel_union A B (f : A -> B) s s' :
collect_rel f (s ∪ s') ≡ collect_rel f s ∪ collect_rel f s'.
Proof. hammer_hook "HahnEquational" "HahnEquational.collect_rel_union". u; eauto 8. Qed.

Lemma collect_rel_bunion A B (f : A -> B) C (s : C -> Prop) rr :
collect_rel f (⋃x ∈ s, rr x) ≡ ⋃x ∈ s, collect_rel f (rr x).
Proof. hammer_hook "HahnEquational" "HahnEquational.collect_rel_bunion". u; eauto 8. Qed.

Hint Rewrite collect_rel_empty collect_rel_cross : hahn.
Hint Rewrite collect_rel_union collect_rel_bunion : hahn.





Lemma acyclic_mon A (r r' : relation A) :
acyclic r -> r' ⊆ r -> acyclic r'.
Proof. hammer_hook "HahnEquational" "HahnEquational.acyclic_mon".
eby repeat red; ins; eapply H, clos_trans_mon.
Qed.

Lemma acyclic_seqC A (r r' : relation A) :
acyclic (r ⨾ r') <-> acyclic (r' ⨾ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.acyclic_seqC".
by unfold acyclic; rewrite ct_rotl, irreflexive_seqC, !seqA, <- ct_end.
Qed.

Lemma restr_seq_compl_l A d (r : relation A) : restr_rel d (⦗set_compl d⦘ ;; r) ≡ ∅₂.
Proof. hammer_hook "HahnEquational" "HahnEquational.restr_seq_compl_l". u. Qed.

Lemma clos_trans_imm :
forall A (r : relation A) (I: irreflexive r)
(T: transitive r) L (ND: NoDup L) a b
(D: forall c, r a c -> r c b -> In c L)
(REL: r a b),
(immediate r)⁺ a b.
Proof. hammer_hook "HahnEquational" "HahnEquational.clos_trans_imm".
intros until 3; induction ND; ins; vauto.
destruct (classic (r a x /\ r x b)) as [|N]; desf;
[apply t_trans with x|]; eapply IHND; ins;
forward (by eapply (D c); eauto) as K; desf; exfalso; eauto.
Qed.

Lemma ct_imm1 :
forall A (r : relation A) (I: irreflexive r) (T: transitive r)
acts (FIN : dom_rel r ⊆₁ (fun x => In x acts)),
r ≡ (immediate r)⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_imm1".
split; cycle 1.
by rewrite immediateE, inclusion_minus_rel; auto with hahn.
assert (M: forall x y, r x y -> In x (undup acts)).
by ins; eapply in_undup_iff, FIN; vauto.
red; ins; eapply clos_trans_imm; eauto.
Qed.

Lemma ct_imm2 :
forall A (r : relation A) (I: irreflexive r) (T: transitive r)
acts (FIN : codom_rel r ⊆₁ (fun x => In x acts)),
r ≡ (immediate r)⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.ct_imm2".
split; cycle 1.
by rewrite immediateE, inclusion_minus_rel; auto with hahn.
assert (M: forall x y, r x y -> In y (undup acts)).
by ins; eapply in_undup_iff, FIN; vauto.
red; ins; eapply clos_trans_imm; eauto.
Qed.


Lemma immediate_clos_trans_elim A (r : relation A) a b :
immediate (r⁺) a b ->
r a b /\ (forall c, r⁺ a c -> r⁺ c b -> False).
Proof. hammer_hook "HahnEquational" "HahnEquational.immediate_clos_trans_elim".
unfold immediate; ins; desf; split; ins.
apply t_step_rt in H; desf.
apply clos_refl_transE in H1; desf; exfalso; eauto using t_step.
Qed.

Lemma clos_trans_immediate1 A (r : relation A) (T: transitive r) a b :
(immediate r)⁺ a b -> r a b.
Proof. hammer_hook "HahnEquational" "HahnEquational.clos_trans_immediate1".
unfold immediate; induction 1; desf; eauto.
Qed.

Lemma clos_trans_immediate2 A (r : relation A)
(T: transitive r) (IRR: irreflexive r) dom
(D: forall a b (r: r a b), In b dom) a b :
r a b ->
(immediate r)⁺ a b.
Proof. hammer_hook "HahnEquational" "HahnEquational.clos_trans_immediate2".
assert (D': forall c, r a c -> r c b -> In c dom).
by ins; apply D in H; desf.
clear D; revert a b D'.
remember (length dom) as n; revert dom Heqn; induction n.
by destruct dom; ins; vauto.
ins; destruct (classic (exists c, r a c /\ r c b)); desf.
2: by eapply t_step; split; ins; eauto.
forward (by eapply D'; eauto) as K; apply in_split in K; desf.
rewrite app_length in *; ins; rewrite <- plus_n_Sm, <- app_length in *; desf.
apply t_trans with c; eapply IHn with (dom := l1 ++ l2); ins;
forward (by eapply (D' c0); eauto);
rewrite !in_app_iff; ins; desf; eauto; exfalso; eauto.
Qed.

Lemma clos_trans_imm2 :
forall A (r : relation A) (I: irreflexive r)
(T: transitive r) L a b
(D: forall c, r a c -> r c b -> In c L)
(REL: r a b),
(immediate r)⁺ a b.
Proof. hammer_hook "HahnEquational" "HahnEquational.clos_trans_imm2".
ins; eapply clos_trans_imm with (L := undup L); ins;
try rewrite in_undup_iff; eauto using nodup_undup.
Qed.


Lemma total_immediate_unique:
forall A (r: A -> A -> Prop) (P: A -> Prop)
(Tot: is_total P r)
a b c (pa: P a) (pb: P b) (pc: P c)
(iac: immediate r a c)
(ibc: immediate r b c),
a = b.
Proof. hammer_hook "HahnEquational" "HahnEquational.total_immediate_unique".
ins; destruct (classic (a = b)) as [|N]; eauto.
exfalso; unfold immediate in *; desf.
eapply Tot in N; eauto; desf; eauto.
Qed.

Lemma acyclic_case_split A (r : relation A) f :
acyclic r <->
acyclic (restr_rel f r) /\ (forall x (NEG: ~ f x) (CYC: r⁺ x x), False).
Proof. hammer_hook "HahnEquational" "HahnEquational.acyclic_case_split".
unfold restr_rel; repeat split; repeat red; ins; desc; eauto.
by eapply H, clos_trans_mon; eauto; instantiate; ins; desf.
destruct (classic (f x)) as [K|K]; eauto.
assert (M: (fun a b => r a b /\ f a /\ f b) ＊ x x) by vauto.
generalize K; revert H0 M K; generalize x at 2 3 5; ins.
apply clos_trans_tn1 in H0; induction H0; eauto 6 using rt_t_trans, t_step.
destruct (classic (f y)); eauto 6 using clos_refl_trans.
eapply H1; eauto.
eapply t_rt_trans, rt_trans; eauto using t_step, clos_trans_in_rt, clos_tn1_trans.
by eapply clos_refl_trans_mon; eauto; instantiate; ins; desf.
Qed.

Lemma seqA2 A (r r' r'' : relation A) x y :
((r⨾ r')⨾ r'') x y <-> (r⨾ r'⨾ r'') x y.
Proof. hammer_hook "HahnEquational" "HahnEquational.seqA2".
unfold seq; split; ins; desf; eauto 8.
Qed.

Lemma inclusion_t_r_t A (r r' r'': relation A) :
r ⊆ r'' ->
r' ⊆ r'' ＊ ->
r⁺ ⨾ r' ⊆ r''⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_t_r_t".
by ins; rewrite H, H0, ct_rt.
Qed.

Lemma inclusion_r_t_t A (r r' r'': relation A) :
r ⊆ r'' ＊ ->
r' ⊆ r'' ->
r ⨾ r'⁺ ⊆ r''⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_r_t_t".
by ins; rewrite H, H0, rt_ct.
Qed.

Lemma inclusion_step2_ct A (r r' r'': relation A) :
r ⊆ r'' ->
r' ⊆ r'' ->
r ⨾ r' ⊆ r''⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_step2_ct".
ins; rewrite H, H0, <- ct_ct; eauto with hahn.
Qed.

Lemma inclusion_ct_seq_eqv_l A dom (r : relation A) :
(⦗dom⦘ ⨾ r)⁺ ⊆ ⦗dom⦘ ⨾ r⁺.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_ct_seq_eqv_l".
by rewrite ct_begin, seqA, inclusion_seq_eqv_l with (r:=r), <- ct_begin.
Qed.

Lemma inclusion_ct_seq_eqv_r A dom (r : relation A) :
(r ⨾ ⦗dom⦘)⁺ ⊆ r⁺ ⨾ ⦗dom⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.inclusion_ct_seq_eqv_r".
by rewrite ct_end, inclusion_seq_eqv_r at 1; rewrite <- seqA, <- ct_end.
Qed.

Lemma minus_eqv_rel_helper A (R T: relation A) d1 d2:
⦗d1⦘ ⨾ (R \ T) ⨾ ⦗d2⦘ ≡ (⦗d1⦘ ⨾ R ⨾ ⦗d2⦘) \ T.
Proof. hammer_hook "HahnEquational" "HahnEquational.minus_eqv_rel_helper".
red; split; unfold inclusion, eqv_rel, minus_rel, seq; ins; desf; firstorder.
Qed.

Lemma fun_seq_minus_helper A (R S T: relation A)
(FUN: functional R):
R ⨾ (S \ T) ≡ (R ⨾ S) \ (R ⨾ T).
Proof. hammer_hook "HahnEquational" "HahnEquational.fun_seq_minus_helper".
red; unfold minus_rel, seq, inclusion, transp, eqv_rel in *;
splits; ins; desf; firstorder.
intro; desf.
assert (z=z0); try by subst.
eapply FUN; eauto.
Qed.

Lemma inter_irrefl_equiv A (r r' : relation A) :
r ∩ r' ≡ ∅₂ <-> irreflexive (r' ⨾ r⁻¹).
Proof. hammer_hook "HahnEquational" "HahnEquational.inter_irrefl_equiv".
firstorder.
Qed.

Lemma tot_ex X (mo : relation X) dom (TOT: is_total dom mo) a b
(INa: dom a) (INb: dom b)
(NMO: ~ mo a b) (NEQ: a <> b) : mo b a.
Proof. hammer_hook "HahnEquational" "HahnEquational.tot_ex". eapply TOT in NEQ; desf; eauto. Qed.

Lemma seq_minus_transitive A (r r1 r2 : relation A)
(TR : transitive r) :
r1 ⨾ r2 \ r ⊆ (r1 \ r) ⨾  r2 ∪ (r1 ∩ r) ⨾  (r2 \ r).
Proof. hammer_hook "HahnEquational" "HahnEquational.seq_minus_transitive".
autounfold with unfolderDb; ins; desf.
destruct (classic (r x z)); [|eauto].
right; eexists; splits; try edone; intro; eauto.
Qed.

Lemma add_dom_l A (r: relation A) (s s': A -> Prop)
(IN: r ⨾ ⦗s⦘ ⊆ ⦗s'⦘ ⨾ r) :
r ⨾ ⦗s⦘ ≡ ⦗s'⦘ ⨾ r ⨾ ⦗s⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.add_dom_l".
split.
all: autounfold with unfolderDb in *; ins; desf; eauto.
edestruct IN; eauto. desf.
eexists; splits; eauto.
Qed.

Lemma add_dom_r A (r: relation A) (s s': A -> Prop)
(IN: ⦗s'⦘ ⨾ r ⊆ r ⨾ ⦗s⦘) :
⦗s'⦘ ⨾ r ≡ ⦗s'⦘ ⨾ r ⨾ ⦗s⦘.
Proof. hammer_hook "HahnEquational" "HahnEquational.add_dom_r".
split.
all: autounfold with unfolderDb in *; ins; desf; eauto.
edestruct IN; eauto.
Qed.

Tactic Notation "rotate" int_or_var(i) := do i (
rewrite <- ?seqA; (apply irreflexive_seqC || apply acyclic_seqC); rewrite ?seqA).
Tactic Notation "rotate" := rotate 1.
