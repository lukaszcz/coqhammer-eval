From Hammer Require Import Hammer.





From hahn Require Import HahnBase.
Require Import List Omega Relations Setoid Morphisms.

Set Implicit Arguments.




Section SetDefs.

Variables A B : Type.
Implicit Type f : A -> B.
Implicit Type s : A -> Prop.
Implicit Type ss : A -> B -> Prop.

Definition set_empty       := fun x : A => False.
Definition set_full        := fun x : A => True.
Definition set_compl s     := fun x => ~ (s x).
Definition set_union s s'  := fun x => s x \/ s' x.
Definition set_inter s s'  := fun x => s x /\ s' x.
Definition set_minus s s'  := fun x => s x /\ ~ (s' x).
Definition set_subset s s' := forall x, s x -> s' x.
Definition set_equiv s s'  := set_subset s s' /\ set_subset s' s.
Definition set_finite s    := exists findom, forall x (IN: s x), In x findom.
Definition set_coinfinite s:= ~ set_finite (set_compl s).
Definition set_collect f s := fun x => exists y, s y /\ f y = x.
Definition set_bunion s ss := fun x => exists y, s y /\ ss y x.
Definition set_disjoint s s':= forall x (IN: s x) (IN': s' x), False.

End SetDefs.

Arguments set_empty {A}.
Arguments set_full {A}.
Arguments set_subset {A}.
Arguments set_equiv {A}.

Notation "P ∪₁ Q" := (set_union P Q) (at level 50, left associativity).
Notation "P ∩₁ Q" := (set_inter P Q) (at level 40, left associativity).
Notation "P \₁ Q" := (set_minus P Q) (at level 46).
Notation "∅"     := (@set_empty _).
Notation "a ⊆₁ b" := (set_subset a b) (at level 60).
Notation "a ≡₁ b" := (set_equiv a b)  (at level 60).
Notation "⋃₁ x ∈ s , a" := (set_bunion s (fun x => a))
(at level 200, x ident, right associativity,
format "'[' ⋃₁ '/ ' x  ∈  s ,  '/ ' a ']'").
Notation "'⋃₁' x , a" := (set_bunion (fun _ => True) (fun x => a))
(at level 200, x ident, right associativity,
format "'[' ⋃₁ '/ ' x ,  '/ ' a ']'").
Notation "'⋃₁' x < n , a" := (set_bunion (fun t => t < n) (fun x => a))
(at level 200, x ident, right associativity,
format "'[' ⋃₁ '/ ' x  <  n ,  '/ ' a ']'").
Notation "'⋃₁' x <= n , a" := (set_bunion (fun t => t <= n) (fun x => a))
(at level 200, x ident, right associativity,
format "'[' ⋃₁ '/ ' x  <=  n ,  '/ ' a ']'").




Hint Unfold set_empty set_full set_compl set_union set_inter : unfolderDb.
Hint Unfold set_minus set_subset set_equiv set_coinfinite set_finite : unfolderDb.
Hint Unfold set_collect set_bunion set_disjoint : unfolderDb.




Section SetProperties.
Local Ltac u :=
repeat autounfold with unfolderDb in *;
ins; try solve [tauto | firstorder | split; ins; tauto].

Variables A B C : Type.
Implicit Type a : A.
Implicit Type f : A -> B.
Implicit Type s : A -> Prop.
Implicit Type ss : A -> B -> Prop.



Lemma set_compl_empty : set_compl ∅ ≡₁ @set_full A.
Proof. hammer_hook "HahnSets" "HahnSets.set_compl_empty". u. Qed.

Lemma set_compl_full : set_compl (@set_full A) ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_compl_full". u. Qed.

Lemma set_compl_compl s : set_compl (set_compl s) ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_compl_compl". u. Qed.

Lemma set_compl_union s s' :
set_compl (s ∪₁ s') ≡₁ set_compl s ∩₁ set_compl s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_compl_union". u. Qed.

Lemma set_compl_inter s s' :
set_compl (s ∩₁ s') ≡₁ set_compl s ∪₁ set_compl s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_compl_inter". u. Qed.

Lemma set_compl_minus s s' :
set_compl (s \₁ s') ≡₁ s' ∪₁ set_compl s.
Proof. hammer_hook "HahnSets" "HahnSets.set_compl_minus". u. Qed.



Lemma set_unionA s s' s'' : (s ∪₁ s') ∪₁ s'' ≡₁ s ∪₁ (s' ∪₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_unionA". u. Qed.

Lemma set_unionC s s' : s ∪₁ s' ≡₁ s' ∪₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_unionC". u. Qed.

Lemma set_unionK s : s ∪₁ s ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_unionK". u. Qed.

Lemma set_union_empty_l s : ∅ ∪₁ s ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_union_empty_l". u. Qed.

Lemma set_union_empty_r s : s ∪₁ ∅ ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_union_empty_r". u. Qed.

Lemma set_union_full_l s : set_full ∪₁ s ≡₁ set_full.
Proof. hammer_hook "HahnSets" "HahnSets.set_union_full_l". u. Qed.

Lemma set_union_full_r s : s ∪₁ set_full ≡₁ set_full.
Proof. hammer_hook "HahnSets" "HahnSets.set_union_full_r". u. Qed.

Lemma set_union_inter_l s s' s'' : (s ∩₁ s') ∪₁ s'' ≡₁ (s ∪₁ s'') ∩₁ (s' ∪₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_union_inter_l". u. Qed.

Lemma set_union_inter_r s s' s'' : s ∪₁ (s' ∩₁ s'') ≡₁ (s ∪₁ s') ∩₁ (s ∪₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_union_inter_r". u. Qed.

Lemma set_union_eq_empty s s' : s ∪₁ s' ≡₁ ∅ <-> s ≡₁ ∅ /\ s' ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_union_eq_empty". u. Qed.



Lemma set_interA s s' s'' : (s ∩₁ s') ∩₁ s'' ≡₁ s ∩₁ (s' ∩₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_interA". u. Qed.

Lemma set_interC s s' : s ∩₁ s' ≡₁ s' ∩₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_interC". u. Qed.

Lemma set_interK s : s ∩₁ s ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_interK". u. Qed.

Lemma set_inter_empty_l s : ∅ ∩₁ s ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_empty_l". u. Qed.

Lemma set_inter_empty_r s : s ∩₁ ∅ ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_empty_r". u. Qed.

Lemma set_inter_full_l s : set_full ∩₁ s ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_full_l". u. Qed.

Lemma set_inter_full_r s : s ∩₁ set_full ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_full_r". u. Qed.

Lemma set_inter_union_l s s' s'' : (s ∪₁ s') ∩₁ s'' ≡₁ (s ∩₁ s'') ∪₁ (s' ∩₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_union_l". u. Qed.

Lemma set_inter_union_r s s' s'' : s ∩₁ (s' ∪₁ s'') ≡₁ (s ∩₁ s') ∪₁ (s ∩₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_union_r". u. Qed.

Lemma set_inter_minus_l s s' s'' : (s \₁ s') ∩₁ s'' ≡₁ (s ∩₁ s'') \₁ s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_minus_l". u. Qed.

Lemma set_inter_minus_r s s' s'' : s ∩₁ (s' \₁ s'') ≡₁ (s ∩₁ s') \₁ s''.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_minus_r". u. Qed.



Lemma set_minusE s s' : s \₁ s' ≡₁ s ∩₁ set_compl s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_minusE". u. Qed.

Lemma set_minusK s : s \₁ s ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_minusK". u. Qed.

Lemma set_minus_inter_l s s' s'' :
(s ∩₁ s') \₁ s'' ≡₁ (s \₁ s'') ∩₁ (s' \₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_minus_inter_l". u. Qed.

Lemma set_minus_inter_r s s' s'' :
s \₁ (s' ∩₁ s'') ≡₁ (s \₁ s') ∪₁ (s \₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_minus_inter_r". u; split; ins; tauto. Qed.

Lemma set_minus_union_l s s' s'' :
(s ∪₁ s') \₁ s'' ≡₁ (s \₁ s'') ∪₁ (s' \₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_minus_union_l". u. Qed.

Lemma set_minus_union_r s s' s'' :
s \₁ (s' ∪₁ s'') ≡₁ (s \₁ s') ∩₁ (s \₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_minus_union_r". u. Qed.

Lemma set_minus_minus_l s s' s'' :
s \₁ s' \₁ s'' ≡₁ s \₁ (s' ∪₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_minus_minus_l". u. Qed.

Lemma set_minus_minus_r s s' s'' :
s \₁ (s' \₁ s'') ≡₁ (s \₁ s') ∪₁ (s ∩₁ s'').
Proof. hammer_hook "HahnSets" "HahnSets.set_minus_minus_r". u. Qed.



Lemma set_subsetE s s' : s ⊆₁ s' <-> s \₁ s' ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_subsetE". u; intuition; apply NNPP; firstorder. Qed.

Lemma set_subset_eq (P : A -> Prop) a (H : P a): eq a ⊆₁ P.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_eq". by intros x H'; subst. Qed.

Lemma set_subset_refl : reflexive _ (@set_subset A).
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_refl". u. Qed.

Lemma set_subset_trans : transitive _ (@set_subset A).
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_trans". u. Qed.

Lemma set_subset_empty_l s : ∅ ⊆₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_empty_l". u. Qed.

Lemma set_subset_empty_r s : s ⊆₁ ∅ <-> s ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_empty_r". u. Qed.

Lemma set_subset_full_l s : set_full ⊆₁ s <-> s ≡₁ set_full.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_full_l". u. Qed.

Lemma set_subset_full_r s : s ⊆₁ set_full.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_full_r". u. Qed.

Lemma set_subset_union_l s s' s'' : s ∪₁ s' ⊆₁ s'' <-> s ⊆₁ s'' /\ s' ⊆₁ s''.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_union_l". u. Qed.

Lemma set_subset_union_r1 s s' : s ⊆₁ s ∪₁ s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_union_r1". u. Qed.

Lemma set_subset_union_r2 s s' : s' ⊆₁ s ∪₁ s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_union_r2". u. Qed.

Lemma set_subset_union_r s s' s'' : s ⊆₁ s' \/ s ⊆₁ s'' -> s ⊆₁ s' ∪₁ s''.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_union_r". u. Qed.

Lemma set_subset_inter_r s s' s'' : s ⊆₁ s' ∩₁ s'' <-> s ⊆₁ s' /\ s ⊆₁ s''.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_inter_r". u. Qed.

Lemma set_subset_compl s s' (S1: s' ⊆₁ s) : set_compl s ⊆₁ set_compl s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_compl". u. Qed.

Lemma set_subset_inter s s' (S1: s ⊆₁ s') t t' (S2: t ⊆₁ t') : s ∩₁ t ⊆₁ s' ∩₁ t'.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_inter". u. Qed.

Lemma set_subset_union s s' (S1: s ⊆₁ s') t t' (S2: t ⊆₁ t') : s ∪₁ t ⊆₁ s' ∪₁ t'.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_union". u. Qed.

Lemma set_subset_minus s s' (S1: s ⊆₁ s') t t' (S2: t' ⊆₁ t) : s \₁ t ⊆₁ s' \₁ t'.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_minus". u. Qed.

Lemma set_subset_bunion_l s ss sb (H: forall x (COND: s x), ss x ⊆₁ sb) : (⋃₁x ∈ s, ss x) ⊆₁ sb.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_bunion_l". u. Qed.

Lemma set_subset_bunion_r s ss sb a (H: s a) (H': sb ⊆₁ ss a) : sb ⊆₁ ⋃₁x ∈ s, ss x.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_bunion_r". u. Qed.

Lemma set_subset_bunion s s' (S: s ⊆₁ s') ss ss' (SS: forall x (COND: s x), ss x ⊆₁ ss' x) :
(⋃₁x ∈ s, ss x) ⊆₁ ⋃₁x ∈ s, ss' x.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_bunion". u. Qed.

Lemma set_subset_bunion_guard s s' (S: s ⊆₁ s') ss ss' (EQ: ss = ss') :
(⋃₁x ∈ s, ss x) ⊆₁ (⋃₁x ∈ s', ss' x).
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_bunion_guard". subst; u. Qed.

Lemma set_subset_collect f s s' (S: s ⊆₁ s') : set_collect f s ⊆₁ set_collect f s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_collect". u. Qed.



Lemma set_equivE s s' : s ≡₁ s' <-> s ⊆₁ s' /\ s' ⊆₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_equivE". u; firstorder. Qed.

Lemma set_equiv_refl : reflexive _ (@set_equiv A).
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_refl". u. Qed.

Lemma set_equiv_symm : symmetric _ (@set_equiv A).
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_symm". u. Qed.

Lemma set_equiv_trans : transitive _ (@set_equiv A).
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_trans". u. Qed.

Lemma set_equiv_compl s s' (S1: s ≡₁ s') : set_compl s ≡₁ set_compl s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_compl". u. Qed.

Lemma set_equiv_inter s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s ∩₁ t ≡₁ s' ∩₁ t'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_inter". u. Qed.

Lemma set_equiv_union s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s ∪₁ t ≡₁ s' ∪₁ t'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_union". u. Qed.

Lemma set_equiv_minus s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s \₁ t ≡₁ s' \₁ t'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_minus". u. Qed.

Lemma set_equiv_bunion s s' (S: s ≡₁ s') ss ss' (SS: forall x (COND: s x), ss x ≡₁ ss' x) :
set_bunion s ss ≡₁ set_bunion s' ss'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_bunion". u. Qed.

Lemma set_equiv_bunion_guard s s' (S: s ≡₁ s') ss ss' (EQ: ss = ss') : set_bunion s ss ≡₁ set_bunion s' ss'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_bunion_guard". subst; u. Qed.

Lemma set_equiv_collect f s s' (S: s ≡₁ s') : set_collect f s ⊆₁ set_collect f s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_collect". u. Qed.

Lemma set_equiv_subset s s' (S1: s ≡₁ s') t t' (S2: t ≡₁ t') : s ⊆₁ t <-> s' ⊆₁ t'.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_subset". u. Qed.

Lemma set_equiv_exp s s' (EQ: s ≡₁ s') : forall x, s x <-> s' x.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_exp". split; apply EQ. Qed.



Lemma set_union_absorb_l s s' (SUB: s ⊆₁ s') : s ∪₁ s' ≡₁ s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_union_absorb_l". u. Qed.

Lemma set_union_absorb_r s s' (SUB: s ⊆₁ s') : s' ∪₁ s ≡₁ s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_union_absorb_r". u. Qed.

Lemma set_inter_absorb_l s s' (SUB: s ⊆₁ s') : s' ∩₁ s ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_absorb_l". u. Qed.

Lemma set_inter_absorb_r s s' (SUB: s ⊆₁ s') : s ∩₁ s' ≡₁ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_inter_absorb_r". u. Qed.

Lemma set_minus_absorb_l s s' (SUB: s ⊆₁ s') : s \₁ s' ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_minus_absorb_l". u. Qed.



Lemma set_subset_single_l a s : eq a ⊆₁ s <-> s a.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_single_l". u; intuition; desf. Qed.

Lemma set_subset_single_r a s :
s ⊆₁ eq a <-> s ≡₁ eq a \/ s ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_single_r".
u; intuition; firstorder.
destruct (classic (exists b, s b)) as [M|M]; desf.
left; split; ins; desf; eauto.
specialize (H _ M); desf.
right; split; ins; eauto.
Qed.

Lemma set_subset_single_single a b :
eq a ⊆₁ eq b <-> a = b.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_single_single". u; intuition; desf; eauto using eq_sym. Qed.

Lemma set_equiv_single_single a b :
eq a ≡₁ eq b <-> a = b.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_single_single". u; intuition; desf; apply H; ins. Qed.

Lemma set_nonemptyE s : ~ s ≡₁ ∅ <-> exists x, s x.
Proof. hammer_hook "HahnSets" "HahnSets.set_nonemptyE".
u; intuition; firstorder.
apply NNPP; intro; apply H0; ins; eauto.
Qed.



Lemma set_bunion_empty ss : set_bunion ∅ ss ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_empty". u. Qed.

Lemma set_bunion_eq a ss : set_bunion (eq a) ss ≡₁ ss a.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_eq". u; splits; ins; desf; eauto. Qed.

Lemma set_bunion_union_l s s' ss :
set_bunion (s ∪₁ s') ss ≡₁ set_bunion s ss ∪₁ set_bunion s' ss.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_union_l". u. Qed.

Lemma set_bunion_union_r s ss ss' :
set_bunion s (fun x => ss x ∪₁ ss' x) ≡₁ set_bunion s ss ∪₁ set_bunion s ss'.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_union_r". u. Qed.

Lemma set_bunion_bunion_l s ss (ss' : B -> C -> Prop) :
(⋃₁x ∈ (⋃₁y ∈ s, ss y), ss' x) ≡₁ ⋃₁y ∈ s, ⋃₁x ∈ ss y, ss' x.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_bunion_l". u. Qed.

Lemma set_bunion_inter_compat_l s sb ss :
set_bunion s (fun x => sb ∩₁ ss x) ≡₁ sb ∩₁ set_bunion s ss.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_inter_compat_l". u; split; ins; desf; eauto 8. Qed.

Lemma set_bunion_inter_compat_r s sb ss :
set_bunion s (fun x => ss x ∩₁ sb) ≡₁ set_bunion s ss ∩₁ sb.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_inter_compat_r". u; split; ins; desf; eauto 8. Qed.

Lemma set_bunion_minus_compat_r s sb ss :
set_bunion s (fun x => ss x \₁ sb) ≡₁ set_bunion s ss \₁ sb.
Proof. hammer_hook "HahnSets" "HahnSets.set_bunion_minus_compat_r". u; split; ins; desf; eauto 8. Qed.



Lemma set_collectE f s : set_collect f s ≡₁ set_bunion s (fun x => eq (f x)).
Proof. hammer_hook "HahnSets" "HahnSets.set_collectE". u. Qed.

Lemma set_collect_empty f : set_collect f ∅ ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_collect_empty". u. Qed.

Lemma set_collect_eq f a : set_collect f (eq a) ≡₁ eq (f a).
Proof. hammer_hook "HahnSets" "HahnSets.set_collect_eq". u; splits; ins; desf; eauto. Qed.

Lemma set_collect_union f s s' :
set_collect f (s ∪₁ s') ≡₁ set_collect f s ∪₁ set_collect f s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_collect_union". u. Qed.

Lemma set_collect_bunion f (s : B -> Prop) (ss : B -> A -> Prop) :
set_collect f (⋃₁x ∈ s, ss x) ≡₁ ⋃₁x ∈ s, set_collect f (ss x).
Proof. hammer_hook "HahnSets" "HahnSets.set_collect_bunion". u. Qed.



Lemma set_finite_empty : set_finite (A:=A) ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_empty". exists nil; ins. Qed.

Lemma set_finite_eq a : set_finite (eq a).
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_eq". exists (a :: nil); ins; desf; eauto. Qed.

Lemma set_finite_le n : set_finite (fun t => t <= n).
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_le". exists (List.seq 0 (S n)); intros; apply in_seq; ins; auto with arith. Qed.

Lemma set_finite_lt n : set_finite (fun t => t < n).
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_lt". exists (List.seq 0 n); intros; apply in_seq; ins; auto with arith. Qed.

Lemma set_finite_union s s' : set_finite (s ∪₁ s') <-> set_finite s /\ set_finite s'.
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_union".
u; split; splits; ins; desf; eauto.
eexists (_ ++ _); ins; desf; eauto using in_or_app.
Qed.

Lemma set_finite_unionI s (F: set_finite s) s' (F': set_finite s') : set_finite (s ∪₁ s').
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_unionI".
u; desf; eauto; eexists (_ ++ _); ins; desf; eauto using in_or_app.
Qed.

Lemma set_finite_bunion s (F: set_finite s) ss :
set_finite (set_bunion s ss) <-> forall a (COND: s a), set_finite (ss a).
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_bunion".
u; split; ins; desf; eauto.
revert s F H; induction findom; ins.
by exists nil; ins; desf; eauto.
specialize (IHfindom (fun x => s x /\ x <> a)); ins.
specialize_full IHfindom; ins; desf; eauto.
by apply F in IN; desf; eauto.
tertium_non_datur (s a) as [X|X].
eapply H in X; desf.
eexists (findom0 ++ findom1); ins; desf.
tertium_non_datur (y = a); desf; eauto 8 using in_or_app.
eexists findom0; ins; desf; apply IHfindom; eexists; splits; eauto; congruence.
Qed.



Lemma set_disjointE s s' : set_disjoint s s' <-> s ∩₁ s' ≡₁ ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjointE". u. Qed.

Lemma set_disjointC s s' : set_disjoint s s' <-> set_disjoint s' s.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjointC". u. Qed.

Lemma set_disjoint_empty_l s : set_disjoint ∅ s.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_empty_l". u. Qed.

Lemma set_disjoint_empty_r s : set_disjoint s ∅.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_empty_r". u. Qed.

Lemma set_disjoint_eq_l a s : set_disjoint (eq a) s <-> ~ s a.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_eq_l". u; split; ins; desf; eauto. Qed.

Lemma set_disjoint_eq_r a s : set_disjoint s (eq a) <-> ~ s a.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_eq_r". u; split; ins; desf; eauto. Qed.

Lemma set_disjoint_eq_eq a b : set_disjoint (eq a) (eq b) <-> a <> b.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_eq_eq". u; split; ins; desf; eauto. Qed.

Lemma set_disjoint_union_l s s' s'' :
set_disjoint (s ∪₁ s') s'' <-> set_disjoint s s'' /\ set_disjoint s' s''.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_union_l". u. Qed.

Lemma set_disjoint_union_r s s' s'' :
set_disjoint s (s' ∪₁ s'') <-> set_disjoint s s' /\ set_disjoint s s''.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_union_r". u. Qed.

Lemma set_disjoint_bunion_l s ss sr :
set_disjoint (set_bunion s ss) sr <-> forall x (IN: s x), set_disjoint (ss x) sr.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_bunion_l". u. Qed.

Lemma set_disjoint_bunion_r s ss sr :
set_disjoint sr (set_bunion s ss) <-> forall x (IN: s x), set_disjoint sr (ss x).
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_bunion_r". u. Qed.

Lemma set_disjoint_subset_l s s' (SUB: s ⊆₁ s') s'' :
set_disjoint s' s'' -> set_disjoint s s''.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_subset_l". u. Qed.

Lemma set_disjoint_subset_r s s' (SUB: s ⊆₁ s') s'' :
set_disjoint s'' s' -> set_disjoint s'' s.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_subset_r". u. Qed.

Lemma set_disjoint_subset s s' (SUB: s ⊆₁ s') sr sr' (SUB': sr ⊆₁ sr') :
set_disjoint s' sr' -> set_disjoint s sr.
Proof. hammer_hook "HahnSets" "HahnSets.set_disjoint_subset". u. Qed.



Lemma set_le n : (fun i => i <= n) ≡₁ (fun i => i < n) ∪₁ (eq n).
Proof. hammer_hook "HahnSets" "HahnSets.set_le".
u; intuition; omega.
Qed.

Lemma set_lt n : (fun i => i < n) ≡₁ (fun i => i <= n) \₁ (eq n).
Proof. hammer_hook "HahnSets" "HahnSets.set_lt".
u; intuition; omega.
Qed.

End SetProperties.


Lemma set_finite_coinfinite_nat (s: nat -> Prop) :
set_finite s -> set_coinfinite s.
Proof. hammer_hook "HahnSets" "HahnSets.set_finite_coinfinite_nat".
assert (LT: forall l x, In x l -> x <= fold_right Init.Nat.add 0 l).
induction l; ins; desf; try apply IHl in H; omega.
repeat autounfold with unfolderDb; red; ins; desf.
tertium_non_datur (s (S (fold_right plus 0 findom + fold_right plus 0 findom0))) as [X|X];
[apply H in X | apply H0 in X]; apply LT in X; omega.
Qed.

Lemma set_coinfinite_fresh (s: nat -> Prop) (COINF: set_coinfinite s) :
exists b, ~ s b /\ set_coinfinite (s ∪₁ eq b).
Proof. hammer_hook "HahnSets" "HahnSets.set_coinfinite_fresh".
repeat autounfold with unfolderDb in *.
tertium_non_datur (forall b, s b).
by destruct COINF; exists nil; ins; desf.
exists n; splits; red; ins; desf.
apply COINF; exists (n :: findom); ins; desf; eauto.
specialize (H0 x); tauto.
Qed.



Add Parametric Relation A : (A -> Prop) (set_subset (A:=A))
reflexivity proved by (set_subset_refl (A:=A))
transitivity proved by (set_subset_trans (A:=A))
as set_subset_rel.

Add Parametric Relation A : (A -> Prop) (set_equiv (A:=A))
reflexivity proved by (set_equiv_refl (A:=A))
symmetry proved by (set_equiv_symm (A:=A))
transitivity proved by (set_equiv_trans (A:=A))
as set_equiv_rel.

Instance set_compl_Proper A : Proper (_ --> _) _ := set_subset_compl (A:=A).
Instance set_union_Proper A : Proper (_ ==> _ ==> _) _ := set_subset_union (A:=A).
Instance set_inter_Proper A : Proper (_ ==> _ ==> _) _ := set_subset_inter (A:=A).
Instance set_minus_Proper A : Proper (_ ++> _ --> _) _ := set_subset_minus (A:=A).
Instance set_bunion_Proper A B : Proper (_ ==> _ ==> _) _ := set_subset_bunion_guard (A:=A) (B:=B).

Instance set_compl_Propere A : Proper (_ ==> _) _ := set_equiv_compl (A:=A).
Instance set_union_Propere A : Proper (_ ==> _ ==> _) _ := set_equiv_union (A:=A).
Instance set_inter_Propere A : Proper (_ ==> _ ==> _) _ := set_equiv_inter (A:=A).
Instance set_minus_Propere A : Proper (_ ==> _ ==> _) _ := set_equiv_minus (A:=A).
Instance set_bunion_Propere A B : Proper (_ ==> _ ==> _) _ := set_equiv_bunion_guard (A:=A) (B:=B).
Instance set_subset_Proper A : Proper (_ ==> _ ==> _) _ := set_equiv_subset (A:=A).

Add Parametric Morphism A : (@set_finite A) with signature
set_subset --> Basics.impl as set_finite_mori.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_Proper". red; autounfold with unfolderDb; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_finite A) with signature
set_equiv ==> iff as set_finite_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_coinfinite A) with signature
set_subset --> Basics.impl as set_coinfinite_mori.
Proof. unfold set_coinfinite; ins; rewrite H; ins. Qed.

Add Parametric Morphism A : (@set_coinfinite A) with signature
set_equiv ==> iff as set_coinfinite_more.
Proof. unfold set_coinfinite; ins; rewrite H; ins. Qed.

Add Parametric Morphism A B : (@set_collect A B) with signature
eq ==> set_subset ==> set_subset as set_collect_mori.
Proof. autounfold with unfolderDb; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@set_collect A B) with signature
eq ==> set_equiv ==> set_equiv as set_collect_more.
Proof. repeat autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_disjoint A) with signature
set_subset --> set_subset --> Basics.impl as set_disjoint_mori.
Proof. red; autounfold with unfolderDb; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_disjoint A) with signature
set_equiv ==> set_equiv ==> iff as set_disjoint_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.



Lemma set_subset_refl2 A (x: A -> Prop) :  x ⊆₁ x.
Proof. hammer_hook "HahnSets" "HahnSets.set_subset_refl2". reflexivity. Qed.

Lemma set_equiv_refl2 A (x: A -> Prop) :  x ≡₁ x.
Proof. hammer_hook "HahnSets" "HahnSets.set_equiv_refl2". reflexivity. Qed.

Hint Immediate set_subset_refl2.
Hint Resolve set_equiv_refl2.

Hint Rewrite set_compl_empty set_compl_full set_compl_compl : hahn.
Hint Rewrite set_compl_union set_compl_inter set_compl_minus : hahn.
Hint Rewrite set_union_empty_l set_union_empty_r set_union_full_l set_union_full_r : hahn.
Hint Rewrite set_inter_empty_l set_inter_empty_r set_inter_full_l set_inter_full_r : hahn.
Hint Rewrite set_bunion_empty set_bunion_eq set_bunion_bunion_l : hahn.
Hint Rewrite set_collect_empty set_collect_eq set_collect_bunion : hahn.
Hint Rewrite set_finite_union : hahn.
Hint Rewrite set_disjoint_eq_eq set_disjoint_eq_l set_disjoint_eq_r : hahn.

Hint Rewrite set_inter_union_l set_inter_union_r set_union_eq_empty : hahn_full.
Hint Rewrite set_minus_union_l set_minus_union_r set_union_eq_empty : hahn_full.
Hint Rewrite set_subset_union_l set_subset_inter_r : hahn_full.
Hint Rewrite set_minusK set_interK set_unionK : hahn_full.
Hint Rewrite set_bunion_inter_compat_l set_bunion_inter_compat_r : hahn_full.
Hint Rewrite set_bunion_minus_compat_r : hahn_full.
Hint Rewrite set_bunion_union_l set_bunion_union_r : hahn_full.
Hint Rewrite set_collect_union : hahn_full.
Hint Rewrite set_disjoint_union_l set_disjoint_union_r : hahn_full.
Hint Rewrite set_disjoint_bunion_l set_disjoint_bunion_r : hahn_full.

Hint Immediate set_subset_empty_l set_subset_full_r : hahn.
Hint Immediate set_finite_empty set_finite_eq set_finite_le set_finite_lt : hahn.
Hint Immediate set_disjoint_empty_l set_disjoint_empty_r : hahn.

Hint Resolve set_subset_union_r : hahn.
Hint Resolve set_finite_unionI set_finite_bunion : hahn.
