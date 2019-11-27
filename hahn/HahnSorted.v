From Hammer Require Import Hammer.





From hahn Require Import HahnBase HahnSets HahnList HahnRelationsBasic HahnEquational.
Require Export Sorted.

Set Implicit Arguments.

Lemma StronglySorted_cons_iff A (r : relation A) (a : A) (l : list A) :
StronglySorted r (a :: l) <-> StronglySorted r l /\ Forall (r a) l.
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_cons_iff".
split; ins; desf; auto using SSorted_cons, StronglySorted_inv.
Qed.

Lemma StronglySorted_app_iff A (r: relation A) l1 l2 :
StronglySorted r (l1 ++ l2) <->
StronglySorted r l1 /\ StronglySorted r l2 /\
(forall x1 (IN1: In x1 l1) x2 (IN2: In x2 l2), r x1 x2).
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_app_iff".
induction l1; ins; [by intuition; vauto|].
rewrite !StronglySorted_cons_iff, IHl1, Forall_app.
clear; intuition; desf; eauto.
all: rewrite Forall_forall in *; eauto.
Qed.

Lemma StronglySorted_app A (r: relation A) l1 l2
(S1: StronglySorted r l1) (S2: StronglySorted r l2)
(L: forall x1 (IN1: In x1 l1) x2 (IN2: In x2 l2), r x1 x2):
StronglySorted r (l1 ++ l2).
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_app".
by apply StronglySorted_app_iff.
Qed.

Lemma StronglySorted_app_l A r (l l': list A):
StronglySorted r (l ++ l') -> StronglySorted r l.
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_app_l".
rewrite StronglySorted_app_iff; tauto.
Qed.

Lemma StronglySorted_app_r A r (l l': list A):
StronglySorted r (l ++ l') -> StronglySorted r l'.
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_app_r".
rewrite StronglySorted_app_iff; tauto.
Qed.

Lemma StronglySorted_filter A r f (l : list A):
StronglySorted r l -> StronglySorted r (filter f l).
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_filter".
induction l; ins; eauto; desf; rewrite StronglySorted_cons_iff in *; desf.
all: splits; desf; eauto using Forall_filter.
Qed.

Lemma StronglySorted_filterP A r f (l : list A):
StronglySorted r l -> StronglySorted r (filterP f l).
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_filterP".
induction l; ins; eauto; desf; rewrite StronglySorted_cons_iff in *; desf.
all: splits; desf; eauto using Forall_filterP.
Qed.

Lemma NoDup_StronglySorted A (r: relation A) (IRR: irreflexive r)
l (SS: StronglySorted r l):
NoDup l.
Proof. hammer_hook "HahnSorted" "HahnSorted.NoDup_StronglySorted".
induction l; ins.
apply StronglySorted_inv in SS; desc.
rewrite Forall_forall in *.
constructor; eauto.
Qed.

Hint Resolve NoDup_StronglySorted : hahn.

Lemma sorted_perm_eq : forall A (cmp: A -> A -> Prop)
(TRANS: transitive cmp)
(ANTIS: antisymmetric cmp)
l l' (P: Permutation l l')
(S : StronglySorted cmp l) (S' : StronglySorted cmp l'), l = l'.
Proof. hammer_hook "HahnSorted" "HahnSorted.sorted_perm_eq".
induction l; ins.
by apply Permutation_nil in P; desf.
assert (X: In a l') by eauto using Permutation_in, Permutation_sym, in_eq.
apply In_split2 in X; desf; apply Permutation_cons_app_inv in P.
destruct l1; ins; [by inv S; inv S'; eauto using f_equal|].
assert (X: In a0 l) by eauto using Permutation_in, Permutation_sym, in_eq.
inv S; inv S'; rewrite Forall_forall in *; ins.
destruct X0; left; apply ANTIS; eauto with hahn.
Qed.

Lemma StronglySorted_eq A (r: relation A) (ORD: strict_partial_order r) l l'
(SS: StronglySorted r l) (SS': StronglySorted r l')
(EQ: forall x, In x l <-> In x l'): l = l'.
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_eq".
red in ORD; desc.
eapply sorted_perm_eq; eauto using NoDup_Permutation with hahn.
Qed.

Lemma StronglySorted_restr A cond (r: relation A) l:
StronglySorted (restr_rel cond r) l -> StronglySorted r l.
Proof. hammer_hook "HahnSorted" "HahnSorted.StronglySorted_restr".
induction l; ins; vauto.
rewrite StronglySorted_cons_iff, ForallE in *.
firstorder.
Qed.
