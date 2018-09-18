From Hammer Require Import Hammer.











Require Import Permut Setoid.

Set Implicit Arguments.

Section multiset_defs.

Variable A : Type.
Variable eqA : A -> A -> Prop.
Hypothesis eqA_equiv : Equivalence eqA.
Hypothesis Aeq_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

Inductive multiset : Type :=
Bag : (A -> nat) -> multiset.

Definition EmptyBag := Bag (fun a:A => 0).
Definition SingletonBag (a:A) :=
Bag (fun a':A => match Aeq_dec a a' with
| left _ => 1
| right _ => 0
end).

Definition multiplicity (m:multiset) (a:A) : nat := let (f) := m in f a.


Definition meq (m1 m2:multiset) :=
forall a:A, multiplicity m1 a = multiplicity m2 a.

Lemma meq_refl : forall x:multiset, meq x x.
Proof. hammer_hook "Multiset" "Multiset.meq_refl".  
destruct x; unfold meq; reflexivity.
Qed.

Lemma meq_trans : forall x y z:multiset, meq x y -> meq y z -> meq x z.
Proof. hammer_hook "Multiset" "Multiset.meq_trans".  
unfold meq.
destruct x; destruct y; destruct z.
intros; rewrite H; auto.
Qed.

Lemma meq_sym : forall x y:multiset, meq x y -> meq y x.
Proof. hammer_hook "Multiset" "Multiset.meq_sym".  
unfold meq.
destruct x; destruct y; auto.
Qed.


Definition munion (m1 m2:multiset) :=
Bag (fun a:A => multiplicity m1 a + multiplicity m2 a).

Lemma munion_empty_left : forall x:multiset, meq x (munion EmptyBag x).
Proof. hammer_hook "Multiset" "Multiset.munion_empty_left".  
unfold meq; unfold munion; simpl; auto.
Qed.

Lemma munion_empty_right : forall x:multiset, meq x (munion x EmptyBag).
Proof. hammer_hook "Multiset" "Multiset.munion_empty_right".  
unfold meq; unfold munion; simpl; auto.
Qed.


Require Plus.

Lemma munion_comm : forall x y:multiset, meq (munion x y) (munion y x).
Proof. hammer_hook "Multiset" "Multiset.munion_comm".  
unfold meq; unfold multiplicity; unfold munion.
destruct x; destruct y; auto with arith.
Qed.

Lemma munion_ass :
forall x y z:multiset, meq (munion (munion x y) z) (munion x (munion y z)).
Proof. hammer_hook "Multiset" "Multiset.munion_ass".  
unfold meq; unfold munion; unfold multiplicity.
destruct x; destruct y; destruct z; auto with arith.
Qed.

Lemma meq_left :
forall x y z:multiset, meq x y -> meq (munion x z) (munion y z).
Proof. hammer_hook "Multiset" "Multiset.meq_left".  
unfold meq; unfold munion; unfold multiplicity.
destruct x; destruct y; destruct z.
intros; elim H; auto with arith.
Qed.

Lemma meq_right :
forall x y z:multiset, meq x y -> meq (munion z x) (munion z y).
Proof. hammer_hook "Multiset" "Multiset.meq_right".  
unfold meq; unfold munion; unfold multiplicity.
destruct x; destruct y; destruct z.
intros; elim H; auto.
Qed.



Lemma munion_rotate :
forall x y z:multiset, meq (munion x (munion y z)) (munion z (munion x y)).
Proof. hammer_hook "Multiset" "Multiset.munion_rotate".  
intros; apply (op_rotate multiset munion meq).
apply munion_comm.
apply munion_ass.
exact meq_trans.
exact meq_sym.
trivial.
Qed.

Lemma meq_congr :
forall x y z t:multiset, meq x y -> meq z t -> meq (munion x z) (munion y t).
Proof. hammer_hook "Multiset" "Multiset.meq_congr".  
intros; apply (cong_congr multiset munion meq); auto using meq_left, meq_right.
exact meq_trans.
Qed.

Lemma munion_perm_left :
forall x y z:multiset, meq (munion x (munion y z)) (munion y (munion x z)).
Proof. hammer_hook "Multiset" "Multiset.munion_perm_left".  
intros; apply (perm_left multiset munion meq); auto using munion_comm, munion_ass, meq_left, meq_right, meq_sym.
exact meq_trans.
Qed.

Lemma multiset_twist1 :
forall x y z t:multiset,
meq (munion x (munion (munion y z) t)) (munion (munion y (munion x t)) z).
Proof. hammer_hook "Multiset" "Multiset.multiset_twist1".  
intros; apply (twist multiset munion meq); auto using munion_comm, munion_ass, meq_sym, meq_left, meq_right.
exact meq_trans.
Qed.

Lemma multiset_twist2 :
forall x y z t:multiset,
meq (munion x (munion (munion y z) t)) (munion (munion y (munion x z)) t).
Proof. hammer_hook "Multiset" "Multiset.multiset_twist2".  
intros; apply meq_trans with (munion (munion x (munion y z)) t).
apply meq_sym; apply munion_ass.
apply meq_left; apply munion_perm_left.
Qed.



Lemma treesort_twist1 :
forall x y z t u:multiset,
meq u (munion y z) ->
meq (munion x (munion u t)) (munion (munion y (munion x t)) z).
Proof. hammer_hook "Multiset" "Multiset.treesort_twist1".  
intros; apply meq_trans with (munion x (munion (munion y z) t)).
apply meq_right; apply meq_left; trivial.
apply multiset_twist1.
Qed.

Lemma treesort_twist2 :
forall x y z t u:multiset,
meq u (munion y z) ->
meq (munion x (munion u t)) (munion (munion y (munion x z)) t).
Proof. hammer_hook "Multiset" "Multiset.treesort_twist2".  
intros; apply meq_trans with (munion x (munion (munion y z) t)).
apply meq_right; apply meq_left; trivial.
apply multiset_twist2.
Qed.



Lemma meq_singleton : forall a a',
eqA a a' -> meq (SingletonBag a) (SingletonBag a').
Proof. hammer_hook "Multiset" "Multiset.meq_singleton".  
intros; red; simpl; intro a0.
destruct (Aeq_dec a a0) as [Ha|Ha]; rewrite H in Ha;
decide (Aeq_dec a' a0) with Ha; reflexivity.
Qed.



End multiset_defs.

Unset Implicit Arguments.

Hint Unfold meq multiplicity: datatypes.
Hint Resolve munion_empty_right munion_comm munion_ass meq_left meq_right
munion_empty_left: datatypes.
Hint Immediate meq_sym: datatypes.
