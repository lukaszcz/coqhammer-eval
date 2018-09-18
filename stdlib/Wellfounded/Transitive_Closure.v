From Hammer Require Import Hammer.











Require Import Relation_Definitions.
Require Import Relation_Operators.

Section Wf_Transitive_Closure.
Variable A : Type.
Variable R : relation A.

Notation trans_clos := (clos_trans A R).

Lemma incl_clos_trans : inclusion A R trans_clos.
red; auto with sets.
Qed.

Lemma Acc_clos_trans : forall x:A, Acc R x -> Acc trans_clos x.
induction 1 as [x0 _ H1].
apply Acc_intro.
intros y H2.
induction H2; auto with sets.
apply Acc_inv with y; auto with sets.
Defined.

Hint Resolve Acc_clos_trans.

Lemma Acc_inv_trans : forall x y:A, trans_clos y x -> Acc R x -> Acc R y.
Proof. hammer_hook "Transitive_Closure" "Transitive_Closure.Acc_inv_trans".  
induction 1 as [| x y]; auto with sets.
intro; apply Acc_inv with y; assumption.
Qed.

Theorem wf_clos_trans : well_founded R -> well_founded trans_clos.
Proof. hammer_hook "Transitive_Closure" "Transitive_Closure.wf_clos_trans".  
unfold well_founded; auto with sets.
Defined.

End Wf_Transitive_Closure.
