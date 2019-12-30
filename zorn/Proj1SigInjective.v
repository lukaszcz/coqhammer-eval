From Hammer Require Import Hammer.

Require Import ProofIrrelevance.


Lemma subset_eq_compatT: forall (U:Type) (P:U->Prop) (x y:U)
(p:P x) (q:P y), x = y -> exist P x p = exist P y q.
Proof. hammer_hook "Proj1SigInjective" "Proj1SigInjective.subset_eq_compatT".
intros.
destruct H.
f_equal.
apply proof_irrelevance.
Qed.

Lemma proj1_sig_injective: forall {A:Type} (P:A->Prop)
(a1 a2:{x:A | P x}), proj1_sig a1 = proj1_sig a2 -> a1 = a2.
Proof. hammer_hook "Proj1SigInjective" "Proj1SigInjective.proj1_sig_injective".
intros.
destruct a1.
destruct a2.
simpl in H.
apply subset_eq_compatT; trivial.
Qed.
