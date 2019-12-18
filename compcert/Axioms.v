From Hammer Require Import Hammer.


















Require ClassicalFacts.
Require FunctionalExtensionality.





Lemma functional_extensionality_dep:
forall {A: Type} {B : A -> Type} (f g : forall x : A, B x),
(forall x, f x = g x) -> f = g.
Proof. hammer_hook "Axioms" "Axioms.functional_extensionality_dep". exact (@FunctionalExtensionality.functional_extensionality_dep). Qed.



Lemma functional_extensionality:
forall {A B: Type} (f g : A -> B), (forall x, f x = g x) -> f = g.
Proof. hammer_hook "Axioms" "Axioms.functional_extensionality". exact (@FunctionalExtensionality.functional_extensionality). Qed.



Lemma extensionality:
forall {A B: Type} (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. hammer_hook "Axioms" "Axioms.extensionality". exact (@functional_extensionality). Qed.





Axiom proof_irr: ClassicalFacts.proof_irrelevance.

Arguments proof_irr [A].
