From Hammer Require Import Hammer.










Definition decidable (P:Prop) := P \/ ~ P.

Theorem dec_not_not : forall P:Prop, decidable P -> (~ P -> False) -> P.
Proof. hammer_hook "Decidable" "Decidable.dec_not_not".  
unfold decidable; tauto.
Qed.

Theorem dec_True : decidable True.
Proof. hammer_hook "Decidable" "Decidable.dec_True".  
unfold decidable; auto.
Qed.

Theorem dec_False : decidable False.
Proof. hammer_hook "Decidable" "Decidable.dec_False".  
unfold decidable, not; auto.
Qed.

Theorem dec_or :
forall A B:Prop, decidable A -> decidable B -> decidable (A \/ B).
Proof. hammer_hook "Decidable" "Decidable.dec_or".  
unfold decidable; tauto.
Qed.

Theorem dec_and :
forall A B:Prop, decidable A -> decidable B -> decidable (A /\ B).
Proof. hammer_hook "Decidable" "Decidable.dec_and".  
unfold decidable; tauto.
Qed.

Theorem dec_not : forall A:Prop, decidable A -> decidable (~ A).
Proof. hammer_hook "Decidable" "Decidable.dec_not".  
unfold decidable; tauto.
Qed.

Theorem dec_imp :
forall A B:Prop, decidable A -> decidable B -> decidable (A -> B).
Proof. hammer_hook "Decidable" "Decidable.dec_imp".  
unfold decidable; tauto.
Qed.

Theorem dec_iff :
forall A B:Prop, decidable A -> decidable B -> decidable (A<->B).
Proof. hammer_hook "Decidable" "Decidable.dec_iff".  
unfold decidable. tauto.
Qed.

Theorem not_not : forall P:Prop, decidable P -> ~ ~ P -> P.
Proof. hammer_hook "Decidable" "Decidable.not_not".  
unfold decidable; tauto.
Qed.

Theorem not_or : forall A B:Prop, ~ (A \/ B) -> ~ A /\ ~ B.
Proof. hammer_hook "Decidable" "Decidable.not_or".  
tauto.
Qed.

Theorem not_and : forall A B:Prop, decidable A -> ~ (A /\ B) -> ~ A \/ ~ B.
Proof. hammer_hook "Decidable" "Decidable.not_and".  
unfold decidable; tauto.
Qed.

Theorem not_imp : forall A B:Prop, decidable A -> ~ (A -> B) -> A /\ ~ B.
Proof. hammer_hook "Decidable" "Decidable.not_imp".  
unfold decidable; tauto.
Qed.

Theorem imp_simp : forall A B:Prop, decidable A -> (A -> B) -> ~ A \/ B.
Proof. hammer_hook "Decidable" "Decidable.imp_simp".  
unfold decidable; tauto.
Qed.

Theorem not_iff :
forall A B:Prop, decidable A -> decidable B ->
~ (A <-> B) -> (A /\ ~ B) \/ (~ A /\ B).
Proof. hammer_hook "Decidable" "Decidable.not_iff".  
unfold decidable; tauto.
Qed.





Theorem not_true_iff : (True -> False) <-> False.
Proof. hammer_hook "Decidable" "Decidable.not_true_iff".  
tauto.
Qed.

Theorem not_false_iff : (False -> False) <-> True.
Proof. hammer_hook "Decidable" "Decidable.not_false_iff".  
tauto.
Qed.

Theorem not_not_iff : forall A:Prop, decidable A ->
(((A -> False) -> False) <-> A).
Proof. hammer_hook "Decidable" "Decidable.not_not_iff".  
unfold decidable; tauto.
Qed.

Theorem contrapositive : forall A B:Prop, decidable A ->
(((A -> False) -> (B -> False)) <-> (B -> A)).
Proof. hammer_hook "Decidable" "Decidable.contrapositive".  
unfold decidable; tauto.
Qed.

Lemma or_not_l_iff_1 : forall A B: Prop, decidable A ->
((A -> False) \/ B <-> (A -> B)).
Proof. hammer_hook "Decidable" "Decidable.or_not_l_iff_1".  
unfold decidable. tauto.
Qed.

Lemma or_not_l_iff_2 : forall A B: Prop, decidable B ->
((A -> False) \/ B <-> (A -> B)).
Proof. hammer_hook "Decidable" "Decidable.or_not_l_iff_2".  
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_1 : forall A B: Prop, decidable A ->
(A \/ (B -> False) <-> (B -> A)).
Proof. hammer_hook "Decidable" "Decidable.or_not_r_iff_1".  
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_2 : forall A B: Prop, decidable B ->
(A \/ (B -> False) <-> (B -> A)).
Proof. hammer_hook "Decidable" "Decidable.or_not_r_iff_2".  
unfold decidable. tauto.
Qed.

Lemma imp_not_l : forall A B: Prop, decidable A ->
(((A -> False) -> B) <-> (A \/ B)).
Proof. hammer_hook "Decidable" "Decidable.imp_not_l".  
unfold decidable. tauto.
Qed.




Theorem not_or_iff : forall A B:Prop,
(A \/ B -> False) <-> (A -> False) /\ (B -> False).
Proof. hammer_hook "Decidable" "Decidable.not_or_iff".  
tauto.
Qed.

Lemma not_and_iff : forall A B:Prop,
(A /\ B -> False) <-> (A -> B -> False).
Proof. hammer_hook "Decidable" "Decidable.not_and_iff".  
tauto.
Qed.

Lemma not_imp_iff : forall A B:Prop, decidable A ->
(((A -> B) -> False) <-> A /\ (B -> False)).
Proof. hammer_hook "Decidable" "Decidable.not_imp_iff".  
unfold decidable. tauto.
Qed.

Lemma not_imp_rev_iff : forall A B : Prop, decidable A ->
(((A -> B) -> False) <-> (B -> False) /\ A).
Proof. hammer_hook "Decidable" "Decidable.not_imp_rev_iff".  
unfold decidable. tauto.
Qed.



Theorem dec_functional_relation :
forall (X Y : Type) (A:X->Y->Prop), (forall y y' : Y, decidable (y=y')) ->
(forall x, exists! y, A x y) -> forall x y, decidable (A x y).
Proof. hammer_hook "Decidable" "Decidable.dec_functional_relation".  
intros X Y A Hdec H x y.
destruct (H x) as (y',(Hex,Huniq)).
destruct (Hdec y y') as [->|Hnot]; firstorder.
Qed.



Hint Resolve dec_True dec_False dec_or dec_and dec_imp dec_not dec_iff
: decidable_prop.



Tactic Notation "solve_decidable" "using" ident(db) :=
match goal with
| |- decidable _ =>
solve [ auto 100 with decidable_prop db ]
end.

Tactic Notation "solve_decidable" :=
solve_decidable using core.
