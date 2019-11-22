From Hammer Require Import Hammer.





Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.






Definition relation (X: Type) := X -> X -> Prop.





Print le.

Check le : nat -> nat -> Prop.
Check le : relation nat.












Definition partial_function {X: Type} (R: relation X) :=
forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.



Print next_nat.

Check next_nat : relation nat.

Theorem next_nat_partial_function :
partial_function next_nat.
Proof. hammer_hook "Rel" "Rel.next_nat_partial_function".
unfold partial_function.
intros x y1 y2 H1 H2.
inversion H1. inversion H2.
reflexivity.  Qed.



Theorem le_not_a_partial_function :
~ (partial_function le).
Proof. hammer_hook "Rel" "Rel.le_not_a_partial_function".
unfold not. unfold partial_function. intros Hc.
assert (0 = 1) as Nonsense. {
apply Hc with (x := 0).
- apply le_n.
- apply le_S. apply le_n. }
discriminate Nonsense.   Qed.














Definition reflexive {X: Type} (R: relation X) :=
forall a : X, R a a.

Theorem le_reflexive :
reflexive le.
Proof. hammer_hook "Rel" "Rel.le_reflexive".
unfold reflexive. intros n. apply le_n.  Qed.






Definition transitive {X: Type} (R: relation X) :=
forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
transitive le.
Proof. hammer_hook "Rel" "Rel.le_trans".
intros n m o Hnm Hmo.
induction Hmo.
-  apply Hnm.
-  apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
transitive lt.
Proof. hammer_hook "Rel" "Rel.lt_trans".
unfold lt. unfold transitive.
intros n m o Hnm Hmo.
apply le_S in Hnm.
apply le_trans with (a := (S n)) (b := (S m)) (c := o).
apply Hnm.
apply Hmo. Qed.



Theorem lt_trans' :
transitive lt.
Proof. hammer_hook "Rel" "Rel.lt_trans'".

unfold lt. unfold transitive.
intros n m o Hnm Hmo.
induction Hmo as [| m' Hm'o].
Admitted.




Theorem lt_trans'' :
transitive lt.
Proof. hammer_hook "Rel" "Rel.lt_trans''".
unfold lt. unfold transitive.
intros n m o Hnm Hmo.
induction o as [| o'].
Admitted.




Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof. hammer_hook "Rel" "Rel.le_Sn_le".
intros n m H. apply le_trans with (S n).
- apply le_S. apply le_n.
- apply H.
Qed.


Theorem le_S_n : forall n m,
(S n <= S m) -> (n <= m).
Proof. hammer_hook "Rel" "Rel.le_S_n".
Admitted.






Theorem le_Sn_n : forall n,
~ (S n <= n).
Proof. hammer_hook "Rel" "Rel.le_Sn_n".
Admitted.









Definition symmetric {X: Type} (R: relation X) :=
forall a b : X, (R a b) -> (R b a).


Theorem le_not_symmetric :
~ (symmetric le).
Proof. hammer_hook "Rel" "Rel.le_not_symmetric".
Admitted.




Definition antisymmetric {X: Type} (R: relation X) :=
forall a b : X, (R a b) -> (R b a) -> a = b.


Theorem le_antisymmetric :
antisymmetric le.
Proof. hammer_hook "Rel" "Rel.le_antisymmetric".
Admitted.



Theorem le_step : forall n m p,
n < m ->
m <= S p ->
n <= p.
Proof. hammer_hook "Rel" "Rel.le_step".
Admitted.







Definition equivalence {X:Type} (R: relation X) :=
(reflexive R) /\ (symmetric R) /\ (transitive R).






Definition order {X:Type} (R: relation X) :=
(reflexive R) /\ (antisymmetric R) /\ (transitive R).



Definition preorder {X:Type} (R: relation X) :=
(reflexive R) /\ (transitive R).

Theorem le_order :
order le.
Proof. hammer_hook "Rel" "Rel.le_order".
unfold order. split.
-  apply le_reflexive.
- split.
+  apply le_antisymmetric.
+  apply le_trans.  Qed.






Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
| rt_step x y (H : R x y) : clos_refl_trans R x y
| rt_refl x : clos_refl_trans R x x
| rt_trans x y z
(Hxy : clos_refl_trans R x y)
(Hyz : clos_refl_trans R y z) :
clos_refl_trans R x z.



Theorem next_nat_closure_is_le : forall n m,
(n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof. hammer_hook "Rel" "Rel.next_nat_closure_is_le".
intros n m. split.
-
intro H. induction H.
+  apply rt_refl.
+
apply rt_trans with m. apply IHle. apply rt_step.
apply nn.
-
intro H. induction H.
+  inversion H. apply le_S. apply le_n.
+  apply le_n.
+
apply le_trans with y.
apply IHclos_refl_trans1.
apply IHclos_refl_trans2. Qed.



Inductive clos_refl_trans_1n {A : Type}
(R : relation A) (x : A)
: A -> Prop :=
| rt1n_refl : clos_refl_trans_1n R x x
| rt1n_trans (y z : A)
(Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
clos_refl_trans_1n R x z.



Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
R x y -> clos_refl_trans_1n R x y.
Proof. hammer_hook "Rel" "Rel.rsc_R".
intros X R x y H.
apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.


Lemma rsc_trans :
forall (X:Type) (R: relation X) (x y z : X),
clos_refl_trans_1n R x y  ->
clos_refl_trans_1n R y z ->
clos_refl_trans_1n R x z.
Proof. hammer_hook "Rel" "Rel.rsc_trans".
Admitted.





Theorem rtc_rsc_coincide :
forall (X:Type) (R: relation X) (x y : X),
clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof. hammer_hook "Rel" "Rel.rtc_rsc_coincide".
Admitted.



