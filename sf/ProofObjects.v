From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.









Print even.








Check ev_SS.






Theorem ev_4 : even 4.
Proof. hammer_hook "ProofObjects" "ProofObjects.ev_4".
apply ev_SS. apply ev_SS. apply ev_0. Qed.



Print ev_4.




Check (ev_SS 2 (ev_SS 0 ev_0)).






Theorem ev_4': even 4.
Proof. hammer_hook "ProofObjects" "ProofObjects.ev_4'".
apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.






Theorem ev_4'' : even 4.
Proof. hammer_hook "ProofObjects" "ProofObjects.ev_4''".
Show Proof.
apply ev_SS.
Show Proof.
apply ev_SS.
Show Proof.
apply ev_0.
Show Proof.
Qed.





Definition ev_4''' : even 4 :=
ev_SS 2 (ev_SS 0 ev_0).



Print ev_4.

Print ev_4'.

Print ev_4''.

Print ev_4'''.




Theorem ev_8 : even 8.
Proof. hammer_hook "ProofObjects" "ProofObjects.ev_8".
Admitted.

Definition ev_8' : even 8
. Admitted.









Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof. hammer_hook "ProofObjects" "ProofObjects.ev_plus4".
intros n H. simpl.
apply ev_SS.
apply ev_SS.
apply H.
Qed.



Definition ev_plus4' : forall n, even n -> even (4 + n) :=
fun (n : nat) => fun (H : even n) =>
ev_SS (S (S n)) (ev_SS n H).



Definition ev_plus4'' (n : nat) (H : even n)
: even (4 + n) :=
ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.








Definition ev_plus2 : Prop :=
forall n, forall (E : even n), even (n + 2).



Definition ev_plus2' : Prop :=
forall n, forall (_ : even n), even (n + 2).



Definition ev_plus2'' : Prop :=
forall n, even n -> even (n + 2).








Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.


Compute add1 2.









Module Props.






Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.



Print prod.




Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof. hammer_hook "ProofObjects" "ProofObjects.Props.and_comm".
intros P Q. split.
- intros [HP HQ]. split.
+ apply HQ.
+ apply HP.
- intros [HP HQ]. split.
+ apply HQ.
+ apply HP.
Qed.



Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
match H with
| conj HP HQ => conj HQ HP
end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
conj (and_comm'_aux P Q) (and_comm'_aux Q P).



Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
. Admitted.







Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.





Definition or_comm : forall P Q, P \/ Q -> Q \/ P
. Admitted.







Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.





Check ex (fun n => even n).




Definition some_nat_is_even : exists n, even n :=
ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).



Definition ex_ev_Sn : ex (fun n => even (S n))
. Admitted.







Inductive True : Prop :=
| I : True.





Inductive False : Prop := .



End Props.






Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
(at level 70, no associativity)
: type_scope.





Lemma four: 2 + 2 == 1 + 3.
Proof. hammer_hook "ProofObjects" "ProofObjects.MyEquality.four".
apply eq_refl.
Qed.



Definition four' : 2 + 2 == 1 + 3 :=
eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
fun (X:Type) (x:X) => eq_refl [x].



Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
x == y -> forall P:X->Prop, P x -> P y.
Proof. hammer_hook "ProofObjects" "ProofObjects.MyEquality.equality__leibniz_equality".
Admitted.




Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
(forall P:X->Prop, P x -> P y) -> x == y.
Proof. hammer_hook "ProofObjects" "ProofObjects.MyEquality.leibniz_equality__equality".
Admitted.



End MyEquality.














