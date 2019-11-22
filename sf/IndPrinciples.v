From Hammer Require Import Hammer.





Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.






Check nat_ind.




Theorem mult_0_r' : forall n:nat,
n * 0 = 0.
Proof. hammer_hook "IndPrinciples" "IndPrinciples.mult_0_r'".
apply nat_ind.
-  reflexivity.
-  simpl. intros n' IHn'. rewrite -> IHn'.
reflexivity.  Qed.





Theorem plus_one_r' : forall n:nat,
n + 1 = S n.
Proof. hammer_hook "IndPrinciples" "IndPrinciples.plus_one_r'".
Admitted.




Inductive yesno : Type :=
| yes
| no.

Check yesno_ind.




Inductive rgb : Type :=
| red
| green
| blue.
Check rgb_ind.




Inductive natlist : Type :=
| nnil
| ncons (n : nat) (l : natlist).

Check natlist_ind.




Inductive natlist1 : Type :=
| nnil1
| nsnoc1 (l : natlist1) (n : nat).







Inductive byntree : Type :=
| bempty
| bleaf (yn : yesno)
| nbranch (yn : yesno) (t1 t2 : byntree).




Inductive ExSet : Type :=

.









Inductive tree (X:Type) : Type :=
| leaf (x : X)
| node (t1 t2 : tree X).
Check tree_ind.










Inductive foo' (X:Type) : Type :=
| C1 (l : list X) (f : foo' X)
| C2.










Definition P_m0r (n:nat) : Prop :=
n * 0 = 0.



Definition P_m0r' : nat->Prop :=
fun n => n * 0 = 0.



Theorem mult_0_r'' : forall n:nat,
P_m0r n.
Proof. hammer_hook "IndPrinciples" "IndPrinciples.mult_0_r''".
apply nat_ind.
-  reflexivity.
-

intros n IHn.
unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.








Theorem plus_assoc' : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof. hammer_hook "IndPrinciples" "IndPrinciples.plus_assoc'".

intros n m p.

induction n as [| n'].
-  reflexivity.
-

simpl. rewrite -> IHn'. reflexivity.  Qed.



Theorem plus_comm' : forall n m : nat,
n + m = m + n.
Proof. hammer_hook "IndPrinciples" "IndPrinciples.plus_comm'".
induction n as [| n'].
-  intros m. rewrite <- plus_n_O. reflexivity.
-  intros m. simpl. rewrite -> IHn'.
rewrite <- plus_n_Sm. reflexivity.  Qed.



Theorem plus_comm'' : forall n m : nat,
n + m = m + n.
Proof. hammer_hook "IndPrinciples" "IndPrinciples.plus_comm''".

induction m as [| m'].
-  simpl. rewrite <- plus_n_O. reflexivity.
-  simpl. rewrite <- IHm'.
rewrite <- plus_n_Sm. reflexivity.  Qed.










Check even_ind.







Theorem ev_ev' : forall n, even n -> even' n.
Proof. hammer_hook "IndPrinciples" "IndPrinciples.ev_ev'".
apply even_ind.
-
apply even'_0.
-
intros m Hm IH.
apply (even'_sum 2 m).
+ apply even'_2.
+ apply IH.
Qed.







Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).



Check le_ind.


















