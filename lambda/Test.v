From Hammer Require Import Hammer.




































Require Import Arith.



Definition test : forall n m : nat, {n <= m} + {n > m}.
Proof. hammer_hook "Test" "Test.test".
simple induction n; simple induction m; simpl in |- *; auto with arith.
intros m' H'; elim (H m'); auto with arith.
Defined.


Definition le_lt : forall n m : nat, n <= m -> {n < m} + {n = m}.
Proof. hammer_hook "Test" "Test.le_lt".
simple induction n; simple induction m; simpl in |- *; auto with arith.
intros m' H1 H2; elim (H m'); auto with arith.
Defined.


Definition compare : forall n m : nat, {n < m} + {n = m} + {n > m}.
Proof. hammer_hook "Test" "Test.compare".
intros n m; elim (test n m); auto with arith.
left; apply le_lt; trivial with arith.
Defined.




