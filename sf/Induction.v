From Hammer Require Import Hammer.





From LF Require Export Basics.








Theorem plus_n_O_firsttry : forall n:nat,
n = n + 0.



Proof. hammer_hook "Induction" "Induction.plus_n_O_firsttry".
intros n.
simpl.
Abort.



Theorem plus_n_O_secondtry : forall n:nat,
n = n + 0.
Proof. hammer_hook "Induction" "Induction.plus_n_O_secondtry".
intros n. destruct n as [| n'] eqn:E.
-
reflexivity.
-
simpl.
Abort.





Theorem plus_n_O : forall n:nat, n = n + 0.
Proof. hammer_hook "Induction" "Induction.plus_n_O".
intros n. induction n as [| n' IHn'].
-     reflexivity.
-  simpl. rewrite <- IHn'. reflexivity.  Qed.



Theorem minus_diag : forall n,
minus n n = 0.
Proof. hammer_hook "Induction" "Induction.minus_diag".

intros n. induction n as [| n' IHn'].
-
simpl. reflexivity.
-
simpl. rewrite -> IHn'. reflexivity.  Qed.





Theorem mult_0_r : forall n:nat,
n * 0 = 0.
Proof. hammer_hook "Induction" "Induction.mult_0_r".
Admitted.

Theorem plus_n_Sm : forall n m : nat,
S (n + m) = n + (S m).
Proof. hammer_hook "Induction" "Induction.plus_n_Sm".
Admitted.

Theorem plus_comm : forall n m : nat,
n + m = m + n.
Proof. hammer_hook "Induction" "Induction.plus_comm".
Admitted.

Theorem plus_assoc : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof. hammer_hook "Induction" "Induction.plus_assoc".
Admitted.




Fixpoint double (n:nat) :=
match n with
| O => O
| S n' => S (S (double n'))
end.



Lemma double_plus : forall n, double n = n + n .
Proof. hammer_hook "Induction" "Induction.double_plus".
Admitted.




Theorem evenb_S : forall n : nat,
evenb (S n) = negb (evenb n).
Proof. hammer_hook "Induction" "Induction.evenb_S".
Admitted.





Definition manual_grade_for_destruct_induction : option (nat*string) := None.







Theorem mult_0_plus' : forall n m : nat,
(0 + n) * m = n * m.
Proof. hammer_hook "Induction" "Induction.mult_0_plus'".
intros n m.
assert (H: 0 + n = n). { reflexivity. }
rewrite -> H.
reflexivity.  Qed.







Theorem plus_rearrange_firsttry : forall n m p q : nat,
(n + m) + (p + q) = (m + n) + (p + q).
Proof. hammer_hook "Induction" "Induction.plus_rearrange_firsttry".
intros n m p q.

rewrite -> plus_comm.

Abort.



Theorem plus_rearrange : forall n m p q : nat,
(n + m) + (p + q) = (m + n) + (p + q).
Proof. hammer_hook "Induction" "Induction.plus_rearrange".
intros n m p q.
assert (H: n + m = m + n).
{ rewrite -> plus_comm. reflexivity. }
rewrite -> H. reflexivity.  Qed.










Theorem plus_assoc' : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof. hammer_hook "Induction" "Induction.plus_assoc'". intros n m p. induction n as [| n' IHn']. reflexivity.
simpl. rewrite -> IHn'. reflexivity.  Qed.



Theorem plus_assoc'' : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof. hammer_hook "Induction" "Induction.plus_assoc''".
intros n m p. induction n as [| n' IHn'].
-
reflexivity.
-
simpl. rewrite -> IHn'. reflexivity.   Qed.










Definition manual_grade_for_plus_comm_informal : option (nat*string) := None.









Theorem plus_swap : forall n m p : nat,
n + (m + p) = m + (n + p).
Proof. hammer_hook "Induction" "Induction.plus_swap".
Admitted.



Theorem mult_comm : forall m n : nat,
m * n = n * m.
Proof. hammer_hook "Induction" "Induction.mult_comm".
Admitted.




Check leb.

Theorem leb_refl : forall n:nat,
true = (n <=? n).
Proof. hammer_hook "Induction" "Induction.leb_refl".
Admitted.

Theorem zero_nbeq_S : forall n:nat,
0 =? (S n) = false.
Proof. hammer_hook "Induction" "Induction.zero_nbeq_S".
Admitted.

Theorem andb_false_r : forall b : bool,
andb b false = false.
Proof. hammer_hook "Induction" "Induction.andb_false_r".
Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
n <=? m = true -> (p + n) <=? (p + m) = true.
Proof. hammer_hook "Induction" "Induction.plus_ble_compat_l".
Admitted.

Theorem S_nbeq_0 : forall n:nat,
(S n) =? 0 = false.
Proof. hammer_hook "Induction" "Induction.S_nbeq_0".
Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof. hammer_hook "Induction" "Induction.mult_1_l".
Admitted.

Theorem all3_spec : forall b c : bool,
orb
(andb b c)
(orb (negb b)
(negb c))
= true.
Proof. hammer_hook "Induction" "Induction.all3_spec".
Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
(n + m) * p = (n * p) + (m * p).
Proof. hammer_hook "Induction" "Induction.mult_plus_distr_r".
Admitted.

Theorem mult_assoc : forall n m p : nat,
n * (m * p) = (n * m) * p.
Proof. hammer_hook "Induction" "Induction.mult_assoc".
Admitted.




Theorem eqb_refl : forall n : nat,
true = (n =? n).
Proof. hammer_hook "Induction" "Induction.eqb_refl".
Admitted.




Theorem plus_swap' : forall n m p : nat,
n + (m + p) = m + (n + p).
Proof. hammer_hook "Induction" "Induction.plus_swap'".
Admitted.







Definition manual_grade_for_binary_commute : option (nat*string) := None.




Fixpoint nat_to_bin (n:nat) : bin
. Admitted.



Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof. hammer_hook "Induction" "Induction.nat_bin_nat".
Admitted.


Definition manual_grade_for_binary_inverse_a : option (nat*string) := None.






Definition manual_grade_for_binary_inverse_b : option (nat*string) := None.






Definition manual_grade_for_binary_inverse_c : option (nat*string) := None.




