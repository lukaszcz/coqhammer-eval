From Hammer Require Import Hammer.





Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.






Theorem silly1 : forall (n m o p : nat),
n = m  ->
[n;o] = [n;p] ->
[n;o] = [m;p].
Proof. hammer_hook "Tactics" "Tactics.silly1".
intros n m o p eq1 eq2.
rewrite <- eq1.



apply eq2.  Qed.



Theorem silly2 : forall (n m o p : nat),
n = m  ->
(forall (q r : nat), q = r -> [q;o] = [r;p]) ->
[n;o] = [m;p].
Proof. hammer_hook "Tactics" "Tactics.silly2".
intros n m o p eq1 eq2.
apply eq2. apply eq1.  Qed.



Theorem silly2a : forall (n m : nat),
(n,n) = (m,m)  ->
(forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
[n] = [m].
Proof. hammer_hook "Tactics" "Tactics.silly2a".
intros n m eq1 eq2.
apply eq2. apply eq1.  Qed.



Theorem silly_ex :
(forall n, evenb n = true -> oddb (S n) = true) ->
oddb 3 = true ->
evenb 4 = true.
Proof. hammer_hook "Tactics" "Tactics.silly_ex".
Admitted.




Theorem silly3_firsttry : forall (n : nat),
true = (n =? 5)  ->
(S (S n)) =? 7 = true.
Proof. hammer_hook "Tactics" "Tactics.silly3_firsttry".
intros n H.



symmetry.
simpl.
apply H.  Qed.



Theorem rev_exercise1 : forall (l l' : list nat),
l = rev l' ->
l' = rev l.
Proof. hammer_hook "Tactics" "Tactics.rev_exercise1".
Admitted.











Example trans_eq_example : forall (a b c d e f : nat),
[a;b] = [c;d] ->
[c;d] = [e;f] ->
[a;b] = [e;f].
Proof. hammer_hook "Tactics" "Tactics.trans_eq_example".
intros a b c d e f eq1 eq2.
rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.



Theorem trans_eq : forall (X:Type) (n m o : X),
n = m -> m = o -> n = o.
Proof. hammer_hook "Tactics" "Tactics.trans_eq".
intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
reflexivity.  Qed.



Example trans_eq_example' : forall (a b c d e f : nat),
[a;b] = [c;d] ->
[c;d] = [e;f] ->
[a;b] = [e;f].
Proof. hammer_hook "Tactics" "Tactics.trans_eq_example'".
intros a b c d e f eq1 eq2.



apply trans_eq with (m:=[c;d]).
apply eq1. apply eq2.   Qed.




Example trans_eq_exercise : forall (n m o p : nat),
m = (minustwo o) ->
(n + p) = m ->
(n + p) = (minustwo o).
Proof. hammer_hook "Tactics" "Tactics.trans_eq_exercise".
Admitted.









Theorem S_injective : forall (n m : nat),
S n = S m ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.S_injective".
intros n m H1.
assert (H2: n = pred (S n)). { reflexivity. }
rewrite H2. rewrite H1. reflexivity.
Qed.



Theorem S_injective' : forall (n m : nat),
S n = S m ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.S_injective'".
intros n m H.



injection H. intros Hnm. apply Hnm.
Qed.



Theorem injection_ex1 : forall (n m o : nat),
[n; m] = [o; o] ->
[n] = [m].
Proof. hammer_hook "Tactics" "Tactics.injection_ex1".
intros n m o H.
injection H. intros H1 H2.
rewrite H1. rewrite H2. reflexivity.
Qed.



Theorem injection_ex2 : forall (n m : nat),
[n] = [m] ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.injection_ex2".
intros n m H.
injection H as Hnm. rewrite Hnm.
reflexivity. Qed.


Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
x :: y :: l = z :: j ->
y :: l = x :: j ->
x = y.
Proof. hammer_hook "Tactics" "Tactics.injection_ex3".
Admitted.




Theorem eqb_0_l : forall n,
0 =? n = true -> n = 0.
Proof. hammer_hook "Tactics" "Tactics.eqb_0_l".
intros n.



destruct n as [| n'] eqn:E.
-
intros H. reflexivity.



-
simpl.



intros H. discriminate H.
Qed.



Theorem discriminate_ex1 : forall (n : nat),
S n = O ->
2 + 2 = 5.
Proof. hammer_hook "Tactics" "Tactics.discriminate_ex1".
intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
false = true ->
[n] = [m].
Proof. hammer_hook "Tactics" "Tactics.discriminate_ex2".
intros n m contra. discriminate contra. Qed.




Example discriminate_ex3 :
forall (X : Type) (x y z : X) (l j : list X),
x :: y :: l = [] ->
x = z.
Proof. hammer_hook "Tactics" "Tactics.discriminate_ex3".
Admitted.




Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
x = y -> f x = f y.
Proof. hammer_hook "Tactics" "Tactics.f_equal". intros A B f x y eq. rewrite eq.  reflexivity.  Qed.






Theorem S_inj : forall (n m : nat) (b : bool),
(S n) =? (S m) = b  ->
n =? m = b.
Proof. hammer_hook "Tactics" "Tactics.S_inj".
intros n m b H. simpl in H. apply H.  Qed.



Theorem silly3' : forall (n : nat),
(n =? 5 = true -> (S (S n)) =? 7 = true) ->
true = (n =? 5)  ->
true = ((S (S n)) =? 7).
Proof. hammer_hook "Tactics" "Tactics.silly3'".
intros n eq H.
symmetry in H. apply eq in H. symmetry in H.
apply H.  Qed.





Theorem plus_n_n_injective : forall n m,
n + n = m + m ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.plus_n_n_injective".
intros n. induction n as [| n'].
Admitted.







Theorem double_injective_FAILED : forall n m,
double n = double m ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.double_injective_FAILED".
intros n m. induction n as [| n'].
-  simpl. intros eq. destruct m as [| m'] eqn:E.
+  reflexivity.
+  discriminate eq.
-  intros eq. destruct m as [| m'] eqn:E.
+  discriminate eq.
+  apply f_equal.



Abort.









Theorem double_injective : forall n m,
double n = double m ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.double_injective".
intros n. induction n as [| n'].
-  simpl. intros m eq. destruct m as [| m'] eqn:E.
+  reflexivity.
+  discriminate eq.

-  simpl.



intros m eq.



destruct m as [| m'] eqn:E.
+  simpl.



discriminate eq.

+
apply f_equal.



apply IHn'. injection eq as goal. apply goal. Qed.






Theorem eqb_true : forall n m,
n =? m = true -> n = m.
Proof. hammer_hook "Tactics" "Tactics.eqb_true".
Admitted.







Definition manual_grade_for_informal_proof : option (nat*string) := None.




Theorem double_injective_take2_FAILED : forall n m,
double n = double m ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.double_injective_take2_FAILED".
intros n m. induction m as [| m'].
-  simpl. intros eq. destruct n as [| n'] eqn:E.
+  reflexivity.
+  discriminate eq.
-  intros eq. destruct n as [| n'] eqn:E.
+  discriminate eq.
+  apply f_equal.

Abort.







Theorem double_injective_take2 : forall n m,
double n = double m ->
n = m.
Proof. hammer_hook "Tactics" "Tactics.double_injective_take2".
intros n m.

generalize dependent n.

induction m as [| m'].
-  simpl. intros n eq. destruct n as [| n'] eqn:E.
+  reflexivity.
+  discriminate eq.
-  intros n eq. destruct n as [| n'] eqn:E.
+  discriminate eq.
+  apply f_equal.
apply IHm'. injection eq as goal. apply goal. Qed.





Theorem eqb_id_true : forall x y,
eqb_id x y = true -> x = y.
Proof. hammer_hook "Tactics" "Tactics.eqb_id_true".
intros [m] [n]. simpl. intros H.
assert (H' : m = n). { apply eqb_true. apply H. }
rewrite H'. reflexivity.
Qed.



Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
length l = n ->
nth_error l n = None.
Proof. hammer_hook "Tactics" "Tactics.nth_error_after_last".
Admitted.







Definition square n := n * n.



Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof. hammer_hook "Tactics" "Tactics.square_mult".
intros n m.
simpl.



unfold square.



rewrite mult_assoc.
assert (H : n * m * n = n * n * m).
{ rewrite mult_comm. apply mult_assoc. }
rewrite H. rewrite mult_assoc. reflexivity.
Qed.



Definition foo (x: nat) := 5.



Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof. hammer_hook "Tactics" "Tactics.silly_fact_1".
intros m.
simpl.
reflexivity.
Qed.



Definition bar x :=
match x with
| O => 5
| S _ => 5
end.



Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof. hammer_hook "Tactics" "Tactics.silly_fact_2_FAILED".
intros m.
simpl.
Abort.





Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof. hammer_hook "Tactics" "Tactics.silly_fact_2".
intros m.
destruct m eqn:E.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.





Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof. hammer_hook "Tactics" "Tactics.silly_fact_2'".
intros m.
unfold bar.



destruct m eqn:E.
- reflexivity.
- reflexivity.
Qed.






Definition sillyfun (n : nat) : bool :=
if n =? 3 then false
else if n =? 5 then false
else false.

Theorem sillyfun_false : forall (n : nat),
sillyfun n = false.
Proof. hammer_hook "Tactics" "Tactics.sillyfun_false".
intros n. unfold sillyfun.
destruct (n =? 3) eqn:E1.
-  reflexivity.
-  destruct (n =? 5) eqn:E2.
+  reflexivity.
+  reflexivity.  Qed.





Fixpoint split {X Y : Type} (l : list (X*Y))
: (list X) * (list Y) :=
match l with
| [] => ([], [])
| (x, y) :: t =>
match split t with
| (lx, ly) => (x :: lx, y :: ly)
end
end.



Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
split l = (l1, l2) ->
combine l1 l2 = l.
Proof. hammer_hook "Tactics" "Tactics.combine_split".
Admitted.




Definition sillyfun1 (n : nat) : bool :=
if n =? 3 then true
else if n =? 5 then true
else false.



Theorem sillyfun1_odd_FAILED : forall (n : nat),
sillyfun1 n = true ->
oddb n = true.
Proof. hammer_hook "Tactics" "Tactics.sillyfun1_odd_FAILED".
intros n eq. unfold sillyfun1 in eq.
destruct (n =? 3).

Abort.



Theorem sillyfun1_odd : forall (n : nat),
sillyfun1 n = true ->
oddb n = true.
Proof. hammer_hook "Tactics" "Tactics.sillyfun1_odd".
intros n eq. unfold sillyfun1 in eq.
destruct (n =? 3) eqn:Heqe3.

-  apply eqb_true in Heqe3.
rewrite -> Heqe3. reflexivity.
-

destruct (n =? 5) eqn:Heqe5.
+
apply eqb_true in Heqe5.
rewrite -> Heqe5. reflexivity.
+  discriminate eq.  Qed.


Theorem bool_fn_applied_thrice :
forall (f : bool -> bool) (b : bool),
f (f (f b)) = f b.
Proof. hammer_hook "Tactics" "Tactics.bool_fn_applied_thrice".
Admitted.











Theorem eqb_sym : forall (n m : nat),
(n =? m) = (m =? n).
Proof. hammer_hook "Tactics" "Tactics.eqb_sym".
Admitted.






Theorem eqb_trans : forall n m p,
n =? m = true ->
m =? p = true ->
n =? p = true.
Proof. hammer_hook "Tactics" "Tactics.eqb_trans".
Admitted.




Definition split_combine_statement : Prop

. Admitted.

Theorem split_combine : split_combine_statement.
Proof. hammer_hook "Tactics" "Tactics.split_combine".
Admitted.


Definition manual_grade_for_split_combine : option (nat*string) := None.




Theorem filter_exercise : forall (X : Type) (test : X -> bool)
(x : X) (l lf : list X),
filter test l = x :: lf ->
test x = true.
Proof. hammer_hook "Tactics" "Tactics.filter_exercise".
Admitted.




Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
. Admitted.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. hammer_hook "Tactics" "Tactics.test_forallb_1".  Admitted.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. hammer_hook "Tactics" "Tactics.test_forallb_2".  Admitted.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. hammer_hook "Tactics" "Tactics.test_forallb_3".  Admitted.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. hammer_hook "Tactics" "Tactics.test_forallb_4".  Admitted.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
. Admitted.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. hammer_hook "Tactics" "Tactics.test_existsb_1".  Admitted.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. hammer_hook "Tactics" "Tactics.test_existsb_2".  Admitted.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. hammer_hook "Tactics" "Tactics.test_existsb_3".  Admitted.

Example test_existsb_4 : existsb evenb [] = false.
Proof. hammer_hook "Tactics" "Tactics.test_existsb_4".  Admitted.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
. Admitted.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
existsb test l = existsb' test l.
Proof. hammer_hook "Tactics" "Tactics.existsb_existsb'".  Admitted.






