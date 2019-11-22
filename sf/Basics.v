From Hammer Require Import Hammer.






















Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.



Definition next_weekday (d:day) : day :=
match d with
| monday    => tuesday
| tuesday   => wednesday
| wednesday => thursday
| thursday  => friday
| friday    => monday
| saturday  => monday
| sunday    => monday
end.





Compute (next_weekday friday).


Compute (next_weekday (next_weekday saturday)).






Example test_next_weekday:
(next_weekday (next_weekday saturday)) = tuesday.



Proof. hammer_hook "Basics" "Basics.test_next_weekday". simpl. reflexivity.  Qed.













Inductive bool : Type :=
| true
| false.



Definition negb (b:bool) : bool :=
match b with
| true => false
| false => true
end.

Definition andb (b1:bool) (b2:bool) : bool :=
match b1 with
| true => b2
| false => false
end.

Definition orb (b1:bool) (b2:bool) : bool :=
match b1 with
| true => true
| false => b2
end.



Example test_orb1:  (orb true  false) = true.
Proof. hammer_hook "Basics" "Basics.test_orb1". simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. hammer_hook "Basics" "Basics.test_orb2". simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. hammer_hook "Basics" "Basics.test_orb3". simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. hammer_hook "Basics" "Basics.test_orb4". simpl. reflexivity.  Qed.



Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. hammer_hook "Basics" "Basics.test_orb5". simpl. reflexivity. Qed.





Definition nandb (b1:bool) (b2:bool) : bool
. Admitted.

Example test_nandb1:               (nandb true false) = true.
Admitted.
Example test_nandb2:               (nandb false false) = true.
Admitted.
Example test_nandb3:               (nandb false true) = true.
Admitted.
Example test_nandb4:               (nandb true true) = false.
Admitted.




Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
. Admitted.

Example test_andb31:                 (andb3 true true true) = true.
Admitted.
Example test_andb32:                 (andb3 false true true) = false.
Admitted.
Example test_andb33:                 (andb3 true false true) = false.
Admitted.
Example test_andb34:                 (andb3 true true false) = false.
Admitted.







Check true.

Check (negb true).




Check negb.









Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).





Definition monochrome (c : color) : bool :=
match c with
| black => true
| white => true
| primary q => false
end.



Definition isred (c : color) : bool :=
match c with
| black => false
| white => false
| primary red => true
| primary _ => false
end.








Inductive bit : Type :=
| B0
| B1.

Inductive nybble : Type :=
| bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).




Definition all_zero (nb : nybble) : bool :=
match nb with
| (bits B0 B0 B0 B0) => true
| (bits _ _ _ _) => false
end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).







Module NatPlayground.






Inductive nat : Type :=
| O
| S (n : nat).









Inductive nat' : Type :=
| stop
| tick (foo : nat').





Definition pred (n : nat) : nat :=
match n with
| O => O
| S n' => n'
end.



End NatPlayground.



Check (S (S (S (S O)))).


Definition minustwo (n : nat) : nat :=
match n with
| O => O
| S O => O
| S (S n') => n'
end.

Compute (minustwo 4).




Check S.
Check pred.
Check minustwo.



Fixpoint evenb (n:nat) : bool :=
match n with
| O        => true
| S O      => false
| S (S n') => evenb n'
end.



Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. hammer_hook "Basics" "Basics.test_oddb1". simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. hammer_hook "Basics" "Basics.test_oddb2". simpl. reflexivity.  Qed.



Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.



Compute (plus 3 2).







Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.

Example test_mult1: (mult 3 3) = 9.
Proof. hammer_hook "Basics" "Basics.NatPlayground2.test_mult1". simpl. reflexivity.  Qed.



Fixpoint minus (n m:nat) : nat :=
match n, m with
| O   , _    => O
| S _ , O    => n
| S n', S m' => minus n' m'
end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
match power with
| O => S O
| S p => mult base (exp base p)
end.



Fixpoint factorial (n:nat) : nat
. Admitted.

Example test_factorial1:          (factorial 3) = 6.
Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Admitted.




Notation "x + y" := (plus x y)
(at level 50, left associativity)
: nat_scope.
Notation "x - y" := (minus x y)
(at level 50, left associativity)
: nat_scope.
Notation "x * y" := (mult x y)
(at level 40, left associativity)
: nat_scope.

Check ((0 + 1) + 1).





Fixpoint eqb (n m : nat) : bool :=
match n with
| O => match m with
| O => true
| S m' => false
end
| S n' => match m with
| O => false
| S m' => eqb n' m'
end
end.



Fixpoint leb (n m : nat) : bool :=
match n with
| O => true
| S n' =>
match m with
| O => false
| S m' => leb n' m'
end
end.

Example test_leb1:             (leb 2 2) = true.
Proof. hammer_hook "Basics" "Basics.test_leb1". simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. hammer_hook "Basics" "Basics.test_leb2". simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. hammer_hook "Basics" "Basics.test_leb3". simpl. reflexivity.  Qed.



Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3':             (4 <=? 2) = false.
Proof. hammer_hook "Basics" "Basics.test_leb3'". simpl. reflexivity.  Qed.



Definition ltb (n m : nat) : bool
. Admitted.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
Admitted.
Example test_ltb2:             (ltb 2 4) = true.
Admitted.
Example test_ltb3:             (ltb 4 2) = false.
Admitted.







Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. hammer_hook "Basics" "Basics.plus_O_n".
intros n. simpl. reflexivity.  Qed.



Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof. hammer_hook "Basics" "Basics.plus_O_n'".
intros n. reflexivity. Qed.





Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. hammer_hook "Basics" "Basics.plus_1_l".
intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. hammer_hook "Basics" "Basics.mult_0_l".
intros n. reflexivity.  Qed.










Theorem plus_id_example : forall n m:nat,
n = m ->
n + n = m + m.



Proof. hammer_hook "Basics" "Basics.plus_id_example".

intros n m.

intros H.

rewrite -> H.
reflexivity.  Qed.





Theorem plus_id_exercise : forall n m o : nat,
n = m -> m = o -> n + m = m + o.
Proof. hammer_hook "Basics" "Basics.plus_id_exercise".
Admitted.






Theorem mult_0_plus : forall n m : nat,
(0 + n) * m = n * m.
Proof. hammer_hook "Basics" "Basics.mult_0_plus".
intros n m.
rewrite -> plus_O_n.
reflexivity.  Qed.


Theorem mult_S_1 : forall n m : nat,
m = S n ->
m * (1 + n) = m * m.
Proof. hammer_hook "Basics" "Basics.mult_S_1".
Admitted.








Theorem plus_1_neq_0_firsttry : forall n : nat,
(n + 1) =? 0 = false.
Proof. hammer_hook "Basics" "Basics.plus_1_neq_0_firsttry".
intros n.
simpl.
Abort.



Theorem plus_1_neq_0 : forall n : nat,
(n + 1) =? 0 = false.
Proof. hammer_hook "Basics" "Basics.plus_1_neq_0".
intros n. destruct n as [| n'] eqn:E.
- reflexivity.
- reflexivity.   Qed.



Theorem negb_involutive : forall b : bool,
negb (negb b) = b.
Proof. hammer_hook "Basics" "Basics.negb_involutive".
intros b. destruct b eqn:E.
- reflexivity.
- reflexivity.  Qed.



Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof. hammer_hook "Basics" "Basics.andb_commutative".
intros b c. destruct b eqn:Eb.
- destruct c eqn:Ec.
+ reflexivity.
+ reflexivity.
- destruct c eqn:Ec.
+ reflexivity.
+ reflexivity.
Qed.





Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof. hammer_hook "Basics" "Basics.andb_commutative'".
intros b c. destruct b eqn:Eb.
{ destruct c eqn:Ec.
{ reflexivity. }
{ reflexivity. } }
{ destruct c eqn:Ec.
{ reflexivity. }
{ reflexivity. } }
Qed.



Theorem andb3_exchange :
forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof. hammer_hook "Basics" "Basics.andb3_exchange".
intros b c d. destruct b eqn:Eb.
- destruct c eqn:Ec.
{ destruct d eqn:Ed.
- reflexivity.
- reflexivity. }
{ destruct d eqn:Ed.
- reflexivity.
- reflexivity. }
- destruct c eqn:Ec.
{ destruct d eqn:Ed.
- reflexivity.
- reflexivity. }
{ destruct d eqn:Ed.
- reflexivity.
- reflexivity. }
Qed.



Theorem plus_1_neq_0' : forall n : nat,
(n + 1) =? 0 = false.
Proof. hammer_hook "Basics" "Basics.plus_1_neq_0'".
intros [|n].
- reflexivity.
- reflexivity.  Qed.



Theorem andb_commutative'' :
forall b c, andb b c = andb c b.
Proof. hammer_hook "Basics" "Basics.andb_commutative''".
intros [] [].
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.



Theorem andb_true_elim2 : forall b c : bool,
andb b c = true -> c = true.
Proof. hammer_hook "Basics" "Basics.andb_true_elim2".
Admitted.



Theorem zero_nbeq_plus_1 : forall n : nat,
0 =? (n + 1) = false.
Proof. hammer_hook "Basics" "Basics.zero_nbeq_plus_1".
Admitted.







Notation "x + y" := (plus x y)
(at level 50, left associativity)
: nat_scope.
Notation "x * y" := (mult x y)
(at level 40, left associativity)
: nat_scope.








Fixpoint plus' (n : nat) (m : nat) : nat :=
match n with
| O => m
| S n' => S (plus' n' m)
end.














Theorem identity_fn_applied_twice :
forall (f : bool -> bool),
(forall (x : bool), f x = x) ->
forall (b : bool), f (f b) = b.
Proof. hammer_hook "Basics" "Basics.identity_fn_applied_twice".
Admitted.







From Coq Require Export String.


Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.




Theorem andb_eq_orb :
forall (b c : bool),
(andb b c = orb b c) ->
b = c.
Proof. hammer_hook "Basics" "Basics.andb_eq_orb".
Admitted.





Inductive bin : Type :=
| Z
| A (n : bin)
| B (n : bin).



Fixpoint incr (m:bin) : bin
. Admitted.

Fixpoint bin_to_nat (m:bin) : nat
. Admitted.






Definition manual_grade_for_binary : option (nat*string) := None.



