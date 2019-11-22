From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From VFA Require Import Perm.






Check Nat.lt.
Check Nat.ltb.



Print reflect.


Check blt_reflect.





Goal (3<?7 = true). Proof. reflexivity. Qed.



Theorem three_less_seven_1: 3<7.
Proof. hammer_hook "Decide" "Decide.three_less_seven_1".
assert (H := blt_reflect 3 7).
remember (3<?7) as b.
destruct H as [P|Q] eqn:?.
*
apply P.
*
compute in Heqb.
inversion Heqb.
Qed.



Theorem three_less_seven_2: 3<7.
Proof. hammer_hook "Decide" "Decide.three_less_seven_2".
assert (H := blt_reflect 3 7).
inversion H as [P|Q].
apply P.
Qed.






Module ScratchPad.



Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B.



Definition t1 := sumbool (3<7) (3>2).
Lemma less37: 3<7. Proof. omega. Qed.
Lemma greater23: 3>2. Proof. omega. Qed.

Definition v1a: t1 := left (3<7) (3>2) less37.
Definition v1b: t1 := right (3<7) (3>2) greater23.





Definition t2 := sumbool (3<7) (2>3).
Definition v2a: t2 := left (3<7) (2>3) less37.





Notation "{ A } + { B }" := (sumbool A B) : type_scope.



Definition t4 := forall a b, {a<b}+{~(a<b)}.



Definition v3: {3<7}+{~(3<7)} := left _ _ less37.

Definition is_3_less_7:  bool :=
match v3 with
| left _ _ _ => true
| right _ _ _ => false
end.

Eval compute in is_3_less_7.

Print t4.



Check blt_reflect.



Definition lt_dec (a: nat) (b: nat) : {a<b}+{~(a<b)} :=
match blt_reflect a b with
| ReflectT _ P => left (a < b) (~ a < b) P
| ReflectF _ Q => right (a < b) (~ a < b) Q
end.



Definition lt_dec' (a: nat) (b: nat) : {a<b}+{~(a<b)}.
destruct (blt_reflect a b) as [P|Q]. left. apply P.  right. apply Q.
Defined.

Print lt_dec.
Print lt_dec'.

Theorem lt_dec_equivalent: forall a b, lt_dec a b = lt_dec' a b.
Proof. hammer_hook "Decide" "Decide.ScratchPad.lt_dec_equivalent".
intros.
unfold lt_dec, lt_dec'.
reflexivity.
Qed.



End ScratchPad.




Module ScratchPad2.
Locate sumbool.
Print sumbool.



Definition lt_dec (a: nat) (b: nat) : {a<b}+{~(a<b)} :=
match blt_reflect a b with
| ReflectT _ P => left P
| ReflectF _ Q => right Q
end.

Definition le_dec (a: nat) (b: nat) : {a<=b}+{~(a<=b)} :=
match ble_reflect a b with
| ReflectT _ P => left P
| ReflectF _ Q => right Q
end.



Fixpoint insert (x:nat) (l: list nat) :=
match l with
| nil => x::nil
| h::t => if le_dec x h then x::h::t else h :: insert x t
end.

Fixpoint sort (l: list nat) : list nat :=
match l with
| nil => nil
| h::t => insert h (sort t)
end.

Inductive sorted: list nat -> Prop :=
| sorted_nil:
sorted nil
| sorted_1: forall x,
sorted (x::nil)
| sorted_cons: forall x y l,
x <= y -> sorted (y::l) -> sorted (x::y::l).


Lemma insert_sorted:
forall a l, sorted l -> sorted (insert a l).
Proof. hammer_hook "Decide" "Decide.ScratchPad2.insert_sorted".
intros a l H.
induction H.
- constructor.
- unfold insert.
destruct (le_dec a x) as [ Hle | Hgt].



Admitted.







Axiom lt_dec_axiom_1:  forall i j: nat, i<j \/ ~(i<j).







Axiom lt_dec_axiom_2:  forall i j: nat, {i<j} + {~(i<j)}.

Definition max_with_axiom (i j: nat) : nat :=
if lt_dec_axiom_2 i j then j else i.



Eval compute in max_with_axiom 3 7.




Lemma prove_with_max_axiom:   max_with_axiom 3 7 = 7.
Proof. hammer_hook "Decide" "Decide.ScratchPad2.prove_with_max_axiom".
unfold max_with_axiom.
try reflexivity.

destruct (lt_dec_axiom_2 3 7).
reflexivity.
contradiction n. omega.
Qed.



End ScratchPad2.







Lemma compute_with_lt_dec:  (if ScratchPad2.lt_dec 3 7 then 7 else 3) = 7.
Proof. hammer_hook "Decide" "Decide.compute_with_lt_dec".
compute.

Abort.



Lemma compute_with_StdLib_lt_dec:  (if lt_dec 3 7 then 7 else 3) = 7.
Proof. hammer_hook "Decide" "Decide.compute_with_StdLib_lt_dec".
compute.
reflexivity.
Qed.



Search ({_}+{~_}).




Definition list_nat_eq_dec:
(forall al bl : list nat, {al=bl}+{al<>bl}) :=
list_eq_dec eq_nat_dec.

Eval compute in if list_nat_eq_dec [1;3;4] [1;4;3] then true else false.


Eval compute in if list_nat_eq_dec [1;3;4] [1;3;4] then true else false.





Definition list_nat_in: forall (i: nat) (al: list nat), {In i al}+{~ In i al}
. Admitted.

Example in_4_pi:  (if list_nat_in 4  [3;1;4;1;5;9;2;6] then true else false) = true.
Proof. hammer_hook "Decide" "Decide.in_4_pi".
simpl.

Admitted.









