From Hammer Require Import Hammer.















From VFA Require Import Perm.

Fixpoint insert (i:nat) (l: list nat) :=
match l with
| nil => i::nil
| h::t => if i <=? h then i::h::t else h :: insert i t
end.

Fixpoint sort (l: list nat) : list nat :=
match l with
| nil => nil
| h::t => insert h (sort t)
end.

Example sort_pi: sort [3;1;4;1;5;9;2;6;5;3;5]
= [1;1;2;3;3;4;5;5;5;6;9].
Proof. hammer_hook "Sort" "Sort.sort_pi". simpl. reflexivity. Qed.



Eval compute in insert 7 [1; 3; 4; 8; 12; 14; 18].









Inductive sorted: list nat -> Prop :=
| sorted_nil:
sorted nil
| sorted_1: forall x,
sorted (x::nil)
| sorted_cons: forall x y l,
x <= y -> sorted (y::l) -> sorted (x::y::l).



Definition sorted' (al: list nat) :=
forall i j, i < j < length al -> nth i al 0 <= nth j al 0.



Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
forall al, Permutation al (f al) /\ sorted (f al).








Search Permutation.

Lemma insert_perm: forall x l, Permutation (x::l) (insert x l).
Proof. hammer_hook "Sort" "Sort.insert_perm".
Admitted.





Theorem sort_perm: forall l, Permutation l (sort l).
Proof. hammer_hook "Sort" "Sort.sort_perm".
Admitted.





Lemma insert_sorted:
forall a l, sorted l -> sorted (insert a l).
Proof. hammer_hook "Sort" "Sort.insert_sorted".
Admitted.





Theorem sort_sorted: forall l, sorted (sort l).
Proof. hammer_hook "Sort" "Sort.sort_sorted".
Admitted.




Theorem insertion_sort_correct:
is_a_sorting_algorithm sort.
Proof. hammer_hook "Sort" "Sort.insertion_sort_correct".
split. apply sort_perm. apply sort_sorted.
Qed.







Lemma sorted_sorted': forall al, sorted al -> sorted' al.



Admitted.



Lemma sorted'_sorted: forall al, sorted' al -> sorted al.



Proof. hammer_hook "Sort" "Sort.sorted'_sorted".
Admitted.








Lemma Forall_nth:
forall {A: Type} (P: A -> Prop) d (al: list A),
Forall P al <-> (forall i,  i < length al -> P (nth i al d)).
Proof. hammer_hook "Sort" "Sort.Forall_nth".
Admitted.




Lemma insert_sorted':
forall a l, sorted' l -> sorted' (insert a l).
Admitted.



Theorem sort_sorted': forall l, sorted' (sort l).
Admitted.








