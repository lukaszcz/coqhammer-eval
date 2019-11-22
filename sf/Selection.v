From Hammer Require Import Hammer.







Require Export Coq.Lists.List.
From VFA Require Import Perm.



Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (x, nil)
|  h::t => if x <=? h
then let (j, l') := select x t in (j, h::l')
else let (j,l') := select h t in (j, x::l')
end.







Fixpoint selsort l n {struct n} :=
match l, n with
| x::r, S n' => let (y,r') := select x r
in y :: selsort r' n'
| nil, _ => nil
| _::_, O => nil
end.



Example out_of_gas: selsort [3;1;4;1;5] 3 <> [1;1;3;4;5].
Proof. hammer_hook "Selection" "Selection.out_of_gas".
simpl.
intro. inversion H.
Qed.



Example too_much_gas: selsort [3;1;4;1;5] 10 = [1;1;3;4;5].
Proof. hammer_hook "Selection" "Selection.too_much_gas".
simpl.
auto.
Qed.



Definition selection_sort l := selsort l (length l).

Example sort_pi: selection_sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof. hammer_hook "Selection" "Selection.sort_pi".
unfold selection_sort.
simpl.
reflexivity.
Qed.



Inductive sorted: list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_1: forall i, sorted (i::nil)
| sorted_cons: forall i j l, i <= j -> sorted (j::l) -> sorted (i::j::l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
forall al, Permutation al (f al) /\ sorted (f al).






Definition selection_sort_correct : Prop :=
is_a_sorting_algorithm selection_sort.




Lemma select_perm: forall x l,
let (y,r) := select x l in
Permutation (x::l) (y::r).
Proof. hammer_hook "Selection" "Selection.select_perm".



intros x l; revert x.
induction l; intros; simpl in *.
Admitted.



Lemma selsort_perm:
forall n,
forall l, length l = n -> Permutation l (selsort l n).
Proof. hammer_hook "Selection" "Selection.selsort_perm".



Admitted.

Theorem selection_sort_perm:
forall l, Permutation l (selection_sort l).
Proof. hammer_hook "Selection" "Selection.selection_sort_perm".
Admitted.



Lemma select_smallest_aux:
forall x al y bl,
Forall (fun z => y <= z) bl ->
select x al = (y,bl) ->
y <= x.
Proof. hammer_hook "Selection" "Selection.select_smallest_aux".

Admitted.

Theorem select_smallest:
forall x al y bl, select x al = (y,bl) ->
Forall (fun z => y <= z) bl.
Proof. hammer_hook "Selection" "Selection.select_smallest".
intros x al; revert x; induction al; intros; simpl in *.
admit.
bdestruct (x <=? a).
*
destruct (select x al) eqn:?H.
Admitted.



Lemma selection_sort_sorted_aux:
forall  y bl,
sorted (selsort bl (length bl)) ->
Forall (fun z : nat => y <= z) bl ->
sorted (y :: selsort bl (length bl)).
Proof. hammer_hook "Selection" "Selection.selection_sort_sorted_aux".

Admitted.

Theorem selection_sort_sorted: forall al, sorted (selection_sort al).
Proof. hammer_hook "Selection" "Selection.selection_sort_sorted".
intros.
unfold selection_sort.

Admitted.




Theorem selection_sort_is_correct: selection_sort_correct.
Proof. hammer_hook "Selection" "Selection.selection_sort_is_correct".
split. apply selection_sort_perm. apply selection_sort_sorted.
Qed.






Require Import Recdef.

Function selsort' l {measure length l} :=
match l with
| x::r => let (y,r') := select x r
in y :: selsort' r'
| nil => nil
end.



Proof.
intros.
pose proof (select_perm x r).
rewrite teq0 in H.
apply Permutation_length in H.
simpl in *; omega.
Defined.


Lemma selsort'_perm:
forall n,
forall l, length l = n -> Permutation l (selsort' l).
Proof. hammer_hook "Selection" "Selection.selsort'_perm".





Admitted.


Eval compute in selsort' [3;1;4;1;5;9;2;6;5].


