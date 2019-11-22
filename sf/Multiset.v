From Hammer Require Import Hammer.





Require Import Coq.Strings.String.
From VFA Require Import Perm.
From VFA Require Import Sort.
Require Export FunctionalExtensionality.



Definition value := nat.

Definition multiset := value -> nat.



Definition empty : multiset :=
fun x => 0.

Definition union (a b : multiset) : multiset :=
fun x => a x + b x.

Definition singleton (v: value) : multiset :=
fun x => if x =? v then 1 else 0.




Lemma union_assoc: forall a b c : multiset,
union a (union b c) = union (union a b) c.
Proof. hammer_hook "Multiset" "Multiset.union_assoc".
intros.
extensionality x.
Admitted.



Lemma union_comm: forall a b : multiset,
union a b = union b a.
Proof. hammer_hook "Multiset" "Multiset.union_comm".
Admitted.






Fixpoint contents (al: list value) : multiset :=
match al with
| a :: bl => union (singleton a) (contents bl)
| nil => empty
end.



Example sort_pi: sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof. hammer_hook "Multiset" "Multiset.sort_pi". simpl. reflexivity. Qed.

Example sort_pi_same_contents:
contents (sort [3;1;4;1;5;9;2;6;5;3;5]) = contents [3;1;4;1;5;9;2;6;5;3;5].
Proof. hammer_hook "Multiset" "Multiset.sort_pi_same_contents".
extensionality x.
do 10 (destruct x; try reflexivity).

Qed.






Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
forall al, contents al = contents (f al) /\ sorted (f al).




Lemma insert_contents: forall x l, contents (x::l) = contents (insert x l).
Proof. hammer_hook "Multiset" "Multiset.insert_contents".
Admitted.





Theorem sort_contents: forall l, contents l = contents (sort l).
Admitted.




Theorem insertion_sort_correct:
is_a_sorting_algorithm' sort.
Proof. hammer_hook "Multiset" "Multiset.insertion_sort_correct".
split. apply sort_contents. apply sort_sorted.
Qed.




Definition manual_grade_for_permutations_vs_multiset : option (prod nat string) := None.










Lemma perm_contents:
forall al bl : list nat,
Permutation al bl -> contents al = contents bl.
Admitted.




Fixpoint list_delete (al: list value) (v: value) :=
match al with
| x::bl => if x =? v then bl else x :: list_delete bl v
| nil => nil
end.

Definition multiset_delete (m: multiset) (v: value) :=
fun x => if x =? v then pred(m x) else m x.


Lemma delete_contents:
forall v al,
contents (list_delete al v) = multiset_delete (contents al) v.
Proof. hammer_hook "Multiset" "Multiset.delete_contents".
intros.
extensionality x.
induction al.
simpl. unfold empty, multiset_delete.
bdestruct (x =? v); auto.
simpl.
bdestruct (a =? v).
Admitted.



Lemma contents_perm_aux:
forall v b, empty = union (singleton v) b -> False.
Proof. hammer_hook "Multiset" "Multiset.contents_perm_aux".
Admitted.



Lemma contents_in:
forall (a: value) (bl: list value) , contents bl a > 0 -> In a bl.
Proof. hammer_hook "Multiset" "Multiset.contents_in".
Admitted.



Lemma in_perm_delete:
forall a bl,
In a bl -> Permutation (a :: list_delete bl a) bl.
Proof. hammer_hook "Multiset" "Multiset.in_perm_delete".
Admitted.



Lemma contents_perm:
forall al bl, contents al = contents bl -> Permutation al bl.
Proof. hammer_hook "Multiset" "Multiset.contents_perm".
induction al; destruct bl; intro.
auto.
simpl in H.
contradiction (contents_perm_aux _ _ H).
simpl in H. symmetry in H.
contradiction (contents_perm_aux _ _ H).
specialize (IHal (list_delete (v :: bl) a)).
remember (v::bl) as cl.
clear v bl Heqcl.



Admitted.




Theorem same_contents_iff_perm:
forall al bl, contents al = contents bl <-> Permutation al bl.
Proof. hammer_hook "Multiset" "Multiset.same_contents_iff_perm".
intros. split. apply contents_perm. apply perm_contents.
Qed.



Corollary sort_specifications_equivalent:
forall sort, is_a_sorting_algorithm sort <->  is_a_sorting_algorithm' sort.
Proof. hammer_hook "Multiset" "Multiset.sort_specifications_equivalent".
unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
split; intros;
destruct (H al); split; auto;
apply same_contents_iff_perm; auto.
Qed.
