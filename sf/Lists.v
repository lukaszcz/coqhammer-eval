From Hammer Require Import Hammer.



From LF Require Export Induction.
Module NatList.






Inductive natprod : Type :=
| pair (n1 n2 : nat).



Check (pair 3 5).



Definition fst (p : natprod) : nat :=
match p with
| pair x y => x
end.

Definition snd (p : natprod) : nat :=
match p with
| pair x y => y
end.

Compute (fst (pair 3 5)).




Notation "( x , y )" := (pair x y).



Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
match p with
| (x,y) => x
end.

Definition snd' (p : natprod) : nat :=
match p with
| (x,y) => y
end.

Definition swap_pair (p : natprod) : natprod :=
match p with
| (x,y) => (y,x)
end.





Theorem surjective_pairing' : forall (n m : nat),
(n,m) = (fst (n,m), snd (n,m)).
Proof. hammer_hook "Lists" "Lists.NatList.surjective_pairing'".
reflexivity.  Qed.



Theorem surjective_pairing_stuck : forall (p : natprod),
p = (fst p, snd p).
Proof. hammer_hook "Lists" "Lists.NatList.surjective_pairing_stuck".
simpl.
Abort.



Theorem surjective_pairing : forall (p : natprod),
p = (fst p, snd p).
Proof. hammer_hook "Lists" "Lists.NatList.surjective_pairing".
intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.




Theorem snd_fst_is_swap : forall (p : natprod),
(snd p, fst p) = swap_pair p.
Proof. hammer_hook "Lists" "Lists.NatList.snd_fst_is_swap".
Admitted.



Theorem fst_swap_is_snd : forall (p : natprod),
fst (swap_pair p) = snd p.
Proof. hammer_hook "Lists" "Lists.NatList.fst_swap_is_snd".
Admitted.







Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).



Definition mylist := cons 1 (cons 2 (cons 3 nil)).



Notation "x :: l" := (cons x l)
(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).



Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].








Fixpoint repeat (n count : nat) : natlist :=
match count with
| O => nil
| S count' => n :: (repeat n count')
end.






Fixpoint length (l:natlist) : nat :=
match l with
| nil => O
| h :: t => S (length t)
end.






Fixpoint app (l1 l2 : natlist) : natlist :=
match l1 with
| nil    => l2
| h :: t => h :: (app t l2)
end.



Notation "x ++ y" := (app x y)
(right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. hammer_hook "Lists" "Lists.NatList.test_app1". reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. hammer_hook "Lists" "Lists.NatList.test_app2". reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. hammer_hook "Lists" "Lists.NatList.test_app3". reflexivity.  Qed.






Definition hd (default:nat) (l:natlist) : nat :=
match l with
| nil => default
| h :: t => h
end.

Definition tl (l:natlist) : natlist :=
match l with
| nil => nil
| h :: t => t
end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. hammer_hook "Lists" "Lists.NatList.test_hd1". reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. hammer_hook "Lists" "Lists.NatList.test_hd2". reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. hammer_hook "Lists" "Lists.NatList.test_tl". reflexivity.  Qed.






Fixpoint nonzeros (l:natlist) : natlist
. Admitted.

Example test_nonzeros:
nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Admitted.

Fixpoint oddmembers (l:natlist) : natlist
. Admitted.

Example test_oddmembers:
oddmembers [0;1;0;2;3;0;0] = [1;3].
Admitted.

Definition countoddmembers (l:natlist) : nat
. Admitted.

Example test_countoddmembers1:
countoddmembers [1;0;3;1;4;5] = 4.
Admitted.

Example test_countoddmembers2:
countoddmembers [0;2;4] = 0.
Admitted.

Example test_countoddmembers3:
countoddmembers nil = 0.
Admitted.




Fixpoint alternate (l1 l2 : natlist) : natlist
. Admitted.

Example test_alternate1:
alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Admitted.

Example test_alternate2:
alternate [1] [4;5;6] = [1;4;5;6].
Admitted.

Example test_alternate3:
alternate [1;2;3] [4] = [1;4;2;3].
Admitted.

Example test_alternate4:
alternate [] [20;30] = [20;30].
Admitted.







Definition bag := natlist.



Fixpoint count (v:nat) (s:bag) : nat
. Admitted.



Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Admitted.



Definition sum : bag -> bag -> bag
. Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Admitted.

Definition add (v:nat) (s:bag) : bag
. Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Admitted.

Definition member (v:nat) (s:bag) : bool
. Admitted.

Example test_member1:             member 1 [1;4;1] = true.
Admitted.

Example test_member2:             member 2 [1;4;1] = false.
Admitted.






Fixpoint remove_one (v:nat) (s:bag) : bag
. Admitted.

Example test_remove_one1:
count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Admitted.

Example test_remove_one2:
count 5 (remove_one 5 [2;1;4;1]) = 0.
Admitted.

Example test_remove_one3:
count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Admitted.

Example test_remove_one4:
count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
. Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool
. Admitted.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Admitted.







Definition manual_grade_for_bag_theorem : option (nat*string) := None.







Theorem nil_app : forall l:natlist,
[] ++ l = l.
Proof. hammer_hook "Lists" "Lists.NatList.nil_app". reflexivity. Qed.





Theorem tl_length_pred : forall l:natlist,
pred (length l) = length (tl l).
Proof. hammer_hook "Lists" "Lists.NatList.tl_length_pred".
intros l. destruct l as [| n l'].
-
reflexivity.
-
reflexivity.  Qed.















Theorem app_assoc : forall l1 l2 l3 : natlist,
(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. hammer_hook "Lists" "Lists.NatList.app_assoc".
intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
-
reflexivity.
-
simpl. rewrite -> IHl1'. reflexivity.  Qed.












Fixpoint rev (l:natlist) : natlist :=
match l with
| nil    => nil
| h :: t => rev t ++ [h]
end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. hammer_hook "Lists" "Lists.NatList.test_rev1". reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. hammer_hook "Lists" "Lists.NatList.test_rev2". reflexivity.  Qed.






Theorem rev_length_firsttry : forall l : natlist,
length (rev l) = length l.
Proof. hammer_hook "Lists" "Lists.NatList.rev_length_firsttry".
intros l. induction l as [| n l' IHl'].
-
reflexivity.
-

simpl.

rewrite <- IHl'.

Abort.



Theorem app_length : forall l1 l2 : natlist,
length (l1 ++ l2) = (length l1) + (length l2).
Proof. hammer_hook "Lists" "Lists.NatList.app_length".

intros l1 l2. induction l1 as [| n l1' IHl1'].
-
reflexivity.
-
simpl. rewrite -> IHl1'. reflexivity.  Qed.





Theorem rev_length : forall l : natlist,
length (rev l) = length l.
Proof. hammer_hook "Lists" "Lists.NatList.rev_length".
intros l. induction l as [| n l' IHl'].
-
reflexivity.
-
simpl. rewrite -> app_length, plus_comm.
simpl. rewrite -> IHl'. reflexivity.  Qed.

























Theorem app_nil_r : forall l : natlist,
l ++ [] = l.
Proof. hammer_hook "Lists" "Lists.NatList.app_nil_r".
Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. hammer_hook "Lists" "Lists.NatList.rev_app_distr".
Admitted.

Theorem rev_involutive : forall l : natlist,
rev (rev l) = l.
Proof. hammer_hook "Lists" "Lists.NatList.rev_involutive".
Admitted.



Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof. hammer_hook "Lists" "Lists.NatList.app_assoc4".
Admitted.



Lemma nonzeros_app : forall l1 l2 : natlist,
nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof. hammer_hook "Lists" "Lists.NatList.nonzeros_app".
Admitted.




Fixpoint eqblist (l1 l2 : natlist) : bool
. Admitted.

Example test_eqblist1 :
(eqblist nil nil = true).
Admitted.

Example test_eqblist2 :
eqblist [1;2;3] [1;2;3] = true.
Admitted.

Example test_eqblist3 :
eqblist [1;2;3] [1;2;4] = false.
Admitted.

Theorem eqblist_refl : forall l:natlist,
true = eqblist l l.
Proof. hammer_hook "Lists" "Lists.NatList.eqblist_refl".
Admitted.








Theorem count_member_nonzero : forall (s : bag),
1 <=? (count 1 (1 :: s)) = true.
Proof. hammer_hook "Lists" "Lists.NatList.count_member_nonzero".
Admitted.




Theorem leb_n_Sn : forall n,
n <=? (S n) = true.
Proof. hammer_hook "Lists" "Lists.NatList.leb_n_Sn".
intros n. induction n as [| n' IHn'].
-
simpl.  reflexivity.
-
simpl.  rewrite IHn'.  reflexivity.  Qed.



Theorem remove_does_not_increase_count: forall (s : bag),
(count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof. hammer_hook "Lists" "Lists.NatList.remove_does_not_increase_count".
Admitted.










Definition manual_grade_for_rev_injective : option (nat*string) := None.







Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
match l with
| nil => 42
| a :: l' => match n =? O with
| true => a
| false => nth_bad l' (pred n)
end
end.



Inductive natoption : Type :=
| Some (n : nat)
| None.



Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
match l with
| nil => None
| a :: l' => match n =? O with
| true => Some a
| false => nth_error l' (pred n)
end
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. hammer_hook "Lists" "Lists.NatList.test_nth_error1". reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. hammer_hook "Lists" "Lists.NatList.test_nth_error2". reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. hammer_hook "Lists" "Lists.NatList.test_nth_error3". reflexivity. Qed.



Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
match l with
| nil => None
| a :: l' => if n =? O then Some a
else nth_error' l' (pred n)
end.





Definition option_elim (d : nat) (o : natoption) : nat :=
match o with
| Some n' => n'
| None => d
end.



Definition hd_error (l : natlist) : natoption
. Admitted.

Example test_hd_error1 : hd_error [] = None.
Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Admitted.




Theorem option_elim_hd : forall (l:natlist) (default:nat),
hd default l = option_elim default (hd_error l).
Proof. hammer_hook "Lists" "Lists.NatList.option_elim_hd".
Admitted.


End NatList.








Inductive id : Type :=
| Id (n : nat).





Definition eqb_id (x1 x2 : id) :=
match x1, x2 with
| Id n1, Id n2 => n1 =? n2
end.


Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof. hammer_hook "Lists" "Lists.eqb_id_refl".
Admitted.




Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
| empty
| record (i : id) (v : nat) (m : partial_map).





Definition update (d : partial_map)
(x : id) (value : nat)
: partial_map :=
record x value d.



Fixpoint find (x : id) (d : partial_map) : natoption :=
match d with
| empty         => None
| record y v d' => if eqb_id x y
then Some v
else find x d'
end.


Theorem update_eq :
forall (d : partial_map) (x : id) (v: nat),
find x (update d x v) = Some v.
Proof. hammer_hook "Lists" "Lists.PartialMap.update_eq".
Admitted.



Theorem update_neq :
forall (d : partial_map) (x y : id) (o: nat),
eqb_id x y = false -> find x (update d y o) = find x d.
Proof. hammer_hook "Lists" "Lists.PartialMap.update_neq".
Admitted.

End PartialMap.



Inductive baz : Type :=
| Baz1 (x : baz)
| Baz2 (y : baz) (b : bool).






Definition manual_grade_for_baz_num_elts : option (nat*string) := None.



