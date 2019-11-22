From Hammer Require Import Hammer.











Require Import Coq.Strings.String.
From VFA Require Import Perm.
From VFA Require Import Maps.
Import FunctionalExtensionality.

Module VerySlow.

Fixpoint loop (input: list nat) (c: nat) (table: total_map bool) : nat :=
match input with
| nil => c
| a::al => if table a
then loop al (c+1) table
else loop al c (t_update table a true)
end.

Definition collisions (input: list nat) : nat :=
loop input 0 (t_empty false).

Example collisions_pi: collisions [3;1;4;1;5;9;2;6] = 1.
Proof. hammer_hook "Trie" "Trie.VerySlow.collisions_pi". reflexivity. Qed.



Print beq_nat.




End VerySlow.





Module Integers.



Inductive positive : Set :=
| xI : positive -> positive
| xO : positive -> positive
| xH : positive.



Definition ten := xO (xI (xO xH)).



Fixpoint positive2nat (p: positive) : nat :=
match p with
| xI q => 1 + 2 * positive2nat q
| xO q => 0 + 2 * positive2nat q
| xH => 1
end.

Eval compute in positive2nat ten.



Fixpoint print_in_binary (p: positive) : list nat :=
match p with
| xI q => print_in_binary q ++ [1]
| xO q =>print_in_binary q ++ [0]
| xH => [1]
end.

Eval compute in print_in_binary ten.



Notation "p ~ 1" := (xI p)
(at level 7, left associativity, format "p '~' '1'").
Notation "p ~ 0" := (xO p)
(at level 7, left associativity, format "p '~' '0'").

Print ten.





Fixpoint succ x :=
match x with
| p~1 => (succ p)~0
| p~0 => p~1
| xH => xH~0
end.



Fixpoint addc (carry: bool) (x y: positive) {struct x} : positive :=
match carry, x, y with
| false, p~1, q~1 => (addc true p q)~0
| false, p~1, q~0 => (addc false p q)~1
| false, p~1, xH => (succ p)~0
| false, p~0, q~1 => (addc false p q)~1
| false, p~0, q~0 => (addc false p q)~0
| false, p~0, xH => p~1
| false, xH, q~1 => (succ q)~0
| false, xH, q~0 => q~1
| false, xH, xH => xH~0
| true, p~1, q~1 => (addc true p q)~1
| true, p~1, q~0 => (addc true p q)~0
| true, p~1, xH => (succ p)~1
| true, p~0, q~1 => (addc true p q)~0
| true, p~0, q~0 => (addc false p q)~1
| true, p~0, xH => (succ p)~0
| true, xH, q~1 => (succ q)~1
| true, xH, q~0 => (succ q)~0
| true, xH, xH => xH~1
end.

Definition add (x y: positive) : positive := addc false x y.


Lemma succ_correct: forall p,
positive2nat (succ p) = S (positive2nat p).
Proof. hammer_hook "Trie" "Trie.Integers.succ_correct".
Admitted.





Lemma addc_correct: forall (c: bool) (p q: positive),
positive2nat (addc c p q) =
(if c then 1 else 0) + positive2nat p + positive2nat q.
Proof. hammer_hook "Trie" "Trie.Integers.addc_correct".
Admitted.

Theorem add_correct: forall (p q: positive),
positive2nat (add p q) = positive2nat p + positive2nat q.
Proof. hammer_hook "Trie" "Trie.Integers.add_correct".
intros.
unfold add.
apply addc_correct.
Qed.






Inductive comparison : Set :=
Eq : comparison | Lt : comparison | Gt : comparison.


Fixpoint compare x y {struct x}:=
match x, y with
| p~1, q~1 => compare p q
| p~1, q~0 => match compare p q with Lt => Lt | _ => Gt end
| p~1, xH => Gt


| _, _ => Lt
end.

Lemma positive2nat_pos:
forall p, positive2nat p > 0.
Proof. hammer_hook "Trie" "Trie.Integers.positive2nat_pos".
intros.
induction p; simpl; omega.
Qed.

Theorem compare_correct:
forall x y,
match compare x y with
| Lt => positive2nat x < positive2nat y
| Eq => positive2nat x = positive2nat y
| Gt => positive2nat x > positive2nat y
end.
Proof. hammer_hook "Trie" "Trie.Integers.compare_correct".
induction x; destruct y; simpl.
Admitted.








Inductive Z : Set :=
| Z0 : Z
| Zpos : positive -> Z
| Zneg : positive -> Z.



End Integers.



Print positive.

Check Pos.compare.
Check Pos.add.

Check Z.add.






Module RatherSlow.

Definition total_mapz (A: Type) := Z -> A.

Definition empty {A:Type} (default: A) : total_mapz A := fun _ => default.
Definition update {A:Type} (m : total_mapz A)
(x : Z) (v : A) :=
fun x' => if Z.eqb x x' then v else m x'.

Fixpoint loop (input: list Z) (c: Z) (table: total_mapz bool) : Z :=
match input with
| nil => c
| a::al => if table a
then loop al (c+1) table
else loop al c (update table a true)
end.

Definition collisions (input: list Z) := loop input 0 (empty false).

Example collisions_pi: collisions [3;1;4;1;5;9;2;6]%Z = 1%Z.
Proof. hammer_hook "Trie" "Trie.RatherSlow.collisions_pi". reflexivity. Qed.

End RatherSlow.











Print positive.


Goal   10%positive = xO (xI (xO xH)).
Proof. hammer_hook "Trie" "Trie.FastEnough.collisions_pi". reflexivity. Qed.



Inductive trie (A : Type) :=
| Leaf : trie A
| Node : trie A -> A -> trie A -> trie A.
Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Definition trie_table (A: Type) : Type := (A * trie A)%type.

Definition empty {A: Type} (default: A) : trie_table A :=
(default, Leaf).

Fixpoint look {A: Type} (default: A) (i: positive) (m: trie A): A :=
match m with
| Leaf => default
| Node l x r =>
match i with
| xH => x
| xO i' => look default i' l
| xI i' => look default i' r
end
end.

Definition lookup {A: Type} (i: positive) (t: trie_table A) : A :=
look (fst t) i (snd t).

Fixpoint ins {A: Type} default (i: positive) (a: A) (m: trie A): trie A :=
match m with
| Leaf =>
match i with
| xH => Node Leaf a Leaf
| xO i' => Node (ins default i' a Leaf) default Leaf
| xI i' => Node Leaf default (ins default i' a Leaf)
end
| Node l o r =>
match i with
| xH => Node l a r
| xO i' => Node (ins default i' a l) o r
| xI i' => Node l o (ins default i' a r)
end
end.

Definition insert {A: Type} (i: positive) (a: A) (t: trie_table A)
: trie_table A :=
(fst t, ins (fst t) i a (snd t)).

Definition three_ten : trie_table bool :=
insert 3 true (insert 10 true (empty false)).

Eval compute in three_ten.


Eval compute in
map (fun i => lookup i three_ten) [3;1;4;1;5]%positive.





Module FastEnough.

Fixpoint loop (input: list positive) (c: nat) (table: trie_table bool) : nat :=
match input with
| nil => c
| a::al => if lookup a table
then loop al (1+c) table
else loop al c (insert a true table)
end.

Definition collisions (input: list positive) := loop input 0 (empty false).

Example collisions_pi: collisions [3;1;4;1;5;9;2;6]%positive = 1.
Proof. reflexivity. Qed.

End FastEnough.








Definition manual_grade_for_successor_of_Z_constant_time : option (prod nat string) := None.











Lemma look_leaf:
forall A (a:A) j, look a j Leaf = a.
Admitted.





Lemma look_ins_same: forall {A} a k (v:A) t, look a k (ins a k v t) = v.
Admitted.






Lemma look_ins_other: forall {A} a j k (v:A) t,
j <> k -> look a j (ins a k v t) = look a j t.
Admitted.







Definition nat2pos (n: nat) : positive := Pos.of_succ_nat n.
Definition pos2nat (n: positive) : nat := pred (Pos.to_nat n).

Lemma pos2nat2pos: forall p, nat2pos (pos2nat p) = p.
Proof. hammer_hook "Trie" "Trie.pos2nat2pos".
intro. unfold nat2pos, pos2nat.
rewrite <- (Pos2Nat.id p) at 2.
destruct (Pos.to_nat p) eqn:?.
pose proof (Pos2Nat.is_pos p). omega.
rewrite <- Pos.of_nat_succ.
reflexivity.
Qed.

Lemma nat2pos2nat: forall i, pos2nat (nat2pos i) = i.
Proof. hammer_hook "Trie" "Trie.nat2pos2nat".
intro. unfold nat2pos, pos2nat.
rewrite SuccNat2Pos.id_succ.
reflexivity.
Qed.




Lemma pos2nat_injective: forall p q, pos2nat p = pos2nat q -> p=q.
Admitted.

Lemma nat2pos_injective: forall i j, nat2pos i = nat2pos j -> i=j.
Admitted.







Definition is_trie {A: Type} (t: trie_table A) : Prop
. Admitted.



Definition abstract {A: Type} (t: trie_table A) (n: nat) : A :=
lookup (nat2pos n) t.

Definition Abs {A: Type} (t: trie_table A) (m: total_map A) :=
abstract t = m.




Theorem empty_is_trie: forall {A} (default: A), is_trie (empty default).
Admitted.

Theorem insert_is_trie: forall {A} i x (t: trie_table A),
is_trie t -> is_trie (insert i x t).
Admitted.





Theorem empty_relate: forall {A} (default: A),
Abs (empty default) (t_empty default).
Proof. hammer_hook "Trie" "Trie.empty_relate".
Admitted.






Theorem lookup_relate: forall {A} i (t: trie_table A) m,
is_trie t -> Abs t m -> lookup i t = m (pos2nat i).
Admitted.





Theorem insert_relate: forall {A} k (v: A) t cts,
is_trie t ->
Abs t cts ->
Abs (insert k v t) (t_update cts (pos2nat k) v).
Admitted.





Example Abs_three_ten:
Abs
(insert 3 true (insert 10 true (empty false)))
(t_update (t_update (t_empty false) (pos2nat 10) true) (pos2nat 3) true).
Proof. hammer_hook "Trie" "Trie.Abs_three_ten".
try (apply insert_relate; [hnf; auto | ]).
try (apply insert_relate; [hnf; auto | ]).
try (apply empty_relate).

Admitted.




