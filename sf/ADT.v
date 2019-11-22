From Hammer Require Import Hammer.



Require Import Omega.



Module Type TABLE.
Parameter V: Type.
Parameter default: V.
Parameter table: Type.
Definition key := nat.
Parameter empty: table.
Parameter get: key -> table -> V.
Parameter set: key -> V -> table -> table.
Axiom gempty: forall k,
get k empty = default.
Axiom gss: forall k v t,
get k (set k v t) = v.
Axiom gso: forall j k v t,
j <> k -> get j (set k v t) = get j t.
End TABLE.



From VFA Require Import Maps.

Module MapsTable <: TABLE.
Definition V := Type.
Definition default: V := Prop.
Definition table := total_map V.
Definition key := nat.
Definition empty : table := t_empty default.
Definition get (k: key) (m: table) : V := m k.
Definition set (k: key) (v: V) (m: table) : table :=
t_update m k v.
Theorem gempty: forall k, get k empty = default.
Proof. hammer_hook "ADT" "ADT.TABLE.gempty". intros. reflexivity. Qed.
Theorem gss: forall k v t,  get k (set k v t) = v.
Proof. hammer_hook "ADT" "ADT.TABLE.gss". intros. unfold get, set. apply t_update_eq. Qed.
Theorem gso: forall j k v t, j<>k -> get j (set k v t) = get j t.
Proof. hammer_hook "ADT" "ADT.TABLE.gso". intros. unfold get, set. apply t_update_neq.
congruence.
Qed.
End MapsTable.





Eval compute in MapsTable.get 1 (MapsTable.set 3 unit (MapsTable.set 1 bool MapsTable.empty)).






From VFA Require Import SearchTree.

Module TreeTable <: TABLE.
Definition V := Type.
Definition default : V := Prop.
Definition table := tree V.
Definition key := nat.
Definition empty : table := empty_tree V.
Definition get (k: key) (m: table) : V := lookup V default k m.
Definition set (k: key) (v: V) (m: table) : table :=
insert V k v m.
Theorem gempty: forall k, get k empty = default.
Proof. hammer_hook "ADT" "ADT.MapsTable.gempty". intros. reflexivity. Qed.

Theorem gss: forall k v t,  get k (set k v t) = v.
Proof. hammer_hook "ADT" "ADT.MapsTable.gss". intros. unfold get, set.
destruct (unrealistically_strong_can_relate V default t)
as [cts H].
assert (H0 := insert_relate V default k v t cts H).
assert (H1 := lookup_relate V default k _ _ H0).
rewrite H1. apply t_update_eq.
Qed.




Theorem gso: forall j k v t,  j<>k -> get j (set k v t) = get j t.
Proof. hammer_hook "ADT" "ADT.MapsTable.gso".
Admitted.

End TreeTable.



Check can_relate.








Check exist.
Check proj1_sig.
Check proj2_sig.



Module TreeTable2 <: TABLE.
Definition V := Type.
Definition default : V := Prop.
Definition table := {x | SearchTree V x}.
Definition key := nat.
Definition empty : table :=
exist (SearchTree V) (empty_tree V) (empty_tree_SearchTree V).
Definition get (k: key) (m: table) : V :=
(lookup V default k (proj1_sig m)).
Definition set (k: key) (v: V) (m: table) : table :=
exist (SearchTree V) (insert V k v (proj1_sig m))
(insert_SearchTree _ _ _ _ (proj2_sig m)).

Theorem gempty: forall k, get k empty = default.
Proof. hammer_hook "ADT" "ADT.TreeTable.gempty". intros. reflexivity. Qed.

Theorem gss: forall k v t,  get k (set k v t) = v.
Proof. hammer_hook "ADT" "ADT.TreeTable.gss". intros. unfold get, set.
unfold table in t.



destruct t as [a Ha].

simpl.

destruct (can_relate V default a Ha) as [cts H].
pose proof (insert_relate V default k v a cts H).
pose proof (lookup_relate V default k _ _ H0).
rewrite H1. apply t_update_eq.
Qed.




Theorem gso: forall j k v t,  j<>k -> get j (set k v t) = get j t.
Proof. hammer_hook "ADT" "ADT.TreeTable.gso".
Admitted.

End TreeTable2.






Section ADT_SUMMARY.
Variable V: Type.
Variable default: V.



Check (empty_tree_SearchTree V).

Check (insert_SearchTree V).




Check (Abs V default).



Check (empty_tree_relate V default).
Check (lookup_relate' V default).
Check (insert_relate' V default).



Check TreeTable2.gso.

End ADT_SUMMARY.






Require Import List.
Import ListNotations.



Fixpoint fibonacci (n: nat) :=
match n with
| 0 => 1
| S i => match i with 0 => 1 | S j => fibonacci i + fibonacci j end
end.

Eval compute in map fibonacci [0;1;2;3;4;5;6].



Fixpoint repeat {A} (f: A->A) (x: A) n :=
match n with O => x | S n' => f (repeat f x n') end.

Definition step (al: list nat) : list nat :=
List.cons (nth 0 al 0 + nth 1 al 0) al.

Eval compute in map (repeat step [1;0;0]) [0;1;2;3;4;5].

Definition fib n := nth 0 (repeat step [1;0;0] n) 0.

Eval compute in map fib [0;1;2;3;4;5;6].



Module Type LISTISH.
Parameter list: Type.
Parameter create : nat -> nat -> nat -> list.
Parameter cons: nat -> list -> list.
Parameter nth: nat -> list -> nat.
End LISTISH.

Module L <: LISTISH.
Definition list := (nat*nat*nat)%type.
Definition create (a b c: nat) : list := (a,b,c).
Definition cons (i: nat) (il : list) := match il with (a,b,c) => (i,a,b) end.
Definition nth (n: nat) (al: list) :=
match al with (a,b,c) =>
match n with 0 => a | 1 => b | 2 => c | _ => 0 end
end.
End L.

Definition sixlist := L.cons 0 (L.cons 1 (L.cons 2 (L.create 3 4 5))).

Eval compute in map (fun i => L.nth i sixlist) [0;1;2;3;4;5;6;7].



Definition stepish (al: L.list) : L.list :=
L.cons (L.nth 0 al + L.nth 1 al) al.

Eval compute in map (repeat stepish (L.create 1 0 0)) [0;1;2;3;4;5].

Definition fibish n := L.nth 0 (repeat stepish  (L.create 1 0 0) n).

Eval compute in map fibish [0;1;2;3;4;5;6].



Lemma nth_firstn:
forall A d i j (al: list A), i<j -> nth i (firstn j al) d = nth i al d.
Proof. hammer_hook "ADT" "ADT.nth_firstn".
induction i; destruct j,al; simpl; intros; auto; try omega.
apply IHi. omega.
Qed.




Inductive L_Abs: L.list -> List.list nat -> Prop :=

.

Definition O_Abs al al' := L_Abs al al'.


Lemma create_relate : True.
Admitted.

Lemma cons_relate : True.
Admitted.

Lemma nth_relate : True.
Admitted.



Opaque L.list.
Opaque L.create.
Opaque L.cons.
Opaque L.nth.
Opaque O_Abs.

Lemma step_relate:
forall al al',
O_Abs al al' ->
O_Abs (stepish al) (step al').
Proof. hammer_hook "ADT" "ADT.step_relate".
Admitted.

Lemma repeat_step_relate:
forall n al al',
O_Abs al al' ->
O_Abs (repeat stepish al n) (repeat step al' n).
Proof. hammer_hook "ADT" "ADT.repeat_step_relate".
Admitted.

Lemma fibish_correct: forall n, fibish n = fib n.
Proof. hammer_hook "ADT" "ADT.fibish_correct".
Admitted.














