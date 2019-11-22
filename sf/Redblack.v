From Hammer Require Import Hammer.












From VFA Require Import Perm.
From VFA Require Import Extract.
Require Import Coq.Lists.List.
Export ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ZArith.
Open Scope Z_scope.

Definition key := int.

Inductive color := Red | Black.

Section TREES.
Variable V : Type.
Variable default: V.

Inductive tree  : Type :=
| E : tree
| T: color -> tree -> key -> V -> tree -> tree.

Definition empty_tree := E.



Fixpoint lookup (x: key) (t : tree) : V :=
match t with
| E => default
| T _ tl k v tr => if ltb x k then lookup x tl
else if ltb k x then lookup x tr
else v
end.



Definition balance rb t1 k vk t2 :=
match rb with Red => T Red t1 k vk t2
| _ =>
match t1 with
| T Red (T Red a x vx b) y vy c =>
T Red (T Black a x vx b) y vy (T Black c k vk t2)
| T Red a x vx (T Red b y vy c) =>
T Red (T Black a x vx b) y vy (T Black c k vk t2)
| a => match t2 with
| T Red (T Red b y vy c) z vz d =>
T Red (T Black t1 k vk b) y vy (T Black c z vz d)
| T Red b y vy (T Red c z vz d)  =>
T Red (T Black t1 k vk b) y vy (T Black c z vz d)
| _ => T Black t1 k vk t2
end
end
end.

Definition makeBlack t :=
match t with
| E => E
| T _ a x vx b => T Black a x vx b
end.

Fixpoint ins x vx s :=
match s with
| E => T Red E x vx E
| T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
else if ltb y x then balance c a y vy (ins x vx b)
else T c a x vx b
end.

Definition insert x vx s := makeBlack (ins x vx s).






Lemma T_neq_E:
forall c l k v r, T c l k v r <> E.
Proof. hammer_hook "Redblack" "Redblack.T_neq_E".
intros. intro Hx. inversion Hx.
Qed.



Lemma ins_not_E: forall x vx s, ins x vx s <> E.
Proof. hammer_hook "Redblack" "Redblack.ins_not_E".
intros. destruct s; simpl.
apply T_neq_E.
remember (ins x vx s1) as a1.
unfold balance.



destruct (ltb x k).

destruct c.

apply T_neq_E.

destruct a1.

destruct s2.

intro Hx; inversion Hx.



match goal with
| |- match ?c with Red => _ | Black => _  end <> _=> destruct c
end.



match goal with
| |- match ?s with E => _ | T _ _ _ _ _ => _ end  <> _=>destruct s
end.



repeat match goal with
| |- match ?s with E => _ | T _ _ _ _ _ => _ end  <> _=>destruct s
end.
match goal with
| |- T _ _ _ _ _ <> E => apply T_neq_E
end.



Abort.

Lemma ins_not_E: forall x vx s, ins x vx s <> E.
Proof. hammer_hook "Redblack" "Redblack.ins_not_E".
intros. destruct s; simpl.
apply T_neq_E.
remember (ins x vx s1) as a1.
unfold balance.



repeat match goal with
| |- (if ?x then _ else _) <> _ => destruct x
| |- match ?c with Red => _ | Black => _  end <> _=> destruct c
| |- match ?s with E => _ | T _ _ _ _ _ => _ end  <> _=>destruct s
end.



apply T_neq_E.
apply T_neq_E.
apply T_neq_E.
apply T_neq_E.
apply T_neq_E.
apply T_neq_E.

apply T_neq_E.
apply T_neq_E.
apply T_neq_E.
apply T_neq_E.

Abort.

Lemma ins_not_E: forall x vx s, ins x vx s <> E.
Proof. hammer_hook "Redblack" "Redblack.ins_not_E".
intros. destruct s; simpl.
apply T_neq_E.
remember (ins x vx s1) as a1.
unfold balance.



repeat match goal with
| |- (if ?x then _ else _) <> _ => destruct x
| |- match ?c with Red => _ | Black => _  end <> _=> destruct c
| |- match ?s with E => _ | T _ _ _ _ _ => _ end  <> _=>destruct s
| |- T _ _ _ _ _ <> E => apply T_neq_E
end.
Qed.






Inductive SearchTree' : Z -> tree -> Z -> Prop :=
| ST_E : forall lo hi, lo <= hi -> SearchTree' lo E hi
| ST_T: forall lo c l k v r hi,
SearchTree' lo l (int2Z k) ->
SearchTree' (int2Z k + 1) r hi ->
SearchTree' lo (T c l k v r) hi.

Inductive SearchTree: tree -> Prop :=
| ST_intro: forall t lo hi, SearchTree' lo t hi -> SearchTree t.


Lemma balance_SearchTree:
forall c  s1 k kv s2 lo hi,
SearchTree' lo s1 (int2Z k) ->
SearchTree' (int2Z k + 1) s2 hi ->
SearchTree' lo (balance c s1 k kv s2) hi.
Proof. hammer_hook "Redblack" "Redblack.balance_SearchTree".
intros.
unfold balance.



repeat  match goal with
|  |- SearchTree' _ (match ?c with Red => _ | Black => _ end) _ => destruct c
|  |- SearchTree' _ (match ?s with E => _ | T _ _ _ _ _ => _ end) _ => destruct s
end.



* constructor; auto.
* constructor; auto.
* constructor; auto.
* constructor; auto.
constructor; auto. constructor; auto.

inv H. inv H0. inv H8. inv H9.
auto.
constructor; auto.
inv H. inv H0. inv H8. inv H9. auto.
inv H. inv H0. inv H8. inv H9. auto.



Abort.

Lemma balance_SearchTree:
forall c  s1 k kv s2 lo hi,
SearchTree' lo s1 (int2Z k) ->
SearchTree' (int2Z k + 1) s2 hi ->
SearchTree' lo (balance c s1 k kv s2) hi.
Proof. hammer_hook "Redblack" "Redblack.balance_SearchTree".
intros.
unfold balance.



repeat  match goal with
| |- SearchTree' _ (match ?c with Red => _ | Black => _ end) _ =>
destruct c
| |- SearchTree' _ (match ?s with E => _ | T _ _ _ _ _ => _ end) _ =>
destruct s
| H: SearchTree' _ E _   |- _  => inv H
| H: SearchTree' _ (T _ _ _ _ _) _   |- _  => inv H
end.


* constructor; auto.
* constructor; auto. constructor; auto. constructor; auto.
* constructor; auto. constructor; auto. constructor; auto. constructor; auto. constructor; auto.
* constructor; auto. constructor; auto. constructor; auto. constructor; auto. constructor; auto.
* constructor; auto. constructor; auto. constructor; auto. constructor; auto. constructor; auto.



Abort.

Lemma balance_SearchTree:
forall c  s1 k kv s2 lo hi,
SearchTree' lo s1 (int2Z k) ->
SearchTree' (int2Z k + 1) s2 hi ->
SearchTree' lo (balance c s1 k kv s2) hi.
Proof. hammer_hook "Redblack" "Redblack.balance_SearchTree".
intros.
unfold balance.



repeat  match goal with
| |- SearchTree' _ (match ?c with Red => _ | Black => _ end) _ =>
destruct c
| |- SearchTree' _ (match ?s with E => _ | T _ _ _ _ _ => _ end) _ =>
destruct s
| H: SearchTree' _ E _   |- _  => inv H
| H: SearchTree' _ (T _ _ _ _ _) _   |- _  => inv H
end;
repeat (constructor; auto).
Qed.



Lemma ins_SearchTree:
forall x vx s lo hi,
lo <= int2Z x ->
int2Z x < hi ->
SearchTree' lo s hi ->
SearchTree' lo (ins x vx s) hi.
Proof. hammer_hook "Redblack" "Redblack.ins_SearchTree".
Admitted.




Lemma empty_tree_SearchTree: SearchTree empty_tree.
Admitted.

Lemma SearchTree'_le:
forall lo t hi, SearchTree' lo t hi -> lo <= hi.
Proof. hammer_hook "Redblack" "Redblack.SearchTree'_le".
induction 1; omega.
Qed.

Lemma expand_range_SearchTree':
forall s lo hi,
SearchTree' lo s hi ->
forall lo' hi',
lo' <= lo -> hi <= hi' ->
SearchTree' lo' s hi'.
Proof. hammer_hook "Redblack" "Redblack.expand_range_SearchTree'".
induction 1; intros.
constructor.
omega.
constructor.
apply IHSearchTree'1; omega.
apply IHSearchTree'2; omega.
Qed.

Lemma insert_SearchTree: forall x vx s,
SearchTree s -> SearchTree (insert x vx s).
Admitted.


Import IntMaps.

Definition combine {A} (pivot: Z) (m1 m2: total_map A) : total_map A :=
fun x => if Z.ltb x pivot  then m1 x else m2 x.

Inductive Abs:  tree -> total_map V -> Prop :=
| Abs_E: Abs E (t_empty default)
| Abs_T: forall a b c l k vk r,
Abs l a ->
Abs r b ->
Abs (T c l k vk r)  (t_update (combine (int2Z k) a b) (int2Z k) vk).

Theorem empty_tree_relate: Abs empty_tree (t_empty default).
Proof. hammer_hook "Redblack" "Redblack.empty_tree_relate".
constructor.
Qed.


Theorem lookup_relate:
forall k t cts ,   Abs t cts -> lookup k t =  cts (int2Z k).
Proof. hammer_hook "Redblack" "Redblack.lookup_relate".
Admitted.


Lemma Abs_helper:
forall m' t m, Abs t m' ->    m' = m ->     Abs t m.
Proof. hammer_hook "Redblack" "Redblack.Abs_helper".
intros. subst. auto.
Qed.

Ltac contents_equivalent_prover :=
extensionality x; unfold t_update, combine, t_empty;
repeat match goal with
| |- context [if ?A then _ else _] => bdestruct A
end;
auto;
omega.




Theorem balance_relate:
forall c l k vk r m,
SearchTree (T c l k vk r) ->
Abs (T c l k vk r) m ->
Abs (balance c l k vk r) m.
Proof. hammer_hook "Redblack" "Redblack.balance_relate".
intros.
inv H.
unfold balance.
repeat match goal with
| H: Abs E _ |- _ => inv H
end.


Admitted.



Definition how_many_subgoals_remaining :=
[1; 1; 1; 1; 1; 2

].



Theorem ins_relate:
forall k v t cts,
SearchTree t ->
Abs t cts ->
Abs (ins k v t) (t_update cts (int2Z k) v).
Proof. hammer_hook "Redblack" "Redblack.ins_relate".
Admitted.


Lemma makeBlack_relate:
forall t cts,
Abs t cts ->
Abs (makeBlack t) cts.
Proof. hammer_hook "Redblack" "Redblack.makeBlack_relate".
intros.
destruct t; simpl; auto.
inv H; constructor; auto.
Qed.

Theorem insert_relate:
forall k v t cts,
SearchTree t ->
Abs t cts ->
Abs (insert k v t) (t_update cts (int2Z k) v).
Proof. hammer_hook "Redblack" "Redblack.insert_relate".
intros.
unfold insert.
apply makeBlack_relate.
apply ins_relate; auto.
Qed.



Check empty_tree_SearchTree.
Check empty_tree_relate.
Check lookup_relate.
Check insert_SearchTree.
Check insert_relate.






Fixpoint elements' (s: tree) (base: list (key*V)) : list (key * V) :=
match s with
| E => base
| T _ a k v b => elements' a ((k,v) :: elements' b base)
end.

Definition elements (s: tree) : list (key * V) := elements' s nil.

Definition elements_property (t: tree) (cts: total_map V) : Prop :=
forall k v,
(In (k,v) (elements t) -> cts (int2Z k) = v) /\
(cts (int2Z k) <> default ->
exists k', int2Z k = int2Z k' /\ In (k', cts (int2Z k)) (elements t)).

Theorem elements_relate:
forall t cts,
SearchTree t ->
Abs t cts ->
elements_property t cts.
Proof. hammer_hook "Redblack" "Redblack.elements_relate".
Admitted.










Inductive is_redblack : tree -> color -> nat -> Prop :=
| IsRB_leaf: forall c, is_redblack E c 0
| IsRB_r: forall tl k kv tr n,
is_redblack tl Red n ->
is_redblack tr Red n ->
is_redblack (T Red tl k kv tr) Black n
| IsRB_b: forall c tl k kv tr n,
is_redblack tl Black n ->
is_redblack tr Black n ->
is_redblack (T Black tl k kv tr) c (S n).

Lemma is_redblack_toblack:
forall s n, is_redblack s Red n -> is_redblack s Black n.
Proof. hammer_hook "Redblack" "Redblack.is_redblack_toblack".
Admitted.

Lemma makeblack_fiddle:
forall s n, is_redblack s Black n ->
exists n, is_redblack (makeBlack s) Red n.
Proof. hammer_hook "Redblack" "Redblack.makeblack_fiddle".
Admitted.



Inductive nearly_redblack : tree -> nat -> Prop :=
| nrRB_r: forall tl k kv tr n,
is_redblack tl Black n ->
is_redblack tr Black n ->
nearly_redblack (T Red tl k kv tr) n
| nrRB_b: forall tl k kv tr n,
is_redblack tl Black n ->
is_redblack tr Black n ->
nearly_redblack (T Black tl k kv tr) (S n).


Lemma ins_is_redblack:
forall x vx s n,
(is_redblack s Black n -> nearly_redblack (ins x vx s) n) /\
(is_redblack s Red n -> is_redblack (ins x vx s) Black n).
Proof. hammer_hook "Redblack" "Redblack.ins_is_redblack".
induction s; intro n; simpl; split; intros; inv H; repeat constructor; auto.
*
destruct (IHs1 n); clear IHs1.
destruct (IHs2 n); clear IHs2.
specialize (H0 H6).
specialize (H2 H7).
clear H H1.
unfold balance.



Admitted.

Lemma insert_is_redblack:
forall x xv s n, is_redblack s Red n ->
exists n', is_redblack (insert x xv s) Red n'.
Proof. hammer_hook "Redblack" "Redblack.insert_is_redblack".

Admitted.


End TREES.
