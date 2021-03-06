From Hammer Require Import Hammer.





Require Import Coq.Strings.String.
From VFA Require Import Perm.
Require Import FunctionalExtensionality.






From VFA Require Import Maps.






Module SectionExample1.
Definition mymap (V: Type) := list (nat*V).
Definition empty (V: Type) : mymap V := nil.
Fixpoint lookup (V: Type) (default: V) (x: nat) (m: mymap V) : V :=
match m with
| (a,v)::al => if x =? a then v else lookup V default x al
| nil => default
end.
Theorem lookup_empty (V: Type) (default: V):
forall x, lookup V default x (empty V) = default.
Proof. hammer_hook "SearchTree" "SearchTree.SectionExample1.lookup_empty". reflexivity. Qed.
End SectionExample1.



Module SectionExample2.
Section MAPS.
Variable V : Type.
Variable default: V.

Definition mymap  := list (nat*V).
Definition empty : mymap := nil.
Fixpoint lookup (x: nat) (m: mymap) : V :=
match m with
| (a,v)::al => if x =? a then v else lookup x al
| nil => default
end.
Theorem lookup_empty:
forall x, lookup x empty = default.
Proof. hammer_hook "SearchTree" "SearchTree.SectionExample2.lookup_empty". reflexivity. Qed.
End MAPS.
End SectionExample2.



Goal SectionExample1.empty = SectionExample2.empty.
Proof. reflexivity.
Qed.

Goal SectionExample1.lookup = SectionExample2.lookup.
Proof.
unfold SectionExample1.lookup, SectionExample2.lookup.
try reflexivity.



extensionality V; extensionality default; extensionality x.
extensionality m; simpl.
induction m as [| [? ?] ]; auto.
destruct (x=?n); auto.
Qed.




Section TREES.
Variable V : Type.
Variable default: V.

Definition key := nat.

Inductive tree : Type :=
| E : tree
| T: tree -> key -> V -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : V :=
match t with
| E => default
| T tl k v tr => if x <? k then lookup x tl
else if k <? x then lookup x tr
else v
end.

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
match s with
| E => T E x v E
| T a y v' b => if  x <? y then T (insert x v a) y v' b
else if y <? x then T a y v' (insert x v b)
else T a x v b
end.

Fixpoint elements' (s: tree) (base: list (key*V)) : list (key * V) :=
match s with
| E => base
| T a k v b => elements' a ((k,v) :: elements' b base)
end.

Definition elements (s: tree) : list (key * V) := elements' s nil.




Section EXAMPLES.
Variables v2 v4 v5 : V.
Eval compute in insert 5 v5 (insert 2 v2 (insert 4 v5 empty_tree)).

Eval compute in lookup 5 (T (T E 2 v2 E) 4 v5 (T E 5 v5 E)).

Eval compute in lookup 3 (T (T E 2 v2 E) 4 v5 (T E 5 v5 E)).

Eval compute in elements (T (T E 2 v2 E) 4 v5 (T E 5 v5 E)).

End EXAMPLES.






Check t_update_eq.
Check t_update_neq.
Check t_update_shadow.
Check t_update_same.
Check t_update_permute.
Check t_apply_empty.













Definition example_tree (v2 v4 v5 : V) :=
T (T E 2 v2 E) 4 v4 (T E 5 v5 E).




Definition example_map (v2 v4 v5: V) : total_map V
. Admitted.




Definition combine {A} (pivot: key) (m1 m2: total_map A) : total_map A :=
fun x => if x <? pivot  then m1 x else m2 x.



Inductive Abs:  tree -> total_map V -> Prop :=
| Abs_E: Abs E (t_empty default)
| Abs_T: forall a b l k v r,
Abs l a ->
Abs r b ->
Abs (T l k v r)  (t_update (combine k a b) k v).




Lemma check_example_map:
forall v2 v4 v5, Abs (example_tree v2 v4 v5) (example_map v2 v4 v5).
Proof. hammer_hook "SearchTree" "SearchTree.check_example_map".
intros.
unfold example_tree.
evar (m: total_map V).
replace (example_map v2 v4 v5) with m; subst m.
repeat constructor.
extensionality x.

Admitted.



Lemma check_too_clever: forall v2 v4 v5: V, True.
Proof. hammer_hook "SearchTree" "SearchTree.check_too_clever".
intros.
evar (m: total_map V).
assert (Abs (example_tree v2 v4 v5) m).
repeat constructor.
(change m with (example_map v2 v4 v5) in H || auto);

fail "Did you use copy-and-paste, from your check_example_map proof,
into your example_map definition?  If so, very clever.
Please try it again with an example_map definition that
you make up from first principles.  Or, to skip that,
uncomment the (* auto; *) above.".
Qed.

Theorem empty_tree_relate: Abs empty_tree (t_empty default).
Proof. hammer_hook "SearchTree" "SearchTree.empty_tree_relate".
constructor.
Qed.


Theorem lookup_relate:
forall k t cts ,
Abs t cts -> lookup k t =  cts k.
Proof. hammer_hook "SearchTree" "SearchTree.lookup_relate".
Admitted.



Theorem insert_relate:
forall k v t cts,
Abs t cts ->
Abs (insert k v t) (t_update cts k v).
Proof. hammer_hook "SearchTree" "SearchTree.insert_relate".
Admitted.







Fixpoint list2map (el: list (key*V)) : total_map V :=
match el with
| nil => t_empty default
| (i,v)::el' => t_update (list2map el') i v
end.


Theorem elements_relate:
forall t cts,  Abs t cts -> list2map (elements t) = cts.
Proof. hammer_hook "SearchTree" "SearchTree.elements_relate".



Abort.

Definition manual_grade_for_elements_relate_informal : option (prod nat string) := None.





Theorem not_elements_relate:
forall v, v <> default ->
~ (forall t cts,  Abs t cts -> list2map (elements t) = cts).
Proof. hammer_hook "SearchTree" "SearchTree.not_elements_relate".
intros.
intro.
pose (bogus := T (T E 3 v E) 2 v E).
pose (m := t_update (t_empty default) 2 v).
pose (m' := t_update
(combine 2
(t_update (combine 3 (t_empty default) (t_empty default)) 3 v)
(t_empty default)) 2 v).
assert (Paradox: list2map (elements bogus) = m /\ list2map (elements bogus) <> m).
split.


Admitted.









Fixpoint forall_nodes (t: tree) (P: tree->key->V->tree->Prop) : Prop :=
match t with
| E => True
| T l k v r => P l k v r /\ forall_nodes l P /\ forall_nodes r P
end.

Definition SearchTreeX (t: tree) :=
forall_nodes t
(fun l k v r =>
forall_nodes l (fun _ j _ _ => j<k) /\
forall_nodes r (fun _ j _ _ => j>k)).

Lemma example_SearchTree_good:
forall v2 v4 v5, SearchTreeX (example_tree v2 v4 v5).
Proof. hammer_hook "SearchTree" "SearchTree.example_SearchTree_good".
intros.
hnf. simpl.
repeat split; auto.
Qed.

Lemma example_SearchTree_bad:
forall v, ~SearchTreeX (T (T E 3 v E) 2 v E).
Proof. hammer_hook "SearchTree" "SearchTree.example_SearchTree_bad".
intros.
intro.
hnf in H; simpl in H.
do 3 destruct H.
omega.
Qed.

Theorem elements_relate_second_attempt:
forall t cts,
SearchTreeX t ->
Abs t cts ->
list2map (elements t) = cts.
Proof. hammer_hook "SearchTree" "SearchTree.elements_relate_second_attempt".



Abort.

Inductive SearchTree' : key -> tree -> key -> Prop :=
| ST_E : forall lo hi, lo <= hi -> SearchTree' lo E hi
| ST_T: forall lo l k v r hi,
SearchTree' lo l k ->
SearchTree' (S k) r hi ->
SearchTree' lo (T l k v r) hi.

Inductive SearchTree: tree -> Prop :=
| ST_intro: forall t hi, SearchTree' 0 t hi -> SearchTree t.

Lemma SearchTree'_le:
forall lo t hi, @SearchTree' lo t hi -> lo <= hi.
Proof. hammer_hook "SearchTree" "SearchTree.SearchTree'_le".
induction 1; omega.
Qed.



Fixpoint slow_elements (s: tree) : list (key * V) :=
match s with
| E => nil
| T a k v b => slow_elements a ++ [(k,v)] ++ slow_elements b
end.




Theorem elements_slow_elements: elements = slow_elements.
Proof. hammer_hook "SearchTree" "SearchTree.elements_slow_elements".
extensionality s.
unfold elements.
assert (forall base, elements' s base = slow_elements s ++ base).
Admitted.




Lemma slow_elements_range:
forall k v lo t hi,
SearchTree' lo t hi ->
In (k,v) (slow_elements t) ->
lo <= k < hi.
Proof. hammer_hook "SearchTree" "SearchTree.slow_elements_range".
Admitted.






Lemma In_decidable:
forall (al: list (key*V)) (i: key),
(exists v, In (i,v) al) \/ (~exists v, In (i,v) al).
Proof. hammer_hook "SearchTree" "SearchTree.In_decidable".
intros.
induction al as [ | [k v]].
right; intros [w H]; inv H.
destruct IHal as [[w H] | H].
left; exists w; right; auto.
bdestruct (k =? i).
subst k.
left; eauto.
exists v; left; auto.
right. intros [w H1].
destruct H1. inv H1. omega.
apply H; eauto.
Qed.

Lemma list2map_app_left:
forall (al bl: list (key*V)) (i: key) v,
In (i,v) al -> list2map (al++bl) i = list2map al i.
Proof. hammer_hook "SearchTree" "SearchTree.list2map_app_left".
intros.
revert H; induction al as [| [j w] al]; intro; simpl; auto.
inv H.
destruct H. inv H.
unfold t_update.
bdestruct (i=?i); [ | omega].
auto.
unfold t_update.
bdestruct (j=?i); auto.
Qed.

Lemma list2map_app_right:
forall (al bl: list (key*V)) (i: key),
~(exists v, In (i,v) al) -> list2map (al++bl) i = list2map bl i.
Proof. hammer_hook "SearchTree" "SearchTree.list2map_app_right".
intros.
revert H; induction al as [| [j w] al]; intro; simpl; auto.
unfold t_update.
bdestruct (j=?i).
subst j.
contradiction H.
exists w; left; auto.
apply IHal.
contradict H.
destruct H as [u ?].
exists u; right; auto.
Qed.

Lemma list2map_not_in_default:
forall (al: list (key*V)) (i: key),
~(exists v, In (i,v) al) -> list2map al i = default.
Proof. hammer_hook "SearchTree" "SearchTree.list2map_not_in_default".
intros.
induction al as [| [j w] al].
reflexivity.
simpl.
unfold t_update.
bdestruct (j=?i).
subst.
contradiction H.
exists w; left; auto.
apply IHal.
intros [v ?].
apply H. exists v; right; auto.
Qed.


Theorem elements_relate:
forall t cts,
SearchTree t ->
Abs t cts ->
list2map (elements t) = cts.
Proof. hammer_hook "SearchTree" "SearchTree.elements_relate".
rewrite elements_slow_elements.
intros until 1. inv H.
revert cts; induction H0; intros.
*
inv H0.
reflexivity.
*
inv H.
specialize (IHSearchTree'1 _ H5). clear H5.
specialize (IHSearchTree'2 _ H6). clear H6.
unfold slow_elements; fold slow_elements.
subst.
extensionality i.
destruct (In_decidable (slow_elements l) i)  as [[w H] | Hleft].
rewrite list2map_app_left with (v:=w); auto.
pose proof (slow_elements_range _ _ _ _ _ H0_ H).
unfold combine, t_update.
bdestruct (k=?i); [ omega | ].
bdestruct (i<?k); [ | omega].
auto.
Admitted.








Theorem empty_tree_SearchTree:  SearchTree empty_tree.
Proof. hammer_hook "SearchTree" "SearchTree.empty_tree_SearchTree".
clear default.
Admitted.



Theorem insert_SearchTree:
forall k v t,
SearchTree t -> SearchTree (insert k v t).
Proof. hammer_hook "SearchTree" "SearchTree.insert_SearchTree".
clear default.
Admitted.







Check lookup_relate.




Check elements_relate.




Lemma lookup_relate':
forall (k : key) (t : tree) (cts : total_map V),
SearchTree t -> Abs t cts -> lookup k t = cts k.



Proof. hammer_hook "SearchTree" "SearchTree.lookup_relate'".
intros.
apply lookup_relate.
apply H0.
Qed.

Theorem insert_relate':
forall k v t cts,
SearchTree t ->
Abs t cts ->
Abs (insert k v t) (t_update cts k v).
Proof. hammer_hook "SearchTree" "SearchTree.insert_relate'". intros. apply insert_relate; auto.
Qed.



Print Abs.



Remark abstraction_of_bogus_tree:
forall v2 v3,
Abs (T (T E 3 v3 E) 2 v2 E) (t_update (t_empty default) 2 v2).
Proof. hammer_hook "SearchTree" "SearchTree.abstraction_of_bogus_tree".
intros.
evar (m: total_map V).
replace  (t_update (t_empty default) 2 v2) with m; subst m.
repeat constructor.
extensionality x.
unfold t_update, combine, t_empty.
bdestruct (2 =? x).
auto.
bdestruct (x <? 2).
bdestruct (3 =? x).

omega.
bdestruct (x <? 3).
auto.
auto.
auto.
Qed.









Lemma can_relate:
forall t,  SearchTree t -> exists cts, Abs t cts.
Proof. hammer_hook "SearchTree" "SearchTree.can_relate".
Admitted.





Lemma unrealistically_strong_can_relate:
forall t,  exists cts, Abs t cts.
Proof. hammer_hook "SearchTree" "SearchTree.unrealistically_strong_can_relate".
Admitted.







Definition AbsX (t: tree) (m: total_map V) : Prop :=
list2map (elements t) = m.



Theorem elements_relateX:
forall t cts,
SearchTree t ->
AbsX t cts ->
list2map (elements t) = cts.
Proof. hammer_hook "SearchTree" "SearchTree.elements_relateX".
intros.
apply H0.
Qed.



Theorem naive_lookup_relateX:
forall k t cts ,
AbsX t cts -> lookup k t =  cts k.
Abort.



Theorem not_naive_lookup_relateX:
forall v, default <> v ->
~ (forall k t cts , AbsX t cts -> lookup k t =  cts k).
Proof. hammer_hook "SearchTree" "SearchTree.not_naive_lookup_relateX".
unfold AbsX.
intros v H.
intros H0.
pose (bogus := T (T E 3 v E) 2 v E).
pose (m := t_update (t_update (t_empty default) 2 v) 3 v).
assert (list2map (elements bogus) = m).
reflexivity.
assert (~ lookup 3 bogus = m 3). {
unfold bogus, m, t_update, t_empty.
simpl.
apply H.
}

apply H2.
apply H0.
apply H1.
Qed.


Theorem lookup_relateX:
forall k t cts ,
SearchTree t -> AbsX t cts -> lookup k t =  cts k.
Proof. hammer_hook "SearchTree" "SearchTree.lookup_relateX".
intros.
unfold AbsX in H0. subst cts.
inv H. remember 0 as lo in H0.
clear - H0.
rewrite elements_slow_elements.


Admitted.






End TREES.
