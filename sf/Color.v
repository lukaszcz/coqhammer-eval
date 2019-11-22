From Hammer Require Import Hammer.










Require Import List.
Require Import FSets.
Require Import FMaps.
From VFA Require Import Perm.



Module E := PositiveOrderedTypeBits.
Print Module E.
Print E.t.



Module S <: FSetInterface.S := PositiveSet.
Print Module S.
Print S.elt.



Module M <: FMapInterface.S := PositiveMap.
Print Module M.
Print M.E.






Module WF := WFacts_fun E M.
Module WP := WProperties_fun E M.
Print Module WF.
Print Module WP.

Check E.lt.



Lemma lt_strict: StrictOrder E.lt.
Proof. hammer_hook "Color" "Color.lt_strict". exact M.ME.MO.IsTO.lt_strorder. Qed.

Lemma lt_proper: Proper (eq ==> eq ==> iff) E.lt.
Proof. hammer_hook "Color" "Color.lt_proper". exact M.ME.MO.IsTO.lt_compat. Qed.



Definition Mdomain {A} (m: M.t A) : S.t :=
M.fold (fun n _ s => S.add n s) m S.empty.



Definition example_map : M.t S.t :=
(M.add 3%positive S.empty
(M.add 9%positive S.empty
(M.add 2%positive S.empty (M.empty S.t   )))).

Example domain_example_map:
S.elements (Mdomain example_map) = [2;9;3]%positive.
Proof. hammer_hook "Color" "Color.domain_example_map". compute. reflexivity. Qed.




Print equivlistA.



Definition same_mod_10 (i j: nat) := i mod 10 = j mod 10.
Example InA_example:  InA same_mod_10 27 [3;17;2].
Proof. hammer_hook "Color" "Color.InA_example". right.  left. compute. reflexivity. Qed.



Example equivlistA_example: equivlistA same_mod_10 [3; 17] [7; 3; 27].
Proof. hammer_hook "Color" "Color.equivlistA_example".
split; intro.
inv H. right; left. auto.
inv H1. left. apply H0.
inv H0.
inv H. right; left. apply H1.
inv H1. left. apply H0.
inv H0. right. left. apply H1.
inv H1.
Qed.





Check SortA_equivlistA_eqlistA.



Goal E.t = positive.  Proof. reflexivity. Qed.
Goal E.eq = @eq positive.  Proof. reflexivity. Qed.



Lemma eqlistA_Eeq_eq: forall al bl, eqlistA E.eq al bl <-> al=bl.
Proof. hammer_hook "Color" "Color.eqlistA_Eeq_eq".
split; intro.
* induction H. reflexivity. unfold E.eq in H. subst. reflexivity.
* subst. induction bl. constructor. constructor.
unfold E.eq. reflexivity. assumption.
Qed.



Lemma SortE_equivlistE_eqlistE:
forall al bl, Sorted E.lt al ->
Sorted E.lt bl ->
equivlistA E.eq al bl -> eqlistA E.eq al bl.
Proof. hammer_hook "Color" "Color.SortE_equivlistE_eqlistE".
apply SortA_equivlistA_eqlistA; auto.
apply lt_strict.
apply lt_proper.
Qed.



Lemma filter_sortE: forall f l,
Sorted E.lt l -> Sorted E.lt (List.filter f l).
Proof. hammer_hook "Color" "Color.filter_sortE".
apply filter_sort with E.eq; auto.
apply lt_strict.
apply lt_proper.
Qed.





Check S.remove.
Check S.elements.



Lemma Sremove_elements:  forall (i: E.t) (s: S.t),
S.In i s ->
S.elements (S.remove i s) =
List.filter (fun x => if E.eq_dec x i then false else true) (S.elements s).
Abort.




Lemma Proper_eq_eq:
forall f, Proper (E.eq ==> @eq bool) f.
Proof. hammer_hook "Color" "Color.Proper_eq_eq".
unfold Proper. unfold respectful.
Admitted.

Lemma Sremove_elements:  forall (i: E.t) (s: S.t),
S.In i s ->
S.elements (S.remove i s) =
List.filter (fun x => if E.eq_dec x i then false else true) (S.elements s).
Proof. hammer_hook "Color" "Color.Sremove_elements".
intros.
apply eqlistA_Eeq_eq.
apply SortE_equivlistE_eqlistE.
*
admit.
*
admit.
*
intro j.
rewrite filter_InA; [ | apply Proper_eq_eq].
destruct (E.eq_dec j i).

+
admit.
+
admit.
Admitted.







Check M.elements.




Lemma InA_map_fst_key:
forall A j l,
InA E.eq j (map (@fst M.E.t A) l) <-> exists e, InA (@M.eq_key_elt A) (j,e) l.
Admitted.






Lemma Sorted_lt_key:
forall A (al: list (positive*A)),
Sorted (@M.lt_key A) al <->  Sorted E.lt (map (@fst positive A) al).
Proof. hammer_hook "Color" "Color.Sorted_lt_key".
Admitted.








Lemma cardinal_map:  forall A B (f: A -> B) g,
M.cardinal (M.map f g) = M.cardinal g.



Check M.cardinal_1.
Check M.elements_1.
Check M.elements_2.
Check M.elements_3.
Check map_length.
Check eqlistA_length.
Check SortE_equivlistE_eqlistE.
Check InA_map_fst_key.
Check WF.map_mapsto_iff.
Check Sorted_lt_key.

Admitted.



Lemma Sremove_cardinal_less: forall i s,
S.In i s ->    S.cardinal (S.remove i s) < S.cardinal s.
Proof. hammer_hook "Color" "Color.Sremove_cardinal_less".
intros.
repeat rewrite S.cardinal_1.
generalize (Sremove_elements _ _ H); intro.
rewrite H0; clear H0.
Admitted.





Lemma specialize_SortA_equivlistA_eqlistA:
forall A al bl,
Sorted (@M.lt_key A) al ->
Sorted (@M.lt_key A) bl ->
equivlistA (@M.eq_key_elt A) al bl ->
eqlistA (@M.eq_key_elt A) al bl.
Proof. hammer_hook "Color" "Color.specialize_SortA_equivlistA_eqlistA".
intros.
apply SortA_equivlistA_eqlistA with (@M.lt_key A); auto.
apply M.eqke_equiv.
apply M.ltk_strorder.
clear.
repeat intro.
unfold M.lt_key, M.eq_key_elt in *.
destruct H, H0. rewrite H,H0. split; auto.
Qed.

Lemma Proper_eq_key_elt:
forall A,
Proper (@M.eq_key_elt A ==> @M.eq_key_elt A ==> iff)
(fun x y : E.t * A => E.lt (fst x) (fst y)).
Proof. hammer_hook "Color" "Color.Proper_eq_key_elt".
repeat intro. destruct H,H0. rewrite H,H0. split; auto.
Qed.


Lemma Mremove_elements:  forall A i s,
M.In i s ->
eqlistA (@M.eq_key_elt A) (M.elements (M.remove i s))
(List.filter (fun x => if E.eq_dec (fst x) i then false else true) (M.elements s)).


Check specialize_SortA_equivlistA_eqlistA.
Check M.elements_1.
Check M.elements_2.
Check M.elements_3.
Check M.remove_1.
Check M.eqke_equiv.
Check M.ltk_strorder.
Check Proper_eq_key_elt.
Check filter_InA.

Admitted.



Lemma Mremove_cardinal_less: forall A i (s: M.t A), M.In i s ->
M.cardinal (M.remove i s) < M.cardinal s.



Admitted.




Lemma fold_right_rev_left:
forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
fold_left f l i = fold_right (fun x y => f y x) i (rev l).
Admitted.

Lemma Snot_in_empty: forall n, ~ S.In n S.empty.
Admitted.



Lemma Sin_domain: forall A n (g: M.t A), S.In n (Mdomain g) <-> M.In n g.



Admitted.





Definition node := E.t.
Definition nodeset := S.t.
Definition nodemap: Type -> Type := M.t.
Definition graph := nodemap nodeset.

Definition adj (g: graph) (i: node) : nodeset :=
match M.find i g with Some a => a | None => S.empty end.

Definition undirected (g: graph) :=
forall i j, S.In j (adj g i) -> S.In i (adj g j).

Definition no_selfloop (g: graph) := forall i, ~ S.In i (adj g i).

Definition nodes (g: graph) := Mdomain g.

Definition subset_nodes
(P: node -> nodeset -> bool)
(g: graph) :=
M.fold (fun n adj s => if P n adj then S.add n s else s) g S.empty.



Definition low_deg (K: nat) (n: node) (adj: nodeset) : bool := S.cardinal adj <? K.

Definition remove_node (n: node) (g: graph) : graph :=
M.map (S.remove n) (M.remove n g).






Lemma subset_nodes_sub:  forall P g, S.Subset (subset_nodes P g) (nodes g).
Admitted.



Lemma select_terminates:
forall (K: nat) (g : graph) (n : S.elt),
S.choose (subset_nodes (low_deg K) g) = Some n ->
M.cardinal (remove_node n g) < M.cardinal g.
Admitted.




Require Import Recdef.

Function select (K: nat) (g: graph) {measure M.cardinal g}: list node :=
match S.choose (subset_nodes (low_deg K) g) with
| Some n => n :: select K (remove_node n g)
| None => nil
end.
Proof. hammer_hook "Color" "Color.select_terminates". apply select_terminates.
Defined.

Definition coloring := M.t node.

Definition colors_of (f: coloring) (s: S.t) : S.t :=
S.fold (fun n s => match M.find n f with Some c => S.add c s | None => s end) s S.empty.

Definition color1 (palette: S.t) (g: graph) (n: node) (f: coloring) : coloring :=
match S.choose (S.diff palette (colors_of f (adj g n))) with
| Some c => M.add n c f
| None => f
end.

Definition color (palette: S.t) (g: graph) : coloring :=
fold_right (color1 palette g)  (M.empty _) (select (S.cardinal palette) g).






Definition coloring_ok (palette: S.t) (g: graph) (f: coloring) :=
forall i j, S.In j (adj g i) ->
(forall ci, M.find i f = Some ci -> S.In ci palette) /\
(forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci<>cj).


Lemma adj_ext: forall g i j, E.eq i j -> S.eq (adj g i) (adj g j).
Admitted.



Lemma in_colors_of_1:
forall i s f c, S.In i s -> M.find i f = Some c -> S.In c (colors_of f s).
Admitted.



Theorem color_correct:
forall palette g,
no_selfloop g ->
undirected g ->
coloring_ok palette g (color palette g).
Admitted.







Local Open Scope positive.


Definition palette: S.t := fold_right S.add S.empty [1; 2; 3].

Definition add_edge (e: (E.t*E.t)) (g: graph) : graph :=
M.add (fst e) (S.add (snd e) (adj g (fst e)))
(M.add (snd e) (S.add (fst e) (adj g (snd e))) g).

Definition mk_graph (el: list (E.t*E.t)) :=
fold_right add_edge (M.empty _) el.

Definition G :=
mk_graph [ (5,6); (6,2); (5,2); (1,5); (1,2); (2,4); (1,4)].

Compute (S.elements (Mdomain G)).

Compute (M.elements (color palette G)).




