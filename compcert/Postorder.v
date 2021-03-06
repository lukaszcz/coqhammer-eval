From Hammer Require Import Hammer.


















Require Import Wellfounded.
Require Import Permutation.
Require Import Mergesort.
From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Iteration.



Definition node: Type := positive.

Definition graph: Type := PTree.t (list node).



Module PositiveOrd.
Definition t := positive.
Definition leb (x y: t): bool := if plt y x then false else true.

Theorem leb_total : forall x y, is_true (leb x y) \/ is_true (leb y x).
Proof. hammer_hook "Postorder" "Postorder.PositiveOrd.leb_total".
unfold leb, is_true; intros.
destruct (plt x y); auto. destruct (plt y x); auto.
elim (Plt_strict x). eapply Plt_trans; eauto.
Qed.
End PositiveOrd.

Module Sort := Mergesort.Sort(PositiveOrd).



Record state : Type := mkstate {
gr: graph;
wrk: list (node * list node);
map: PTree.t positive;
next: positive
}.

Definition init_state (g: graph) (root: node) :=
match g!root with
| Some succs =>
{| gr := PTree.remove root g;
wrk := (root, Sort.sort succs) :: nil;
map := PTree.empty positive;
next := 1%positive |}
| None =>
{| gr := g;
wrk := nil;
map := PTree.empty positive;
next := 1%positive |}
end.

Definition transition (s: state) : PTree.t positive + state :=
match s.(wrk) with
| nil =>
inl _ s.(map)
| (x, nil) :: l =>
inr _ {| gr := s.(gr);
wrk := l;
map := PTree.set x s.(next) s.(map);
next := Pos.succ s.(next) |}
| (x, y :: succs_x) :: l =>
match s.(gr)!y with
| None =>
inr _ {| gr := s.(gr);
wrk := (x, succs_x) :: l;
map := s.(map);
next := s.(next) |}
| Some succs_y =>
inr _ {| gr := PTree.remove y s.(gr);
wrk := (y, Sort.sort succs_y) :: (x, succs_x) :: l;
map := s.(map);
next := s.(next) |}
end
end.

Section POSTORDER.

Variable ginit: graph.
Variable root: node.

Inductive invariant (s: state) : Prop :=
Invariant

(SUB: forall x y, s.(gr)!x = Some y -> ginit!x = Some y)

(ROOT: s.(gr)!root = None)

(BELOW: forall x y, s.(map)!x = Some y -> Plt y s.(next))

(INJ: forall x1 x2 y, s.(map)!x1 = Some y -> s.(map)!x2 = Some y -> x1 = x2)

(REM: forall x y, s.(gr)!x = Some y -> s.(map)!x = None)

(COLOR: forall x succs n y,
ginit!x = Some succs -> s.(map)!x = Some n ->
In y succs -> s.(gr)!y = None)

(WKLIST: forall x l, In (x, l) s.(wrk) ->
s.(gr)!x = None /\
exists l', ginit!x = Some l'
/\ forall y, In y l' -> ~In y l -> s.(gr)!y = None)

(GREY: forall x, ginit!x <> None -> s.(gr)!x = None -> s.(map)!x = None ->
exists l, In (x,l) s.(wrk)).

Inductive postcondition (map: PTree.t positive) : Prop :=
Postcondition
(INJ: forall x1 x2 y, map!x1 = Some y -> map!x2 = Some y -> x1 = x2)
(ROOT: ginit!root <> None -> map!root <> None)
(SUCCS: forall x succs y, ginit!x = Some succs -> map!x <> None -> In y succs -> ginit!y <> None -> map!y <> None).

Remark In_sort:
forall x l, In x l <-> In x (Sort.sort l).
Proof. hammer_hook "Postorder" "Postorder.In_sort".
intros; split; intros.
apply Permutation_in with l. apply Sort.Permuted_sort. auto.
apply Permutation_in with (Sort.sort l). apply Permutation_sym. apply Sort.Permuted_sort. auto.
Qed.

Lemma transition_spec:
forall s, invariant s ->
match transition s with inr s' => invariant s' | inl m => postcondition m end.
Proof. hammer_hook "Postorder" "Postorder.transition_spec".
intros. inv H. unfold transition. destruct (wrk s) as [ | [x succ_x] l].

constructor; intros.
eauto.
caseEq (s.(map)!root); intros. congruence. exploit GREY; eauto. intros [? ?]; contradiction.
destruct (s.(map)!x) eqn:?; try congruence.
destruct (s.(map)!y) eqn:?; try congruence.
exploit COLOR; eauto. intros. exploit GREY; eauto. intros [? ?]; contradiction.

destruct succ_x as [ | y succ_x ].

constructor; simpl; intros.

eauto.

eauto.

rewrite PTree.gsspec in H. destruct (peq x0 x). inv H.
apply Plt_succ.
apply Plt_trans_succ. eauto.

rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0.
destruct (peq x1 x); destruct (peq x2 x); subst.
auto.
inv H. exploit BELOW; eauto. intros. eelim Plt_strict; eauto.
inv H0. exploit BELOW; eauto. intros. eelim Plt_strict; eauto.
eauto.

intros. rewrite PTree.gso; eauto. red; intros; subst x0.
exploit (WKLIST x nil); auto with coqlib. intros [A B]. congruence.

rewrite PTree.gsspec in H0. destruct (peq x0 x).
inv H0.  exploit (WKLIST x nil); auto with coqlib.
intros [A [l' [B C]]].
assert (l' = succs) by congruence. subst l'.
apply C; auto.
eauto.

apply WKLIST. auto with coqlib.

rewrite PTree.gsspec in H1. destruct (peq x0 x). inv H1.
exploit GREY; eauto. intros [l' A]. simpl in A; destruct A.
congruence.
exists l'; auto.


destruct ((gr s)!y) as [ succs_y | ] eqn:?.

constructor; simpl; intros.

rewrite PTree.grspec in H. destruct (PTree.elt_eq x0 y); eauto. inv H.

rewrite PTree.gro. auto. congruence.

eauto.

eauto.

rewrite PTree.grspec in H. destruct (PTree.elt_eq x0 y); eauto. inv H.

rewrite PTree.grspec. destruct (PTree.elt_eq y0 y); eauto.

destruct H.
inv H. split. apply PTree.grs. exists succs_y; split. eauto.
intros. rewrite In_sort in H. tauto.
destruct H.
inv H. exploit WKLIST; eauto with coqlib. intros [A [l' [B C]]].
split. rewrite PTree.grspec. destruct (PTree.elt_eq x0 y); auto.
exists l'; split. auto. intros. rewrite PTree.grspec. destruct (PTree.elt_eq y0 y); auto.
apply C; auto. simpl. intuition congruence.
exploit (WKLIST x0 l0); eauto with coqlib. intros [A [l' [B C]]].
split. rewrite PTree.grspec. destruct (PTree.elt_eq x0 y); auto.
exists l'; split; auto. intros.
rewrite PTree.grspec. destruct (PTree.elt_eq y0 y); auto.

rewrite PTree.grspec in H0. destruct (PTree.elt_eq x0 y) in H0.
subst. exists (Sort.sort succs_y); auto with coqlib.
exploit GREY; eauto. simpl. intros [l1 A]. destruct A.
inv H2. exists succ_x; auto.
exists l1; auto.


constructor; simpl; intros; eauto.

destruct H. inv H.
exploit (WKLIST x0); eauto with coqlib. intros [A [l' [B C]]].
split. auto. exists l'; split. auto.
intros. destruct (peq y y0). congruence. apply C; auto. simpl. intuition congruence.
eapply WKLIST; eauto with coqlib.

exploit GREY; eauto. intros [l1 A]. simpl in A. destruct A.
inv H2. exists succ_x; auto.
exists l1; auto.
Qed.

Lemma initial_state_spec:
invariant (init_state ginit root).
Proof. hammer_hook "Postorder" "Postorder.initial_state_spec".
unfold init_state. destruct (ginit!root) as [succs|] eqn:?.

constructor; simpl; intros.

rewrite PTree.grspec in H. destruct (PTree.elt_eq x root). inv H. auto.

apply PTree.grs.

rewrite PTree.gempty in H; inv H.

rewrite PTree.gempty in H; inv H.

apply PTree.gempty.

rewrite PTree.gempty in H0; inv H0.

destruct H; inv H.
split. apply PTree.grs. exists succs; split; auto.
intros. rewrite In_sort in H. intuition.

rewrite PTree.grspec in H0. destruct (PTree.elt_eq x root).
subst. exists (Sort.sort succs); auto.
contradiction.


constructor; simpl; intros.

auto.

auto.

rewrite PTree.gempty in H; inv H.

rewrite PTree.gempty in H; inv H.

apply PTree.gempty.

rewrite PTree.gempty in H0; inv H0.

contradiction.

contradiction.

Qed.



Fixpoint size_worklist (w: list (positive * list positive)) : nat :=
match w with
| nil => 0%nat
| (x, succs) :: w' => (S (List.length succs) + size_worklist w')%nat
end.

Definition lt_state (s1 s2: state) : Prop :=
lex_ord lt lt (PTree_Properties.cardinal s1.(gr), size_worklist s1.(wrk))
(PTree_Properties.cardinal s2.(gr), size_worklist s2.(wrk)).

Lemma lt_state_wf: well_founded lt_state.
Proof. hammer_hook "Postorder" "Postorder.lt_state_wf".
set (f := fun s => (PTree_Properties.cardinal s.(gr), size_worklist s.(wrk))).
change (well_founded (fun s1 s2 => lex_ord lt lt (f s1) (f s2))).
apply wf_inverse_image.
apply wf_lex_ord.
apply lt_wf. apply lt_wf.
Qed.

Lemma transition_decreases:
forall s s', transition s = inr _ s' -> lt_state s' s.
Proof. hammer_hook "Postorder" "Postorder.transition_decreases".
unfold transition, lt_state; intros.
destruct (wrk s) as [ | [x succs] l].
discriminate.
destruct succs as [ | y succs ].
inv H. simpl. apply lex_ord_right. omega.
destruct ((gr s)!y) as [succs'|] eqn:?.
inv H. simpl. apply lex_ord_left. eapply PTree_Properties.cardinal_remove; eauto.
inv H. simpl. apply lex_ord_right. omega.
Qed.

End POSTORDER.

Definition postorder (g: graph) (root: node) :=
WfIter.iterate _ _ transition lt_state lt_state_wf transition_decreases (init_state g root).

Inductive reachable (g: graph) (root: positive) : positive -> Prop :=
| reachable_root:
reachable g root root
| reachable_succ: forall x succs y,
reachable g root x -> g!x = Some succs -> In y succs ->
reachable g root y.

Theorem postorder_correct:
forall g root,
let m := postorder g root in
(forall x1 x2 y, m!x1 = Some y -> m!x2 = Some y -> x1 = x2)
/\ (forall x, reachable g root x -> g!x <> None -> m!x <> None).
Proof. hammer_hook "Postorder" "Postorder.postorder_correct".
intros.
assert (postcondition g root m).
unfold m. unfold postorder.
apply WfIter.iterate_prop with (P := invariant g root).
apply transition_spec.
apply initial_state_spec.
inv H.
split. auto.
induction 1; intros.

apply ROOT; auto.

eapply SUCCS; eauto. apply IHreachable. congruence.
Qed.

