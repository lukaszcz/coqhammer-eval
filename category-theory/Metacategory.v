From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import Category.Lib.FMapExt.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.



Module PNN := PairUsualDecidableType Nat_as_DT Nat_as_DT.

Module Metacategory (M : WSfun PNN).

Module Import FMapExt := FMapExt PNN M.
Module P := FMapExt.P.
Module F := P.F.

Definition defined x y := M.In (elt:=nat) (x, y).


Record Metacategory := {

arr := nat;


pairs : M.t arr;


composite (f g h : arr) := M.MapsTo (f, g) h pairs;


identity (u : arr) :=
(∀ (f : arr), composite f u f) ∧ (∀ (g : arr), composite u g g);






composition_law (k g f kg gf : arr) :
composite k g kg ->
composite g f gf ->
∀ kgf, composite kg f kgf ↔ composite k gf kgf;




triple_composition (k g f kg gf : arr) :
composite k g kg ->
composite g f gf -> (exists kgf : arr, composite kg f kgf)%type;




identity_law (g : arr) :
∃ u,  identity u  ->
∃ u', identity u' ->
defined g u pairs ∧ defined u' g pairs;
}.

Definition composite_defined (M : Metacategory) (f g h : arr M) :
composite M f g h -> defined f g (pairs M) := fun H =>
proj2 (@in_mapsto_iff _ _ _) (ex_intro _ h H).

Program Definition defined_composite (M : Metacategory) (f g : arr M) :
defined f g (pairs M) -> ∃ h : arr M, composite M f g h.
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.defined_composite".
intro H.
unfold defined in H.
destruct (M.find (f, g) (pairs M)) eqn:Heqe.
exists n.
apply (M.find_2 Heqe).
apply F.in_find_iff in H.
contradiction.
Defined.

Lemma identity_morphism (M : Metacategory) (i : arr M) :
identity M i -> composite M i i i.
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.identity_morphism". intro H; apply H. Qed.

Lemma identity_composition_between (M : Metacategory) :
∀ f g u,
identity M u ->
defined f u (pairs M) ->
defined u g (pairs M) ->
defined f g (pairs M).
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.identity_composition_between".
intros.
destruct H.
pose proof (@triple_composition M f u g f g (c f) (c0 g)) as H3;
simpl in H3.
destruct H3.
apply composite_defined with (h:=x).
exact H.
Defined.

Lemma identity_composition_left (M : Metacategory) :
∀ f g fg u,
identity M u ->
composite M f g fg ->
defined u f (pairs M) ->
defined u fg (pairs M).
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.identity_composition_left".
intros.
destruct H.
apply composite_defined with (h:=fg); auto.
Qed.

Lemma identity_composition_right (M : Metacategory) :
∀ f g fg u,
identity M u ->
composite M f g fg ->
defined g u (pairs M) ->
defined fg u (pairs M).
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.identity_composition_right".
intros.
destruct H.
apply composite_defined with (h:=fg); auto.
Qed.

Local Obligation Tactic := intros.

Global Program Definition FromArrows (M : Metacategory) : Category := {|

obj := ∃ i : arr M, identity M i;


hom := fun x y =>
∃ f : arr M, defined f ``x (pairs M) ∧ defined ``y f (pairs M);

homset := fun _ _ => {| Setoid.equiv := fun f g => `1 f = `1 g |}
|}.
Next Obligation.
equivalence; simpl in *; subst.
Qed.
Next Obligation.
destruct x as [i [Hil Hir]].
exists i.
split; apply composite_defined with (h:=i); auto.
Defined.
Next Obligation.
destruct x as [x x_id];
destruct y as [y y_id];
destruct z as [z z_id];
destruct f as [f [fl fr]];
destruct g as [g [gl gr]]; simpl in *.
pose proof (identity_composition_between M f g y y_id fl gr).
destruct (defined_composite _ _ _ H) as [fg Hfg].
exists fg; split.
eapply identity_composition_right; eauto.
eapply identity_composition_left; eauto.
Defined.
Next Obligation.
proper.
unfold FromArrows_obligation_3; simpl in *; subst.
destruct (defined_composite _ _ _); reflexivity.
Qed.
Next Obligation.
unfold FromArrows_obligation_3; simpl.
destruct x, y, f, i, i0, p; simpl in *; subst.
destruct (defined_composite _ _ _).
pose proof (c2 x1).
unfold composite in c3, H.
apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
unfold FromArrows_obligation_3; simpl.
destruct x, y, f, i, i0, p; simpl in *; subst.
destruct (defined_composite _ _ _).
pose proof (c x1).
unfold composite in c3, H.
apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
unfold FromArrows_obligation_3; simpl.
destruct x as [x [xl_id xr_id]];
destruct y as [y [yl_id yr_id]];
destruct z as [z [zl_id zr_id]];
destruct w as [w [wl_id wr_id]];
destruct f as [f [fl fr]];
destruct g as [g [gl gr]];
destruct h as [h [hl hr]];
simpl in *.
repeat destruct (defined_composite _ _ _).
unfold composite in *.
pose proof (fst (composition_law M f g h x2 x0 c1 c x3) c2).
simpl in H.
apply (FMapExt.F.MapsTo_fun c0 H).
Qed.
Next Obligation.
symmetry.
unfold FromArrows_obligation_3; simpl.
destruct x as [x [xl_id xr_id]];
destruct y as [y [yl_id yr_id]];
destruct z as [z [zl_id zr_id]];
destruct w as [w [wl_id wr_id]];
destruct f as [f [fl fr]];
destruct g as [g [gl gr]];
destruct h as [h [hl hr]];
simpl in *.
repeat destruct (defined_composite _ _ _).
unfold composite in *.
pose proof (fst (composition_law M f g h x2 x0 c1 c x3) c2).
simpl in H.
apply (FMapExt.F.MapsTo_fun c0 H).
Qed.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac structure :=
simpl in *;
repeat (
match goal with
| [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H; subst
| [ |- ?X = ?Y → False ] =>
let H := fresh "H" in
intro H; inversion H; tauto
| [ H : M.MapsTo _ _ _ |- _ ] => simplify_maps
| [ |- M.MapsTo _ _ _ ] => simplify_maps
| [ |- _ ↔ _ ] => split; intros
| [ |- _ /\ _ ] => split
| [ |- _ \/ _ ] => solve [ left; structure | right; structure ]
end; intuition idtac; try congruence).

Ltac check_structure :=
first [ unfold defined;
repeat (unshelve eexists; try assumption; intros []);
split; apply in_mapsto_iff;
eexists; intuition
| unshelve (structure; eexists; structure); exact 0%nat
| structure ].

Local Obligation Tactic := program_simpl; check_structure.

Program Definition ZeroArrows : Metacategory := {|
pairs := [map]
|}.

Program Definition OneArrow : Metacategory := {|
pairs := [map (0, 0) +=> 0 ]%nat
|}.

Program Definition TwoArrows : Metacategory := {|
pairs := [map (0, 0) +=> 0
;    (1, 1) +=> 1

;    (0, 2) +=> 2
;    (2, 1) +=> 2 ]%nat
|}.

Program Definition ThreeArrows : Metacategory := {|
pairs := [map (0, 0) +=> 0
;    (1, 1) +=> 1
;    (2, 2) +=> 2

;    (0, 3) +=> 3
;    (3, 1) +=> 3

;    (1, 4) +=> 4
;    (4, 2) +=> 4

;    (3, 4) +=> 5

;    (0, 5) +=> 5
;    (5, 2) +=> 5 ]%nat
|}.

Definition Three : Category := FromArrows ThreeArrows.

Definition cardinality (M : Metacategory) : nat :=
M.cardinal (P.filter (fun '(dom, cod) v =>
((dom =? v)%nat && (cod =? v)%nat)%bool)
(pairs M)).

Lemma elements_filter {elt} (m : M.t elt) (P : M.key → elt → bool) :
M.elements (P.filter P m)
= filter (fun p => P (fst p) (snd p)) (M.elements m).
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.elements_filter".
unfold P.filter.
apply P.fold_rec; intros.
rewrite (proj1 (P.elements_Empty m0) H); simpl.
apply P.elements_empty.
destruct (P k e) eqn:Heqe.
apply add_equal_iff in H1.
Abort.

Lemma length_elements_filter {elt} (m : M.t elt) k v (P : M.key * elt → bool) :
length (filter P (M.elements (M.add k v m)))
= length (filter P ((k, v) :: M.elements m)).
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.length_elements_filter".
Abort.

Theorem elements_rect {elt} (P : list (M.key * elt) -> Type) :
(∀ m1 m2, M.Equal m1 m2 -> P (M.elements m1) -> P (M.elements m2))
-> ∀ m k v, P ((k, v) :: M.elements m) -> P (M.elements (M.add k v m)).
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.elements_rect".
Abort.


Lemma ThreeArrows_card_3 : cardinality ThreeArrows = 3%nat.
Proof. hammer_hook "Metacategory" "Metacategory.Metacategory.ThreeArrows_card_3".




assert (P.transpose_neqkey
M.Equal
(λ (k : M.key) (e : nat) (m : M.t nat),
if (let '(dom, cod) := k in
λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
then k +=> e m
else m)).
intros ??????.
destruct k, k'.
assert (n ≠ n1 \/ n0 ≠ n2).
destruct (Nat.eq_dec n n1); subst.
right; congruence.
left; assumption.
destruct ((n =? e)%nat && (n0 =? e)%nat) eqn:Heqe.
apply andb_true_iff in Heqe.
destruct Heqe.
apply Nat.eqb_eq in H1.
apply Nat.eqb_eq in H2.
subst.
destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
apply andb_true_iff in Heqe2.
destruct Heqe2.
apply Nat.eqb_eq in H1.
apply Nat.eqb_eq in H2.
subst.
apply add_associative.
intros; congruence.
reflexivity.
destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
apply andb_true_iff in Heqe2.
destruct Heqe2.
apply Nat.eqb_eq in H1.
apply Nat.eqb_eq in H2.
subst.
reflexivity.
reflexivity.

assert (Proper (eq ==> eq ==> M.Equal ==> M.Equal)
(λ (k : M.key) (e : nat) (m : M.t nat),
if (let '(dom, cod) := k in
λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
then k +=> e m
else m)).
intros ?????????.
destruct x, y; subst.
inversion H0; clear H0; subst.
destruct ((n1 =? y0)%nat && (n2 =? y0)%nat) eqn:Heqe.
apply andb_true_iff in Heqe.
destruct Heqe.
apply Nat.eqb_eq in H0.
apply Nat.eqb_eq in H1.
subst.
rewrite H2; reflexivity.
assumption.

unfold cardinality; simpl.
unfold P.filter; simpl.
repeat (rewrite P.fold_add; eauto; relational; simpl);
try (apply not_in_mapsto_iff; intros;
repeat (unfold not; intros; simplify_maps; try congruence)).
rewrite P.fold_Empty; auto; [| apply M.empty_1 ].

assert (P.transpose_neqkey eq (λ (_ : M.key) (_ : nat), S)) by proper.

rewrite P.cardinal_fold.
repeat (rewrite P.fold_add; eauto; relational; simpl);
try (apply not_in_mapsto_iff; intros;
repeat (unfold not; intros; simplify_maps; try congruence)).
rewrite P.fold_Empty; auto; apply M.empty_1.
Qed.




Local Obligation Tactic := program_simpl.



End Metacategory.
