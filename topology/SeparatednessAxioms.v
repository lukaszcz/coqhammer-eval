From Hammer Require Import Hammer.

From Topology Require Export TopologicalSpaces.
From Topology Require Import InteriorsClosures.
From Topology Require Import InverseImageLemmas.
From Topology Require Import Homeomorphisms.

Definition T0_sep (X:TopologicalSpace) : Prop :=
forall x y:point_set X, x <> y ->
(exists U:Ensemble (point_set X), open U /\ In U x /\ ~ In U y) \/
(exists U:Ensemble (point_set X), open U /\ ~ In U x /\ In U y).

Lemma topological_property_T0_sep : topological_property T0_sep.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.topological_property_T0_sep".
intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hsep x y neq.
destruct (Hsep (g x) (g y)) as [[U [Hopen [Hin H']]] | [U [Hopen [H' Hin]]]];
[ shelve | left | right ];
exists (inverse_image g U);
repeat split;
try apply Hcont_g;
assumption + (intros [?]; contradiction).
Unshelve.
intro contra.
eapply f_equal in contra.
rewrite Hfg, Hfg in contra.
contradiction.
Qed.

Definition T1_sep (X:TopologicalSpace) : Prop :=
forall x:point_set X, closed (Singleton x).

Lemma topological_property_T1_sep : topological_property T1_sep.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.topological_property_T1_sep".
intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hsep x.
replace (Singleton x) with (inverse_image g (Singleton (g x))).
- red.
rewrite <- inverse_image_complement.
apply Hcont_g.
apply Hsep.
- apply Extensionality_Ensembles.
split;
red;
intros.
+ destruct H.
inversion H.
eapply f_equal in H1.
rewrite Hfg, Hfg in H1.
subst.
constructor.
+ inversion H.
subst.
constructor.
constructor.
Qed.

Definition Hausdorff (X:TopologicalSpace) : Prop :=
forall x y:point_set X, x <> y ->
exists U:Ensemble (point_set X),
exists V:Ensemble (point_set X),
open U /\ open V /\ In U x /\ In V y /\
Intersection U V = Empty_set.
Definition T2_sep := Hausdorff.

Definition topological_property_Hausdorff :
topological_property Hausdorff.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.topological_property_Hausdorff".
intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hhaus x y neq.
destruct (Hhaus (g x) (g y)) as [U [V [HopenU [HopenV [HinU [HinV eq]]]]]].
- intro contra.
eapply f_equal in contra.
rewrite Hfg, Hfg in contra.
contradiction.
- exists (inverse_image g U), (inverse_image g V).
repeat split;
try apply Hcont_g;
try assumption.
erewrite <- inverse_image_intersection, <- inverse_image_empty.
f_equal.
assumption.
Qed.

Definition T3_sep (X:TopologicalSpace) : Prop :=
T1_sep X /\
forall (x:point_set X) (F:Ensemble (point_set X)),
closed F -> ~ In F x -> exists U:Ensemble (point_set X),
exists V:Ensemble (point_set X),
open U /\ open V /\ In U x /\ Included F V /\
Intersection U V = Empty_set.

Lemma topological_property_T3_sep : topological_property T3_sep.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.topological_property_T3_sep".
intros X Y f Hf [HT1 H].
split.
- eapply topological_property_T1_sep.
+ exact Hf.
+ assumption.
- destruct Hf as [g Hcont_f Hcont_g Hgf Hfg].
intros y F Hcl Hn.
destruct (H (g y) (inverse_image f F)) as [U [V [HopenU [HopenV [HinU [Hincl eq]]]]]].
+ red.
rewrite <- inverse_image_complement.
apply Hcont_f.
assumption.
+ intros [contra].
rewrite Hfg in contra.
contradiction.
+ exists (inverse_image g U), (inverse_image g V).
repeat split;
try apply Hcont_g;
try assumption.
* apply Hincl.
constructor.
rewrite Hfg.
assumption.
* erewrite <- inverse_image_intersection, <- inverse_image_empty.
f_equal.
assumption.
Qed.

Definition normal_sep (X:TopologicalSpace) : Prop :=
T1_sep X /\
forall (F G:Ensemble (point_set X)),
closed F -> closed G -> Intersection F G = Empty_set ->
exists U:Ensemble (point_set X), exists V:Ensemble (point_set X),
open U /\ open V /\ Included F U /\ Included G V /\
Intersection U V = Empty_set.
Definition T4_sep := normal_sep.

Lemma T1_sep_impl_T0_sep: forall X:TopologicalSpace,
T1_sep X -> T0_sep X.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.T1_sep_impl_T0_sep".
intros.
red; intros.
left.
exists (Complement (Singleton y)); repeat split.
apply H.
repeat red; intro.
destruct H1; contradiction H0; trivial.
red; intro.
repeat red in H1.
apply H1; constructor.
Qed.

Lemma Hausdorff_impl_T1_sep: forall X:TopologicalSpace,
Hausdorff X -> T1_sep X.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.Hausdorff_impl_T1_sep".
intros.
red; intros.
assert (closure (Singleton x) = Singleton x).
apply Extensionality_Ensembles; split.
red; intros.
assert (x = x0).
apply NNPP.
red; intro.
pose proof (H x x0 H1).
destruct H2 as [U [V ?]].
intuition.
assert (In (interior (Complement (Singleton x))) x0).
exists V.
constructor; split; trivial.
red; intros.
red; red; intro.
destruct H8.
assert (In Empty_set x).
rewrite <- H7.
constructor; trivial.
destruct H8.
assumption.
rewrite interior_complement in H6.
contradiction H6; exact H0.
destruct H1; constructor.
apply closure_inflationary.

rewrite <- H0; apply closure_closed.
Qed.

Lemma T3_sep_impl_Hausdorff: forall X:TopologicalSpace,
T3_sep X -> Hausdorff X.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.T3_sep_impl_Hausdorff".
intros.
destruct H.
red; intros.
pose proof (H0 x (Singleton y)).
match type of H2 with | ?A -> ?B -> ?C => assert C end.
apply H2.
apply H.
red; intro.
destruct H3.
contradiction H1; trivial.
destruct H3 as [U [V [? [? [? [? ?]]]]]].
exists U; exists V; repeat split; auto with sets.
Qed.

Lemma normal_sep_impl_T3_sep: forall X:TopologicalSpace,
normal_sep X -> T3_sep X.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.normal_sep_impl_T3_sep".
intros.
destruct H.
split; trivial.
intros.
pose proof (H0 (Singleton x) F).
match type of H3 with | ?A -> ?B -> ?C -> ?D => assert D end.
apply H3; trivial.
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
destruct H4 as [? []].
contradiction H2.
destruct H4 as [U [V [? [? [? [? ?]]]]]].
exists U; exists V; repeat split; auto with sets.
Qed.

From Topology Require Export Nets.

Section Hausdorff_and_nets.

Lemma Hausdorff_impl_net_limit_unique:
forall {X:TopologicalSpace} {I:DirectedSet} (x:Net I X),
Hausdorff X -> uniqueness (net_limit x).
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.Hausdorff_impl_net_limit_unique".
intros.
red; intros x1 x2 ? ?.
apply NNPP; intro.
destruct (H x1 x2) as [U [V [? [? [? [? ?]]]]]]; trivial.
destruct (H0 U H3 H5) as [i].
destruct (H1 V H4 H6) as [j].
destruct (DS_join_cond i j) as [k [? ?]].
assert (In (Intersection U V) (x k)).
constructor; (apply H8 || apply H9); trivial.
rewrite H7 in H12.
destruct H12.
Qed.

Lemma Hausdorff_impl_net_limit_is_unique_cluster_point:
forall {X:TopologicalSpace} {I:DirectedSet} (x:Net I X)
(x0:point_set X), Hausdorff X -> net_limit x x0 ->
forall y:point_set X, net_cluster_point x y -> y = x0.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.Hausdorff_impl_net_limit_is_unique_cluster_point".
intros.
destruct (net_cluster_point_impl_subnet_converges _ _ x y H1) as
[J [x' [? ?]]].
destruct (H0 Full_set).
apply open_full.
constructor.
exists; exact x1.
assert (net_limit x' x0).
apply subnet_limit with _ x; trivial.
apply Hausdorff_impl_net_limit_unique with x'; trivial.
Qed.

Lemma net_limit_is_unique_cluster_point_impl_Hausdorff:
forall (X:TopologicalSpace),
(forall (I:DirectedSet) (x:Net I X) (x0 y:point_set X),
net_limit x x0 -> net_cluster_point x y ->
y = x0) -> Hausdorff X.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.net_limit_is_unique_cluster_point_impl_Hausdorff".
intros.
red; intros.
assert (~ net_cluster_point (neighborhood_net _ x) y).
red; intro.
contradiction H0.
symmetry.
apply H with _ (neighborhood_net _ x).
apply neighborhood_net_limit.
assumption.

apply not_all_ex_not in H1.
destruct H1 as [V].
apply imply_to_and in H1.
destruct H1.
apply imply_to_and in H2.
destruct H2.
apply not_all_ex_not in H3.
destruct H3 as [[U]].
exists U; exists V; repeat split; trivial.
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
destruct H4.
contradiction H3.
exists (intro_neighborhood_net_DS X x U x0 o i H4).
split.
simpl; auto with sets.
simpl.
trivial.
Qed.

Lemma net_limit_uniqueness_impl_Hausdorff:
forall X:TopologicalSpace,
(forall (I:DirectedSet) (x:Net I X), uniqueness (net_limit x)) ->
Hausdorff X.
Proof. hammer_hook "SeparatednessAxioms" "SeparatednessAxioms.net_limit_uniqueness_impl_Hausdorff".
intros.
apply net_limit_is_unique_cluster_point_impl_Hausdorff.
intros.
pose proof (net_cluster_point_impl_subnet_converges _ _ _ _ H1).
destruct H2 as [J [x' [? ?]]].
destruct (H0 Full_set).
apply open_full.
constructor.
exists; exact x1.
assert (net_limit x' x0).
apply subnet_limit with _ x; trivial.
unfold uniqueness in H.
apply H with _ x'; trivial.
Qed.

End Hausdorff_and_nets.
