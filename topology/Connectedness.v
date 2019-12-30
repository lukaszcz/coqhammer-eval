From Hammer Require Import Hammer.

From Topology Require Export TopologicalSpaces.
From Topology Require Import InverseImageLemmas.

Definition clopen {X:TopologicalSpace} (S:Ensemble (point_set X))
: Prop :=
open S /\ closed S.

Definition connected (X:TopologicalSpace) : Prop :=
forall S:Ensemble (point_set X), clopen S ->
S = Empty_set \/ S = Full_set.

From Topology Require Export Homeomorphisms.

Lemma connected_img: forall {X Y:TopologicalSpace}
(f:point_set X -> point_set Y),
connected X -> continuous f -> surjective f -> connected Y.
Proof. hammer_hook "Connectedness" "Connectedness.connected_img".
intros.
red; intros.
destruct (H (inverse_image f S)).
split.
apply H0.
apply H2.
red.
rewrite <- inverse_image_complement.
apply H0.
apply H2.

left.
apply Extensionality_Ensembles; split; red; intros.
destruct (H1 x).
assert (In Empty_set x0).
rewrite <- H3.
constructor.
rewrite H5.
trivial.
destruct H6.
destruct H4.

right.
apply Extensionality_Ensembles; split; red; intros.
constructor.
destruct (H1 x).
rewrite <- H5.
assert (In (inverse_image f S) x0).
rewrite H3; constructor.
destruct H6; trivial.
Qed.

From Topology Require Export SubspaceTopology.

Lemma connected_union: forall {X:TopologicalSpace}
{A:Type} (S:IndexedFamily A (point_set X)),
(forall a:A, connected (SubspaceTopology (S a))) ->
Inhabited (IndexedIntersection S) ->
IndexedUnion S = Full_set -> connected X.
Proof. hammer_hook "Connectedness" "Connectedness.connected_union".
intros.
pose (inc := fun (a:A) => subspace_inc (S a)).
destruct H0.
destruct H0.
red; intros.
assert (forall a:A, clopen (inverse_image (inc a) S0)).
intro.
split.
apply subspace_inc_continuous.
apply H2.
red.
rewrite <- inverse_image_complement.
apply subspace_inc_continuous.
apply H2.
destruct (classic (In S0 x)).
right.
assert (forall a:A, inverse_image (inc a) S0 = Full_set).
intro.
destruct (H a _ (H3 a)).
assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
(exist _ x (H0 a))).
rewrite <- H5.
constructor.
simpl.
trivial.
destruct H6.
trivial.
apply Extensionality_Ensembles; split; red; intros.
constructor.
assert (In (IndexedUnion S) x0).
rewrite H1; constructor.
destruct H7.
assert (In (@Full_set (point_set (SubspaceTopology (S a))))
(exist _ x0 H7)).
constructor.
rewrite <- H5 in H8.
destruct H8.
simpl in H8.
trivial.

left.
assert (forall a:A, inverse_image (inc a) S0 = Empty_set).
intros.
destruct (H a _ (H3 a)).
trivial.
assert (In (@Full_set (point_set (SubspaceTopology (S a))))
(exist _ x (H0 a))).
constructor.
rewrite <- H5 in H6.
destruct H6.
simpl in H6.
contradiction H4.

apply Extensionality_Ensembles; split; red; intros.
assert (In (IndexedUnion S) x0).
rewrite H1; constructor.
destruct H7.
assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
(exist _ x0 H7)).
rewrite <- H5.
constructor.
simpl.
trivial.
destruct H8.
destruct H6.
Qed.

Lemma topological_property_connected :
topological_property connected.
Proof. hammer_hook "Connectedness" "Connectedness.topological_property_connected".
intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hconn S [Hopen Hclose].
destruct (Hconn (inverse_image f S));
[ | left | right ];
try apply Extensionality_Ensembles;
split; red; intros.
- apply Hcont_f.
assumption.
- rewrite <- inverse_image_complement.
apply Hcont_f.
assumption.
- rewrite <- Hfg.
apply in_inverse_image.
rewrite inverse_image_empty, <- H.
constructor.
rewrite Hfg.
assumption.
- destruct H0.
- constructor.
- rewrite <- Hfg.
apply in_inverse_image.
rewrite H.
constructor.
Qed.
