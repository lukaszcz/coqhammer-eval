From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Morphisms.

Context {C : Category}.

Open Scope type_scope.

Class Idempotent `(f : x ~> x) := {
idem : f ∘ f ≈ f
}.

Class Involutive `(f : x ~> x) := {
invol : f ∘ f ≈ id
}.

Lemma flip_invol {x y} (f h : x ~> y) (g : y ~> y) `{@Involutive _ g} :
f ≈ g ∘ h ↔ g ∘ f ≈ h.
Proof. hammer_hook "Morphisms" "Morphisms.flip_invol".
split; intros.
rewrite X, comp_assoc, invol; cat.
rewrite <- X, comp_assoc, invol; cat.
Qed.

Class Section `(f : x ~> y) := {
section : y ~> x;
section_comp : section ∘ f ≈ id
}.

Class Retraction `(f : x ~> y) := {
retract : y ~> x;
retract_comp : f ∘ retract ≈ id
}.

Class SplitIdempotent {x y : C} := {
split_idem_retract := y;

split_idem    : x ~> x;
split_idem_r  : x ~> split_idem_retract;
split_idem_s  : split_idem_retract ~> x;
split_idem_sr : split_idem_s ∘ split_idem_r ≈ split_idem;
split_idem_rs : split_idem_r ∘ split_idem_s ≈ id
}.

Class Epic {x y} (f : x ~> y) := {
epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2
}.

Class Monic {x y} (f : x ~> y) := {
monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2
}.

Definition Bimorphic `(f : x ~> y) := (Epic f * Monic f)%type.
Definition SplitEpi  `(f : x ~> y) := Retraction f.
Definition SplitMono `(f : x ~> y) := Section f.

Corollary id_idem : ∀ x, Idempotent (id (x:=x)).
Proof. hammer_hook "Morphisms" "Morphisms.id_idem". intros; constructor; cat. Qed.

Corollary id_invol : ∀ x, Involutive (id (x:=x)).
Proof. hammer_hook "Morphisms" "Morphisms.id_invol". intros; constructor; cat. Qed.

Corollary id_monic : ∀ x, Monic (id (x:=x)).
Proof. hammer_hook "Morphisms" "Morphisms.id_monic".
intros; constructor; intros.
rewrite !id_left in X.
assumption.
Qed.

Corollary id_epic : ∀ x, Epic (id (x:=x)).
Proof. hammer_hook "Morphisms" "Morphisms.id_epic".
intros; constructor; intros.
rewrite !id_right in X.
assumption.
Qed.

Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.

Section Lemmas.

Variables x y : C.
Variable f : x ~> y.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); try f_equiv; cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); try f_equiv; cat.

Lemma retractions_are_epic : Retraction f → Epic f.
Proof. hammer_hook "Morphisms" "Morphisms.retractions_are_epic".
autounfold.
intros.
destruct X.
constructor; intros.
rewrite <- id_right.
symmetry.
rewrite <- id_right.
rewrite <- retract_comp0.
reassociate_right.
Qed.

Lemma sections_are_monic : Section f → Monic f.
Proof. hammer_hook "Morphisms" "Morphisms.sections_are_monic".
autounfold.
intros.
destruct X.
constructor; intros.
rewrite <- id_left.
symmetry.
rewrite <- id_left.
rewrite <- section_comp0.
reassociate_left.
Qed.

End Lemmas.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); cat.

Definition epi_compose {x y z : C}
`(ef : @Epic y z f) `(eg : @Epic x y g) : Epic (f ∘ g).
Proof. hammer_hook "Morphisms" "Morphisms.epi_compose".
autounfold; intros.
destruct ef, eg.
constructor; intros.
apply epic0, epic1.
reassociate_left.
Qed.

Definition monic_compose {x y z : C}
`(ef : @Monic y z f) `(eg : @Monic x y g) : Monic (f ∘ g).
Proof. hammer_hook "Morphisms" "Morphisms.monic_compose".
autounfold; intros.
destruct ef, eg.
constructor; intros.
apply monic1, monic0.
reassociate_right.
Qed.

End Morphisms.

Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.

Definition flip_Section {C : Category} `(f : x ~> y)
(s : @Section C x y f) : @Retraction C y x section.
Proof. hammer_hook "Morphisms" "Morphisms.flip_Section".
autounfold.
destruct s.
exists f.
assumption.
Qed.

Definition flip_Retraction {C : Category} `(f : x ~> y)
(s : @Retraction C x y f) : @Section C y x retract.
Proof. hammer_hook "Morphisms" "Morphisms.flip_Retraction".
autounfold.
destruct s.
exists f.
assumption.
Qed.
