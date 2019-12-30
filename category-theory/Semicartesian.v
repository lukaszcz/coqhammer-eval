From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section SemicartesianMonoidal.

Context {C : Category}.



Class SemicartesianMonoidal `{@Monoidal C} := {
eliminate {x} : x ~> I;

unit_terminal {x} (f g : x ~> I) : f ≈ g;

proj_left  {x y} : x ⨂ y ~> x := unit_right ∘ id ⨂ eliminate;
proj_right {x y} : x ⨂ y ~> y := unit_left  ∘ eliminate ⨂ id
}.

Corollary eliminate_comp `{@Monoidal C} `{@SemicartesianMonoidal _} `{f : A ~> B} :
eliminate ∘ f ≈ eliminate.
Proof. hammer_hook "Semicartesian" "Semicartesian.eliminate_comp". intros; apply unit_terminal. Qed.

End SemicartesianMonoidal.

Require Import Category.Structure.Terminal.



Program Definition SemicartesianMonoidal_Terminal `{@Monoidal C}
`{@SemicartesianMonoidal C _} : @Terminal C := {|
terminal_obj := I;
one := @eliminate _ _ _;
one_unique := @unit_terminal _ _ _
|}.

Import EqNotations.



Program Definition Terminal_SemicartesianMonoidal `{M : @Monoidal C}
`{T : @Terminal C} (Heq : 1 = @I C M) :
@SemicartesianMonoidal C _ := {|
eliminate := fun x => rew Heq in one;
unit_terminal := fun x f g =>
_ (one_unique (rew <- Heq in f) (rew <- Heq in g))
|}.
Next Obligation.
unfold eq_rect_r, eq_rect, eq_sym in x.
destruct Heq.
assumption.
Defined.
