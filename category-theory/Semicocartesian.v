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

Section SemicocartesianMonoidal.

Context {C : Category}.





Class SemicocartesianMonoidal `{@Monoidal C} := {
generate {x} : I ~> x;

unit_initial {x} (f g : I ~> x) : f ≈ g;

embed_left  {x y} : x ~> x ⨂ y := id ⨂ generate ∘ unit_right⁻¹;
embed_right {x y} : y ~> x ⨂ y := generate ⨂ id ∘ unit_left⁻¹
}.

Corollary generate_comp `{@Monoidal C} `{@SemicocartesianMonoidal _} `{f : A ~> B} :
f ∘ generate ≈ generate.
Proof. hammer_hook "Semicocartesian" "Semicocartesian.generate_comp". intros; apply unit_initial. Qed.

End SemicocartesianMonoidal.

Require Import Category.Structure.Initial.



Program Definition SemicocartesianMonoidal_Initial `{@Monoidal C}
`{@SemicocartesianMonoidal C _} : @Initial C := {|
terminal_obj := @I C _;
one := @generate _ _ _;
one_unique := @unit_initial _ _ _
|}.

Import EqNotations.



Program Definition Initial_SemicocartesianMonoidal `{M : @Monoidal C}
`{T : @Initial C} (Heq : @initial_obj C T = @I C M) :
@SemicocartesianMonoidal C _ := {|
generate := fun x => _ (@zero C T x);
unit_initial := fun x f g => _ (@zero_unique C T x) f g
|}.
Next Obligation. rewrite Heq in x0; apply x0. Defined.
