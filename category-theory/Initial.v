From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Structure.Terminal.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.



Notation "'Initial' C" := (@Terminal (C^op))
(at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
(at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

Definition initial_obj : C := @terminal_obj _ I.
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≈ g :=
@one_unique _ I _ _ _.

End Initial_.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
(at level 9, format "zero[ C ]") : morphism_scope.

Hint Resolve @zero_unique : category_laws.

Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
f ∘ zero ≈ zero.
Proof. hammer_hook "Initial" "Initial.zero_comp". apply (@one_comp _ T). Qed.

Hint Rewrite @zero_comp : categories.
