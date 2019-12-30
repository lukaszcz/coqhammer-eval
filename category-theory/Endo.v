From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.



Class EndoFunctor {C : Category} (F : C -> C) : Type := {
map {x y} (f : x ~> y) : F x ~> F y;

is_functor : C ⟶ C;

fobj_related {x} : F x ≅ is_functor x;
fmap_related {x y} (f : x ~> y) :
map f ≈ from fobj_related ∘ fmap[is_functor] f ∘ to fobj_related
}.

Coercion is_functor : EndoFunctor >-> Functor.

Notation "map[ F ]" := (@map _ _ F _ _)
(at level 9, format "map[ F ]") : morphism_scope.

Program Instance Identity_EndoFunctor {C : Category} :
EndoFunctor (fun x => x) | 9 := {
map := fun _ _ f => f;
is_functor := Id
}.

Program Instance Functor_EndoFunctor {C : Category} {F : C ⟶ C} :
EndoFunctor F := {
map := fun _ _ f => fmap[F] f;
is_functor := F
}.

Program Instance Functor_Eta_EndoFunctor {C : Category} {F : C ⟶ C} :
EndoFunctor (fun x => F x) := {
map := fun _ _ f => fmap[F] f;
is_functor := F
}.

Program Instance Functor_Map_EndoFunctor {C : Category}
`{G : @EndoFunctor C P} {F : C ⟶ C} :
EndoFunctor (fun x => F (P x)) := {
map := fun _ _ f => fmap[F] (map f);
is_functor := F ◯ G
}.
Next Obligation.
destruct G; simpl.
apply fobj_respects.
apply fobj_related0.
Defined.
Next Obligation.
destruct G; simpl.
rewrite <- !fmap_comp.
apply fmap_respects.
apply fmap_related0.
Defined.


Theorem EndoFunctor_Denotes {C : Category} (F : C ⟶ C) : EndoFunctor F.
Proof. hammer_hook "Endo" "Endo.EndoFunctor_Denotes". construct; cat. Qed.
