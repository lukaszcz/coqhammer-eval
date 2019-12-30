From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Naturality.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Transform.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.



Class Transform := {
transform {x} : F x ~> G x;

naturality {x y} (f : x ~> y) :
fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;

naturality_sym {x y} (f : x ~> y) :
transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
}.

Global Program Instance Transform_Setoid : Setoid Transform.

End Transform.

Arguments transform {_ _ _ _} _ _.
Arguments naturality
{_ _ _ _ _ _ _ _}, {_ _ _ _} _ {_ _ _}, {_ _ _ _} _ _ _ _.
Arguments naturality_sym
{_ _ _ _ _ _ _ _}, {_ _ _ _} _ {_ _ _}, {_ _ _ _} _ _ _ _.

Bind Scope transform_scope with Transform.
Delimit Scope transform_type_scope with transform_type.
Delimit Scope transform_scope with transform.
Open Scope transform_type_scope.
Open Scope transform_scope.

Notation "F ⟹ G" := (@Transform _ _ F%functor G%functor)
(at level 90, right associativity) : transform_type_scope.

Notation "transform[ F ]" := (@transform _ _ _ _ F%transform)
(at level 9, only parsing, format "transform[ F ]") : morphism_scope.
Notation "naturality[ F ]" := (@naturality _ _ _ _ F%transform)
(at level 9, only parsing, format "naturality[ F ]") : morphism_scope.

Coercion transform : Transform >-> Funclass.

Ltac transform :=
unshelve (refine {| transform := _ |}; simpl; intros).

Corollary fun_id_left {C D : Category} {F : C ⟶ D} : Id ◯ F ⟹ F.
Proof. hammer_hook "Transformation" "Transformation.fun_id_left". transform; simpl; intros; cat. Qed.

Corollary fun_id_left_sym {C D : Category} {F : C ⟶ D} : F ⟹ Id ◯ F.
Proof. hammer_hook "Transformation" "Transformation.fun_id_left_sym". transform; simpl; intros; cat. Qed.

Corollary fun_id_right {C D : Category} {F : C ⟶ D} : F ◯ Id ⟹ F.
Proof. hammer_hook "Transformation" "Transformation.fun_id_right". transform; simpl; intros; cat. Qed.

Corollary fun_id_right_sym {C D : Category} {F : C ⟶ D} : F ⟹ F ◯ Id.
Proof. hammer_hook "Transformation" "Transformation.fun_id_right_sym". transform; simpl; intros; cat. Qed.

Corollary fun_comp_assoc {C D E B : Category}
{F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : F ◯ (G ◯ H) ⟹ (F ◯ G) ◯ H.
Proof. hammer_hook "Transformation" "Transformation.fun_comp_assoc". transform; simpl; intros; cat. Qed.

Corollary fun_comp_assoc_sym {C D E B : Category}
{F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : (F ◯ G) ◯ H ⟹ F ◯ (G ◯ H).
Proof. hammer_hook "Transformation" "Transformation.fun_comp_assoc_sym". transform; simpl; intros; cat. Qed.

Program Definition whisker_right {C D : Category} {F G : C ⟶ D} `(N : F ⟹ G)
{E : Category} (X : E ⟶ C) : F ◯ X ⟹ G ◯ X := {|
transform := fun x => N (X x);

naturality     := fun _ _ _ => naturality;
naturality_sym := fun _ _ _ => naturality_sym
|}.

Notation "N ⊲ F" := (whisker_right N F) (at level 10).

Program Definition whisker_left {C D : Category}
{E : Category} (X : D ⟶ E)
{F G : C ⟶ D} `(N : F ⟹ G) : X ◯ F ⟹ X ◯ G := {|
transform := fun x => fmap[X] (N x)
|}.
Next Obligation.
simpl; rewrite <- !fmap_comp;
apply fmap_respects, naturality.
Qed.
Next Obligation.
simpl; rewrite <- !fmap_comp;
apply fmap_respects, naturality_sym.
Qed.

Notation "F ⊳ N" := (whisker_left F N) (at level 10).



