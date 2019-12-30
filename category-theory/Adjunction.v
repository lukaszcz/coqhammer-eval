From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Naturality.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.



Section Adjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Reserved Notation "⌊ f ⌋".
Reserved Notation "⌈ f ⌉".

Class Adjunction := {
adj {x y} : F x ~{C}~> y ≊ x ~{D}~> U y
where "⌊ f ⌋" := (to   adj f)
and "⌈ f ⌉" := (from adj f);

to_adj_nat_l {x y z} (f : F y ~> z) (g : x ~> y) :
⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
to_adj_nat_r {x y z} (f : y ~> z) (g : F x ~> y) :
⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋;

from_adj_nat_l {x y z} (f : y ~> U z) (g : x ~> y) :
⌈f ∘ g⌉ ≈ ⌈f⌉ ∘ fmap[F] g;
from_adj_nat_r {x y z} (f : y ~> z) (g : x ~> U y) :
⌈fmap[U] f ∘ g⌉ ≈ f ∘ ⌈g⌉
}.

Context `{@Adjunction}.

Notation "⌊ f ⌋" := (to adj f).
Notation "⌈ f ⌉" := (from adj f).

Corollary adj_univ `(f : F x ~> y) (g : x ~> U y) :
f ≈ ⌈g⌉ ↔ ⌊f⌋ ≈ g.
Proof. hammer_hook "Adjunction" "Adjunction.adj_univ".
split; intros.
rewrite X.
sapply (@iso_to_from Sets _ _ (@adj _ x y)).
rewrite <- X.
symmetry.
sapply (@iso_from_to Sets _ _ (@adj _ x y)).
Qed.

Corollary to_adj_comp_law {x y} (f : F x ~> y) :
⌈⌊f⌋⌉ ≈ f.
Proof. hammer_hook "Adjunction" "Adjunction.to_adj_comp_law". sapply (@iso_from_to Sets _ _ (@adj _ x y) f). Qed.

Corollary from_adj_comp_law {x y} (f : x ~> U y) :
⌊⌈f⌉⌋ ≈ f.
Proof. hammer_hook "Adjunction" "Adjunction.from_adj_comp_law". sapply (@iso_to_from Sets _ _ (@adj _ x y) f). Qed.

Definition unit   {x : D} : x ~> U (F x) := ⌊id⌋.
Definition counit {x : C} : F (U x) ~> x := ⌈id⌉.

Notation "'η'" := unit.
Notation "'ε'" := counit.

Corollary from_adj_unit {x} :
⌈η⌉ ≈ id[F x].
Proof. hammer_hook "Adjunction" "Adjunction.from_adj_unit". sapply (@iso_from_to Sets _ _ (@adj _ x (F x))). Qed.

Corollary to_adj_counit {x} :
⌊ε⌋ ≈ id[U x].
Proof. hammer_hook "Adjunction" "Adjunction.to_adj_counit". sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)). Qed.

Corollary counit_comp {x y} (f : F x ~> y) :
ε ∘ fmap[F] (fmap[U] f) ≈ f ∘ ε.
Proof. hammer_hook "Adjunction" "Adjunction.counit_comp".
unfold counit.
rewrite <- from_adj_nat_l.
rewrite <- from_adj_nat_r.
rewrite id_left, id_right.
reflexivity.
Qed.

Corollary unit_comp {x y} (f : x ~> U y) :
fmap[U] (fmap[F] f) ∘ η ≈ η ∘ f.
Proof. hammer_hook "Adjunction" "Adjunction.unit_comp".
unfold unit.
rewrite <- to_adj_nat_l.
rewrite <- to_adj_nat_r.
rewrite id_left, id_right.
reflexivity.
Qed.

Corollary adj_univ_impl {x y} (f : F x ~> y) (g : x ~> U y) :
f ≈ ε ∘ fmap[F] g ↔ ⌊f⌋ ≈ g.
Proof. hammer_hook "Adjunction" "Adjunction.adj_univ_impl".
unfold counit.
split; intros.
rewrite X; clear X.
rewrite <- from_adj_nat_l.
rewrite id_left.
apply from_adj_comp_law.
rewrite <- X; clear X.
rewrite <- from_adj_nat_l.
rewrite id_left.
symmetry.
apply to_adj_comp_law.
Qed.

Corollary to_adj_unit {x y} (f : F x ~> y) :
⌊f⌋ ≈ fmap[U] f ∘ η.
Proof. hammer_hook "Adjunction" "Adjunction.to_adj_unit".
rewrite <- (id_right f).
rewrite to_adj_nat_r.
rewrite fmap_comp; cat.
Qed.

Corollary from_adj_counit {x y} (f : x ~> U y) :
⌈f⌉ ≈ ε ∘ fmap[F] f.
Proof. hammer_hook "Adjunction" "Adjunction.from_adj_counit".
rewrite <- (id_left f).
rewrite from_adj_nat_l.
rewrite fmap_comp; cat.
Qed.

Corollary counit_fmap_unit  {x} :
ε ∘ fmap[F] η ≈ id[F x].
Proof. hammer_hook "Adjunction" "Adjunction.counit_fmap_unit".
unfold unit, counit.
rewrite <- from_adj_nat_l; cat.
sapply (@iso_from_to Sets _ _ (@adj _ x (F x))).
Qed.

Corollary fmap_counit_unit  {x} :
fmap[U] ε ∘ η ≈ id[U x].
Proof. hammer_hook "Adjunction" "Adjunction.fmap_counit_unit".
unfold unit, counit.
rewrite <- to_adj_nat_r; cat.
sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)).
Qed.

Corollary fmap_from_adj_unit {x y} (f : x ~{D}~> y) : fmap[F] f ≈ ⌈η ∘ f⌉.
Proof. hammer_hook "Adjunction" "Adjunction.fmap_from_adj_unit".
unfold unit.
rewrite from_adj_nat_l.
rewrite to_adj_comp_law; cat.
Qed.

Corollary fmap_to_adj_counit {x y} (f : x ~{C}~> y) : fmap[U] f ≈ ⌊f ∘ ε⌋.
Proof. hammer_hook "Adjunction" "Adjunction.fmap_to_adj_counit".
unfold counit.
rewrite to_adj_nat_r.
rewrite from_adj_comp_law; cat.
Qed.


Theorem adj_monic  {x y} (f : F x ~> y) c (g h : c ~> x) :
Faithful F -> Monic f ->
⌊f⌋ ∘ g ≈ ⌊f⌋ ∘ h -> g ≈ h.
Proof. hammer_hook "Adjunction" "Adjunction.adj_monic".
intros.
rewrite <- !to_adj_nat_l in X1.
pose proof (monic (Monic:=@iso_to_monic Sets _ _ (@adj H c y))
{| carrier   := Datatypes.unit
; is_setoid := {| equiv := eq |} |}
{| morphism  := fun _ => f ∘ fmap[F] g |}
{| morphism  := fun _ => f ∘ fmap[F] h |}) as X2;
simpl in X2.
apply X.
apply X0.
apply X2; intros.
exact X1.
exact tt.
Qed.

Corollary to_adj_respects {x y} (f g : F x ~{C}~> y) :
f ≈ g -> ⌊f⌋ ≈ ⌊g⌋.
Proof. hammer_hook "Adjunction" "Adjunction.to_adj_respects". intros; now rewrites. Qed.

Corollary from_adj_respects {x y} (f g : x ~{D}~> U y) :
f ≈ g -> ⌈f⌉ ≈ ⌈g⌉.
Proof. hammer_hook "Adjunction" "Adjunction.from_adj_respects". intros; now rewrites. Qed.

End Adjunction.

Arguments Adjunction {C D} F%functor U%functor.

Bind Scope adjunction_scope with Adjunction.
Delimit Scope adjunction_type_scope with adjunction_type.
Delimit Scope adjunction_scope with adjunction.
Open Scope adjunction_type_scope.
Open Scope adjunction_scope.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 59) : category_scope.
Notation "adj[ A ]" := (@adj _ _ _ _ A _ _)
(at level 9, format "adj[ A ]") : morphism_scope.






