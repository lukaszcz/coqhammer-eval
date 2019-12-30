From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Instance.Cones.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Theorem Cones_to_Comma `(F : J ⟶ C) :
Cones F ⟶ (Diagonal J ↓ @Const Fun F).
Proof. hammer_hook "Comma" "Comma.Cones_to_Comma".
functor; simpl; intros.
- exists (vertex_obj, ()).
transform; simpl; intros.
+ apply vertex_map.
+ abstract (rewrite id_right; apply ump_cones).
+ abstract (rewrite id_right; symmetry; apply ump_cones).
- exists (`1 f, ()); abstract (simpl; intros; cat).
- abstract proper.
- abstract cat.
- abstract cat.
Defined.

Theorem Cones_from_Comma `(F : J ⟶ C) :
(Diagonal J ↓ @Const Fun F) ⟶ Cones F.
Proof. hammer_hook "Comma" "Comma.Cones_from_Comma".
functor; simpl; intros.
- construct; simpl; intros.
+ exact (fst ``X).
+ exact (transform[`2 X] _).
+ abstract (rewrite (naturality[`2 X]); cat).
- destruct f; simpl in *.
exists (fst x0); abstract (intros; rewrite e; cat).
- abstract proper.
- abstract cat.
- abstract cat.
Defined.



Theorem Cones_Comma `(F : J ⟶ C) :
Cones F ≅[Cat] (Diagonal J ↓ @Const Fun F).
Proof. hammer_hook "Comma" "Comma.Cones_Comma".
isomorphism; simpl; intros.
- apply Cones_to_Comma.
- apply Cones_from_Comma.
- constructive.
+ exists (id, ()); abstract cat.
+ exists (id, ()); abstract cat.
+ abstract (simpl; cat).
+ abstract (simpl; cat).
+ abstract (simpl; cat).
- constructive.
+ exists id; abstract (intros; cat).
+ exists id; abstract (intros; cat).
+ abstract (simpl; cat).
+ abstract (simpl; cat).
+ abstract (simpl; cat).
Qed.
