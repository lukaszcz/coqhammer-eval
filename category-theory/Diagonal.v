From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Diagonal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Corollary Diagonal_Unique `(C : Category) {D : Category} (d : D) :
Diagonal C d ≈[Cat] Const d ∘[Cat] one.
Proof. hammer_hook "Diagonal" "Diagonal.Diagonal_Unique". exists (fun _ => iso_id); simpl; intros; cat. Qed.
