From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Subcategory.

Context (C : Category).

Record Subcategory := {

sobj : C -> Type;


shom {x y : C} : sobj x -> sobj y -> (x ~> y) -> Type;


scomp {x y z : C} (ox : sobj x) (oy : sobj y) (oz : sobj z)
{f : y ~> z} {g : x ~> y} :
shom oy oz f -> shom ox oy g -> shom ox oz (f ∘ g);


sid {x : C} (ox : sobj x) : shom ox ox (@id C x)
}.

Variable S : Subcategory.


Program Definition Sub : Category := {|
obj     := { x : C & sobj S x };
hom     := fun x y => { f : `1 x ~> `1 y & shom S `2 x `2 y f };
homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
id      := fun x => (id; sid S `2 x);
compose := fun x y z f g  => (`1 f ∘ `1 g; scomp S `2 x `2 y `2 z `2 f `2 g)
|}.


Program Instance Incl : Sub ⟶ C := {
fobj := fun x => `1 x;
fmap := fun x y f => `1 f
}.



Definition Full : Type :=
∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y), shom S ox oy f.



Lemma Full_Implies_Full_Functor : Full -> Functor.Full Incl.
Proof. hammer_hook "Subcategory" "Subcategory.Full_Implies_Full_Functor".
unfold Full; intros.
construct.
- exists g.
destruct x, y.
apply X; auto.
- proper.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.



Definition Replete : Type :=
∀ (x : C) (ox : sobj S x) (y : C) (f : x ≅ y),
{ oy : sobj S y & shom S ox oy (to f) ∧ shom S oy ox (from f) }.



Definition Wide : Type := ∀ x : C, sobj S x.

End Subcategory.
