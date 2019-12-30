From Hammer Require Import Hammer.

Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.



Inductive RoofObj : Type := RNeg | RZero | RPos.

Inductive RoofHom : RoofObj -> RoofObj -> Type :=
| IdNeg   : RoofHom RNeg  RNeg
| ZeroNeg : RoofHom RZero RNeg
| IdZero  : RoofHom RZero RZero
| ZeroPos : RoofHom RZero RPos
| IdPos   : RoofHom RPos  RPos.

Definition RoofHom_inv_t : forall x y, RoofHom x y -> Prop.
Proof. hammer_hook "Roof" "Roof.RoofHom_inv_t".
intros [] [] f.
exact (f = IdNeg).
exact False.
exact False.
exact (f = ZeroNeg).
exact (f = IdZero).
exact (f = ZeroPos).
exact False.
exact False.
exact (f = IdPos).
Defined.

Corollary RoofHom_inv x y f : RoofHom_inv_t x y f.
Proof. hammer_hook "Roof" "Roof.RoofHom_inv". destruct f; reflexivity. Qed.

Lemma RNeg_RNeg_id (f : RoofHom RNeg RNeg) : f = IdNeg.
Proof. hammer_hook "Roof" "Roof.RNeg_RNeg_id". exact (RoofHom_inv _ _ f). Qed.

Lemma RZero_RPos_id (f : RoofHom RZero RPos) : f = ZeroPos.
Proof. hammer_hook "Roof" "Roof.RZero_RPos_id". exact (RoofHom_inv _ _ f). Qed.

Lemma RNeg_RZero_absurd : RoofHom RNeg RZero -> False.
Proof. hammer_hook "Roof" "Roof.RNeg_RZero_absurd". inversion 1. Qed.

Hint Extern 4 => contradiction RNeg_RZero_absurd : roof_laws.

Lemma RPos_RZero_absurd : RoofHom RPos RZero -> False.
Proof. hammer_hook "Roof" "Roof.RPos_RZero_absurd". inversion 1. Qed.

Hint Extern 4 => contradiction RPos_RZero_absurd : roof_laws.

Lemma RNeg_RPos_absurd : RoofHom RNeg RPos -> False.
Proof. hammer_hook "Roof" "Roof.RNeg_RPos_absurd". inversion 1. Qed.

Hint Extern 4 => contradiction RNeg_RPos_absurd : roof_laws.

Lemma RPos_RNeg_absurd : RoofHom RPos RNeg -> False.
Proof. hammer_hook "Roof" "Roof.RPos_RNeg_absurd". inversion 1. Qed.

Hint Extern 4 => contradiction RPos_RNeg_absurd : roof_laws.

Program Definition Roof : Category := {|
obj    := RoofObj;
hom    := RoofHom;

homset := fun x y => {| equiv := fun (f g : RoofHom x y) => True |};
id     := fun x => match x return RoofHom x x with
| RNeg  => IdNeg
| RZero => IdZero
| RPos  => IdPos
end
|}.
Next Obligation.
destruct x, y, z;
try constructor;
try inversion f;
try inversion g.
Defined.
