From Hammer Require Import Hammer.

Require Import Coq.Setoids.Setoid.
Require Import ExtLib.Structures.Proper.

Set Universe Polymorphism.


Class type@{t} (T : Type@{t}) : Type :=
{ equal : T -> T -> Prop
; proper : T -> Prop
}.

Definition type_from_equal@{t} {T : Type@{t}} (r : T -> T -> Prop) : type@{t} T :=
{| equal := r
; proper := fun x => r x x
|}.

Definition type_libniz@{t} (T : Type@{t}) : type@{t} T :=
{| equal := @eq T
; proper := fun _ => True
|}.

Existing Class proper.

Section type.
Universe u.
Context {T : Type@{u}}.
Variable tT : type T.

Class typeOk@{} :=
{ only_proper : forall x y, equal x y -> proper x /\ proper y
; equiv_prefl :> PReflexive proper equal
; equiv_sym :> Symmetric equal
; equiv_trans :> Transitive equal
}.

Global Instance proper_left@{} :
typeOk ->
forall x y : T, equal x y -> proper x.
Proof. hammer_hook "Type" "Type.proper_left".
clear. intros.
match goal with
| H : equal _ _ |- _ => eapply only_proper in H
end; intuition.
Qed.
Global Instance proper_right@{} :
typeOk ->
forall x y : T, equal x y -> proper y.
Proof. hammer_hook "Type" "Type.proper_right".
clear. intros.
match goal with
| H : equal _ _ |- _ => eapply only_proper in H
end; intuition.
Qed.

End type.


Definition type1@{d r z} (F : Type@{d} -> Type@{r}) : Type@{z} :=
forall {T:Type@{d}}, type@{d} T -> type@{r} (F T).

Definition type2@{t u v z} (F : Type@{t} -> Type@{u} -> Type@{v}) : Type@{z} :=
forall {T:Type@{t}}, type T -> forall {U:Type@{u}}, type U -> type (F T U).

Definition type3@{t u v w z} (F : Type@{t} -> Type@{u} -> Type@{v} -> Type@{w}) : Type@{z} :=
forall {T:Type@{t}}, type T -> forall {U:Type@{u}}, type U -> forall {V:Type@{w}}, type V ->  type (F T U V).

Definition typeOk1@{d r z} (F : Type@{d} -> Type@{r}) (tF : type1@{d r z} F) : Type@{z} :=
forall (T : Type@{d}) tT, @typeOk T tT -> typeOk (tF _ tT).

Definition typeOk2@{t u v z}
(F : Type@{t} -> Type@{u} -> Type@{v}) (tF : type2@{t u v z} F)
: Type@{z} :=
forall (T : Type@{t}) (tT : type@{t} T), @typeOk@{t} T tT -> typeOk1@{u v z} _ (tF _ tT).

Definition typeOk3@{t u v w z} F (tF : type3 F) : Type@{z} :=
forall (T : Type@{t}) (tT : type T), @typeOk@{t} T tT -> typeOk2@{u v w z} _ (tF _ tT).

Existing Class type1.
Existing Class type2.
Existing Class type3.

Global Instance type_type1 F (tF : type1 F) T (tT : type T) : type (F T) :=
tF _ tT.

Global Instance type1_type2 F (tF : type2 F) T (tT : type T) : type1 (F T) :=
tF _ tT.

Global Instance type2_type3 F (tF : type3 F) T (tT : type T) : type2 (F T) :=
tF _ tT.

Class Oktype T : Type :=
{ the_type :> type T
; the_proof :> typeOk the_type
}.

Coercion the_type : Oktype >-> type.

Global Instance typeOk_typeOk1 F (tF : type1 F) T (tT : type T) : type (F T) :=
tF _ tT.

Global Instance typeOk1_typeOk2 F (tF : type2 F) T (tT : type T) : type1 (F T) :=
tF _ tT.

Global Instance typeOk2_typeOk3 F (tF : type3 F) T (tT : type T) : type2 (F T) :=
tF _ tT.


Section typeOk_from_equal.
Universe u.
Context {T : Type@{u}} (r : relation T).
Hypothesis p : forall x y, r x y -> r x x /\ r y y.
Hypothesis sym : Symmetric r.
Hypothesis trans : Transitive r.

Theorem typeOk_from_equal@{} : typeOk (type_from_equal r).
Proof. hammer_hook "Type" "Type.typeOk_from_equal".
constructor; auto.
{ simpl. red. auto. }
Qed.
End typeOk_from_equal.

Theorem typeOk_libniz@{u} (T : Type@{u}) : typeOk (type_libniz T).
Proof. hammer_hook "Type" "Type.typeOk_libniz".
constructor; unfold equal, type_libniz; auto with typeclass_instances.
{ split; exact I. }
Qed.


