From Hammer Require Import Hammer.

Require Import BinPos.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Proper.

Global Instance type_N : type N :=
{ equal := @eq N
; proper := fun _ => True
}.

Global Instance typeOk_N : typeOk type_N.
Proof. hammer_hook "N" "N.typeOk_N".
constructor.
{ compute; auto. }
{ compute; auto. }
{ compute; auto. }
{ compute. intros. etransitivity; eauto. }
Qed.

Global Instance N_proper (n : N) : proper n.
Proof. hammer_hook "N" "N.N_proper". exact I. Qed.
