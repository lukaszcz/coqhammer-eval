From Hammer Require Import Hammer.


















From Tait Require Import minlog_mode.

Ltac dcase x := generalize (refl_equal x); pattern x at -1; case x.

Inductive nc_type (A:Set) : Prop := nc : A -> nc_type A.
Arguments nc [A].
Notation " t ! " := (nc_type t) (at level 50).

Inductive existsnc_t (A : Prop) (P : A -> Type) : Type :=
existsnc_I : forall x : A, P x -> existsnc_t A P.

Notation "'existsnc' x : t , p" := (existsnc_t (t!) (fun x => p))
(at level 200, x ident) : type_scope.

Notation "'forallnc' x : t , p" := (forall x:t!,p)
(at level 200, x ident) : type_scope.

Notation "'letnc' x := y 'in' p" :=
(forall x, nc x = y -> p)
(at level 200, x ident) : type_scope.

Ltac existsnc_i wit := match goal with
|- (existsnc_t ?A ?P) => apply (existsnc_I A P (nc wit))
end.

Set Implicit Arguments.

Axiom ProofRelevance : forall (A:Set)(a b:A), nc a = nc b -> a = b.

Lemma nc_ex : forall (A:Set)(p: A!), exists r, p = nc r.
intros.
case p; intro r.
exists r.
reflexivity.
Defined.

Definition nc1 (A B:Set)(f:A->B) :=
fun (a:A!) => let (a'):=a in nc (f a').

Check nc1.
Check (nc1 pred).

Definition nc2 (A B C:Set)(f:A->B->C) :=
fun (a:A!)(b:B!) => let (a'):=a in let (b'):=b in nc (f a' b').

Check nc2.
Check (nc2 plus).
Check (nc2 plus (nc 0) (nc 3)).
Eval compute in (nc2 plus (nc 0) (nc 3)).

Definition nc3 (A B C D:Set)(f:A->B->C->D) :=
fun (a:A!)(b:B!)(c:C!) =>
let (a'):=a in let (b'):=b in let (c'):=c in nc (f a' b' c').

Definition ncP (A:Set)(P:A->Prop) :=
fun (a:A!) => letnc a':=a in P a'.

Definition ncP2 (A B:Set)(P:A->B->Prop) :=
fun (a:A!)(b:B!) => letnc a':=a in letnc b':=b in P a' b'.

Unset Implicit Arguments.



Ltac ncsimp := match goal with
|H : (nc _ = nc _) |- _ =>

generalize (ProofRelevance H); clear H; intro H
|H : (letnc id := nc ?t in _) |- _ =>
generalize (H t (refl_equal (nc t))); clear H; intro H
| |- nc _ = nc _ => f_equal
end.

Ltac nc:=intros;
repeat (progress (match goal with
| a:(_ !) |-_ =>
(unfold a in *; clear a) ||
(dcase a; intro; intro; subst)
end));
unfold nc1, nc2 in *; repeat ncsimp; try subst.

Ltac nc2:= match goal with
|H : context [match ?t with nc _ => _ end] |- _ =>
dcase t; intro;
let H' := fresh in
(intro H'; subst || (rewrite_all H'; clear H'))
|H : (letnc id := ?t in _) |- _ =>
elim (nc_ex t); intro ;
let H':= fresh in
(intro H'; subst || (rewrite_all H';clear H'))
end.



Section ProofRelevance.

Inductive test : Prop := A | B :test.

Lemma EqPropCons_ProofIrr :
A=B <-> forall (P:Prop)(p p':P), p = p'.
split.
intros.
set (discr := fun a => match a with A => p | B => p' end).
exact
(eq_ind A
(fun a : test => discr A = discr a)
(refl_equal p) B H).
intros.
apply (H _ A B).
Qed.



Lemma ProofIrr_NoHope :
(forall (P:Prop)(p p':P), p = p') <-> nc 0 = nc 1.
Proof. hammer_hook "nc" "nc.ProofIrr_NoHope".
split.
intro.
apply H.
intros.
set (discr := fun a => match a with
| nc O => p
| nc (S _) => p' end).
exact
(eq_ind (nc 0)
(fun a => discr (nc 0) = discr a)
(refl_equal p) (nc 1) H).
Qed.



End ProofRelevance.
