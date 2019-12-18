From Hammer Require Import Hammer.














From Coq Require Import List.
From Coq.ssr Require Import ssreflect.
From compcert Require Import Alphabet.

Class IsValidator (P : Prop) (b : bool) :=
is_validator : b = true -> P.
Hint Mode IsValidator + - : typeclass_instances.

Instance is_validator_true : IsValidator True true.
Proof. hammer_hook "Validator_classes" "Validator_classes.is_validator_true". done. Qed.

Instance is_validator_false : IsValidator False false.
Proof. hammer_hook "Validator_classes" "Validator_classes.is_validator_false". done. Qed.

Instance is_validator_eq_true b :
IsValidator (b = true) b.
Proof. hammer_hook "Validator_classes" "Validator_classes.is_validator_eq_true". done. Qed.

Instance is_validator_and P1 b1 P2 b2 `{IsValidator P1 b1} `{IsValidator P2 b2}:
IsValidator (P1 /\ P2) (if b1 then b2 else false).
Proof. hammer_hook "Validator_classes" "Validator_classes.is_validator_and". by split; destruct b1, b2; apply is_validator. Qed.

Instance is_validator_comparable_leibniz_eq A (C:Comparable A) (x y : A) :
ComparableLeibnizEq C ->
IsValidator (x = y) (compare_eqb x y).
Proof. hammer_hook "Validator_classes" "Validator_classes.is_validator_comparable_leibniz_eq". intros ??. by apply compare_eqb_iff. Qed.

Instance is_validator_comparable_eq_impl A `(Comparable A) (x y : A) P b :
IsValidator P b ->
IsValidator (x = y -> P) (if compare_eqb x y then b else true).
Proof. hammer_hook "Validator_classes" "Validator_classes.is_validator_comparable_eq_impl".
intros Hval Val ->. rewrite /compare_eqb compare_refl in Val. auto.
Qed.

Lemma is_validator_forall_finite A P b `(Finite A) :
(forall (x : A), IsValidator (P x) (b x)) ->
IsValidator (forall (x : A), P x) (forallb b all_list).
Proof. hammer_hook "Validator_classes" "Validator_classes.is_validator_forall_finite".
move=> ? /forallb_forall Hb ?.
apply is_validator, Hb, all_list_forall.
Qed.


Hint Extern 2 (IsValidator (forall x : ?A, _) _) =>
eapply (is_validator_forall_finite _ _ (fun (x:A) => _))
: typeclass_instances.


Hint Extern 2 (IsValidator (match ?u with _ => _ end) ?b0) =>
let b := fresh "b" in
unshelve notypeclasses refine (let b : bool := _ in _);
[destruct u; intros; shelve|];
unify b b0;
unfold b; destruct u; clear b
: typeclass_instances.


Hint Extern 100 (IsValidator ?X _) => unfold X
: typeclass_instances.
