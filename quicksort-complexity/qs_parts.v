From Hammer Require Import Hammer.

Set Implicit Arguments.

From QuicksortComplexity Require Import util.
Require Import Le.
Require Import Plus.
Require Import Lt.
Require Import Arith.
From QuicksortComplexity Require Import monoid_expec.
Require Import List.
From QuicksortComplexity Require Import monads.
From QuicksortComplexity Require Import list_utils.
Require Import Coq.Program.Wf.
From QuicksortComplexity Require Import monoid_monad_trans.
From QuicksortComplexity Require Import nat_seqs.
From QuicksortComplexity Require Import monoid_tree_monad.
From QuicksortComplexity Require qs_definitions.
From QuicksortComplexity Require fix_measure_utils.
From QuicksortComplexity Require Import nat_below.
Require Coq.Vectors.Vector.

Import qs_definitions.mon_nondet.

Set Shrink Obligations.

Section contents.

Variable M: Monad.

Variables (X: Set) (pick: forall T: Set, ne_list.L T -> M T) (cmp: X -> X -> M comparison).

Definition lowRecPart n (t: Vector.t X (S n)) (i: natBelow (S n)) (part: {p: Partitioning X |
Permutation.Permutation (p Eq ++ p Lt ++ p Gt) (vec.to_list (vec.remove t i))}) :=
low <- qs cmp pick (proj1_sig part Lt);
upp <- qs cmp pick (proj1_sig part Gt);
ret (low ++ vec.nth t i :: proj1_sig part Eq ++ upp).

Definition partitionPart n (t: Vector.t X (S n)) (i: natBelow (S n))
:= partition M cmp (vec.nth t i) (vec.to_list (vec.remove t i)) >>= lowRecPart t i.

Definition selectPivotPart n (t: Vector.t X (S n)) := pick (ne_list.from_vec (vec.nats 0 (S n))) >>= partitionPart t.

Lemma selectPivotPart_eq n m (t: Vector.t X (S n)) (t': Vector.t X (S m)): vec.to_list t = vec.to_list t' ->
selectPivotPart t = selectPivotPart t'.
Proof with auto. hammer_hook "qs_parts" "qs_parts.selectPivotPart_eq".
intros.
pose proof (vec.length t).
rewrite H in H0.
rewrite vec.length in H0.
inversion H0.
subst. clear H0.
rewrite (vec.eq_as_lists t t')...
Qed.

Definition body n (v: Vector.t X n) :=
match v with
| Vector.nil => ret nil
| l => selectPivotPart l
end.

Definition raw_body (l0: list X) (qs: {l': list X | length l' < length l0} -> M (list X)) :=
match l0 as l1 return (l1 = l0 -> M (list X)) with
| nil => fun _ => ret nil
| h :: t => fun e =>
i <- pick (ne_list.from_vec (vec.nats 0 (length (h :: t))));
part <- partition M cmp (vec.nth (vec.from_list (h :: t)) i) (vec.to_list (vec.remove (vec.from_list (h :: t)) i));
low <- qs (exist (fun l': list X => length l' < length l0) (proj1_sig part Lt) (qs_definitions.mon_nondet.qs_obligation_1 M (fun l H => qs (exist _ l H)) e i part));
upp <- qs (exist (fun l': list X => length l' < length l0) (proj1_sig part Gt) (qs_definitions.mon_nondet.qs_obligation_2 M (fun l H => qs (exist _ l H)) e i part));
ret (low ++ vec.nth (vec.from_list (h :: t)) i :: proj1_sig part Eq ++ upp)
end refl_equal.

Variable e: extMonad M.

Definition raw_body_ext (l: list X) (qs qs': {l': list X | length l' < length l} -> M (list X)):
(forall x y, proj1_sig x = proj1_sig y -> qs x = qs' y) -> raw_body l qs = raw_body l qs'.
Proof with auto. hammer_hook "qs_parts" "qs_parts.raw_body_ext".
unfold raw_body.
intros.
destruct l...
apply e. intro.
apply e. intro.
apply bind_eqq...
intro.
apply bind_eqq...
intro...
Qed.

Lemma bodies x0:
raw_body x0 (fun y: {y: list X | length y < length x0} => qs (M:=M) cmp pick (proj1_sig y)) = body (vec.from_list x0).
Proof. hammer_hook "qs_parts" "qs_parts.bodies".
intros.
unfold raw_body, body, selectPivotPart, partitionPart, lowRecPart.
destruct x0; reflexivity.
Qed.

Lemma toBody (l: list X): qs cmp pick l = body (vec.from_list l).
Proof with auto. hammer_hook "qs_parts" "qs_parts.toBody".
unfold qs.
fold raw_body.
rewrite fix_measure_utils.unfold.
rewrite <- bodies.
unfold qs. fold raw_body...
intros.
apply raw_body_ext.
intros.
destruct x. destruct y.
simpl in H0.
subst...
Qed.

Lemma toBody_cons (n: nat) (v: Vector.t X (S n)): body v = selectPivotPart v.
intros.
rewrite (vec.eq_cons v).
simpl.
reflexivity.
Qed.

Lemma rect (Q: list X -> M (list X) -> Type):
(Q nil (ret nil)) ->
(forall n (v: Vector.t X (S n)), (forall y, length y < S n -> Q y (qs cmp pick y)) -> Q (vec.to_list v) (selectPivotPart v)) ->
forall x, Q x (qs cmp pick x).
Proof with auto. hammer_hook "qs_parts" "qs_parts.rect".
intros.
unfold qs.
match goal with
|- context C [Fix_sub ?A ?R ?P ?p ?f ?x] =>
let folded := context C [ Fix_sub A R P p raw_body x ] in
change folded
end.
apply fix_measure_utils.rect.
intros.
apply raw_body_ext.
intros.
destruct x1. destruct y.
simpl in H0.
subst...
intros.
erewrite raw_body_ext.
rewrite bodies.
unfold body.
destruct x0...
simpl.
rewrite <- (vec.list_round_trip (x0 :: x1)).
apply X1.
intros.
unfold qs. fold raw_body...
intros.
unfold qs. fold raw_body.
f_equal; assumption.
Qed.

Lemma rect_using_lists (Q: list X -> M (list X) -> Type):
(Q nil (ret nil)) ->
(forall h t, (forall y, length y <= length t -> Q y (qs cmp pick y)) -> Q (h::t) (selectPivotPart (vec.from_list (h::t)))) ->
forall x, Q x (qs cmp pick x).
Proof with auto with arith. hammer_hook "qs_parts" "qs_parts.rect_using_lists".
intros.
apply rect...
intros.
simpl in X1.
rewrite (vec.eq_cons v).
simpl.
assert (forall y : list X, length y <= length (vec.to_list (vec.tail v)) -> Q y (qs cmp pick y)).
intros.
apply X2.
rewrite vec.length in H...
pose proof (X1 (vec.head v) (vec.to_list (vec.tail v)) X3).
pose proof (selectPivotPart_eq (Vector.cons (vec.head v) (vec.from_list (vec.to_list (vec.tail v)))) (Vector.cons (vec.head v) (vec.tail v))).
rewrite <- H...
simpl.
rewrite vec.list_round_trip...
Qed.

End contents.
