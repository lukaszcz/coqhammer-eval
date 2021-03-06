From Hammer Require Import Hammer.

Set Implicit Arguments.

Require Import Le.
Require Import Lt.
Require Import Arith.
Require Import Recdef.
Require Coq.Program.Wf.
Require List.

Section measure_wf.



Variables T M: Set.
Variable R: M -> M -> Prop.
Hypothesis wf: well_founded R.
Variable m: T -> M.

Definition MR (x y: T): Prop := R (m x) (m y).

Lemma measure_wf: well_founded MR.
Proof with auto. hammer_hook "fix_measure_utils" "fix_measure_utils.measure_wf".
unfold well_founded.
cut (forall a: M, forall a0: T, m a0 = a -> Acc MR a0).
intros.
apply (H (m a))...
apply (@well_founded_ind M R wf (fun mm => forall a, m a = mm -> Acc MR a)).
intros.
apply Acc_intro.
intros.
unfold MR in H1.
rewrite H0 in H1.
apply (H (m y))...
Defined.

End measure_wf.

Section Fix_measure_rects.

Variable A: Set.
Variable R: A -> A -> Prop.
Variable Rwf: well_founded R.
Variable P: A -> Type.
Variable f: forall x: A, (forall y: { y: A | R y x }, P (proj1_sig y)) -> P x.

Lemma F_unfold x r:
Wf.Fix_F_sub A R P f x r =
f (fun y => Wf.Fix_F_sub A R P f (proj1_sig y) (Acc_inv r (proj2_sig y))).
Proof. hammer_hook "fix_measure_utils" "fix_measure_utils.F_unfold". intros. case r; auto. Qed.



Lemma F_sub_rect
(Q: forall x, P x -> Type)
(inv: forall x: A,
(forall (y: A) (H: R y x) (a: Acc R y),
Q y (Wf.Fix_F_sub A R P f y a)) ->
forall (a: Acc R x),
Q x (f (fun y: {y: A | R y x} =>
Wf.Fix_F_sub A R P f (proj1_sig y) (Acc_inv a (proj2_sig y)))))
: forall x a, Q _ (Wf.Fix_F_sub A R P f x a).
Proof with auto. hammer_hook "fix_measure_utils" "fix_measure_utils.F_sub_rect".
set (R' := fun (x: A) => forall a, Q _ (Wf.Fix_F_sub A R P f x a)).
cut (forall x, R' x)...
apply (well_founded_induction_type Rwf).
subst R'.
simpl.
intros.
rewrite F_unfold...
Qed.



Hypothesis equiv_lowers:
forall x0 (g h: forall x: {y: A | R y x0}, P (proj1_sig x)),
(forall x p p', g (exist (fun y: A => R y x0) x p) = h (exist _ x p')) ->
f g = f h.



Lemma eq_F_sub x: forall (a a': Acc R x),
Wf.Fix_F_sub A R P f x a =
Wf.Fix_F_sub A R P f x a'.
Proof. hammer_hook "fix_measure_utils" "fix_measure_utils.eq_F_sub".
intro a.
pattern x, (Wf.Fix_F_sub A R P f x a).
apply F_sub_rect.
intros.
rewrite F_unfold.
apply equiv_lowers.
intros.
apply H.
assumption.
Qed.

Lemma unfold x:
Wf.Fix_sub A R Rwf P f x =
f (fun y => Wf.Fix_sub A R Rwf P f (proj1_sig y)).
Proof. hammer_hook "fix_measure_utils" "fix_measure_utils.unfold". intros. unfold Wf.Fix_sub.
rewrite F_unfold.
apply equiv_lowers.
intros.
apply eq_F_sub.
Qed.



Lemma rect
(Q: forall x, P x -> Type)
(inv: forall
(x: A)
(H: forall (y: A), R y x -> Q y (Wf.Fix_sub A R Rwf P f y))
(a: Acc R x),
Q x (f (fun y: {y: A | R y x} => Wf.Fix_sub A R Rwf P f (proj1_sig y))))
: forall x, Q _ (Wf.Fix_sub A R Rwf P f x).
Proof with auto. hammer_hook "fix_measure_utils" "fix_measure_utils.rect".
unfold Wf.Fix_sub.
intros.
apply F_sub_rect.
intros.
assert (forall y: A, R y x0 -> Q y (Wf.Fix_F_sub A R P f y (Rwf y)))...
set (inv x0 X0 a). clearbody q.
rewrite <- (equiv_lowers (fun y: {y: A | R y x0} => Wf.Fix_F_sub A R P f (proj1_sig y) (Rwf (proj1_sig y))) (fun y: {y: A | R y x0} => Wf.Fix_F_sub A R P f (proj1_sig y) (Acc_inv a (proj2_sig y))))...
intros.
apply eq_F_sub.
Qed.

End Fix_measure_rects.

Module Example.

Import List.

Definition tail (l: list nat): list nat :=
match l with
| nil => nil
| _ :: t => t
end.

Program Fixpoint bla (l: list nat) {measure (length l) lt}: nat :=
match l with
| nil => 3
| _ => bla (tail l) + 2
end.

Next Obligation.
destruct l.
elimtype False. apply H. reflexivity.
simpl. apply le_refl.
Qed.



Goal forall x, 3 <= bla x.
Proof with auto. hammer_hook "fix_measure_utils" "fix_measure_utils.Example.tail".
intro x.
pattern (bla x).
set (fun n : nat => 3 <= n).
unfold bla.
generalize x. clear x.
apply rect; intros.
destruct x0...
subst P.
simpl.
destruct x...
replace 3 with (3 + 0)...
apply plus_le_compat...
apply H.
unfold Wf.MR...
Qed.

End Example.
