From Hammer Require Import Hammer.




















From compcert Require Import Coqlib.

Module BE.

Definition bool_eq {A: Type} (x y: A) : Type := bool.

Ltac bool_eq_base x y :=
change (bool_eq x y);
match goal with
| [ H: forall (x y: ?A), bool |- @bool_eq ?A x y ] => exact (H x y)
| [ H: forall (x y: ?A), {x=y} + {x<>y}  |- @bool_eq ?A x y ] => exact (proj_sumbool (H x y))
| _ => idtac
end.

Ltac bool_eq_case :=
match goal with
| |- bool_eq (?C ?x1 ?x2 ?x3 ?x4) (?C ?y1 ?y2 ?y3 ?y4) =>
refine (_ && _ && _ && _); [bool_eq_base x1 y1|bool_eq_base x2 y2|bool_eq_base x3 y3|bool_eq_base x4 y4]
| |- bool_eq (?C ?x1 ?x2 ?x3) (?C ?y1 ?y2 ?y3) =>
refine (_ && _ && _); [bool_eq_base x1 y1|bool_eq_base x2 y2|bool_eq_base x3 y3]
| |- bool_eq (?C ?x1 ?x2) (?C ?y1 ?y2) =>
refine (_ && _); [bool_eq_base x1 y1|bool_eq_base x2 y2]
| |- bool_eq (?C ?x1) (?C ?y1) => bool_eq_base x1 y1
| |- bool_eq ?C ?C => exact true
| |- bool_eq _ _ => exact false
end.

Ltac bool_eq :=
match goal with
| [ |- ?A -> ?A -> bool ] =>
let f := fresh "rec" in let x := fresh "x" in let y := fresh "y" in
fix f 1; intros x y; change (bool_eq x y); destruct x, y; bool_eq_case
| [ |- _ -> _ ] =>
let eq := fresh "eq" in intro eq; bool_eq
end.

Lemma proj_sumbool_is_true:
forall (A: Type) (f: forall (x y: A), {x=y} + {x<>y}) (x: A),
proj_sumbool (f x x) = true.
Proof. hammer_hook "BoolEqual" "BoolEqual.BE.proj_sumbool_is_true".
intros. unfold proj_sumbool. destruct (f x x). auto. elim n; auto.
Qed.

Ltac bool_eq_refl_case :=
match goal with
| [ |- true = true ] => reflexivity
| [ |- proj_sumbool _ = true ] => apply proj_sumbool_is_true
| [ |- _ && _ = true ] => apply andb_true_iff; split; bool_eq_refl_case
| _ => auto
end.

Ltac bool_eq_refl :=
let H := fresh "Hrec" in let x := fresh "x" in
fix H 1; intros x; destruct x; simpl; bool_eq_refl_case.

Lemma false_not_true:
forall (P: Prop), false = true -> P.
Proof. hammer_hook "BoolEqual" "BoolEqual.BE.false_not_true".
intros. discriminate.
Qed.

Lemma proj_sumbool_true:
forall (A: Type) (x y: A) (a: {x=y} + {x<>y}),
proj_sumbool a = true -> x = y.
Proof. hammer_hook "BoolEqual" "BoolEqual.BE.proj_sumbool_true".
intros. destruct a. auto. discriminate.
Qed.

Ltac bool_eq_sound_case :=
match goal with
| [ H: false = true |- _ ] => exact (false_not_true _ H)
| [ H: _ && _ = true |- _ ] => apply andb_prop in H; destruct H; bool_eq_sound_case
| [ H: proj_sumbool ?a = true |- _ ] => apply proj_sumbool_true in H; bool_eq_sound_case
| [ |- ?C ?x1 ?x2 ?x3 ?x4 = ?C ?y1 ?y2 ?y3 ?y4 ] => apply f_equal4; auto
| [ |- ?C ?x1 ?x2 ?x3 = ?C ?y1 ?y2 ?y3 ] => apply f_equal3; auto
| [ |- ?C ?x1 ?x2 = ?C ?y1 ?y2 ] => apply f_equal2; auto
| [ |- ?C ?x1 = ?C ?y1 ] => apply f_equal; auto
| [ |- ?x = ?x ] => reflexivity
| _ => idtac
end.

Ltac bool_eq_sound :=
let Hrec := fresh "Hrec" in let x := fresh "x" in let y := fresh "y" in
fix Hrec 1; intros x y; destruct x, y; simpl; intro; bool_eq_sound_case.

Lemma dec_eq_from_bool_eq:
forall (A: Type) (f: A -> A -> bool)
(f_refl: forall x, f x x = true) (f_sound: forall x y, f x y = true -> x = y),
forall (x y: A), {x=y} + {x<>y}.
Proof. hammer_hook "BoolEqual" "BoolEqual.BE.dec_eq_from_bool_eq".
intros. destruct (f x y) eqn:E.
left. apply f_sound. auto.
right; red; intros. subst y. rewrite f_refl in E. discriminate.
Defined.

End BE.


Ltac boolean_equality := BE.bool_eq.



Ltac decidable_equality_from beq :=
apply (BE.dec_eq_from_bool_eq _ beq); [abstract BE.bool_eq_refl|abstract BE.bool_eq_sound].
