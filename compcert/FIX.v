From Hammer Require Import Hammer.




From compcert Require Import Raux.
From compcert Require Import Defs.
From compcert Require Import Round_pred.
From compcert Require Import Generic_fmt.
From compcert Require Import Ulp.
From compcert Require Import Round_NE.

Section RND_FIX.

Variable beta : radix.

Notation bpow := (bpow beta).

Variable emin : Z.

Inductive FIX_format (x : R) : Prop :=
FIX_spec (f : float beta) :
x = F2R f -> (Fexp f = emin)%Z -> FIX_format x.

Definition FIX_exp (e : Z) := emin.



Global Instance FIX_exp_valid : Valid_exp FIX_exp.
Proof. hammer_hook "FIX" "FIX.FIX_exp_valid".
intros k.
unfold FIX_exp.
split ; intros H.
now apply Zlt_le_weak.
split.
apply Z.le_refl.
now intros _ _.
Qed.

Theorem generic_format_FIX :
forall x, FIX_format x -> generic_format beta FIX_exp x.
Proof. hammer_hook "FIX" "FIX.generic_format_FIX".
intros x [[xm xe] Hx1 Hx2].
rewrite Hx1.
now apply generic_format_canonical.
Qed.

Theorem FIX_format_generic :
forall x, generic_format beta FIX_exp x -> FIX_format x.
Proof. hammer_hook "FIX" "FIX.FIX_format_generic".
intros x H.
rewrite H.
eexists ; repeat split.
Qed.

Theorem FIX_format_satisfies_any :
satisfies_any FIX_format.
Proof. hammer_hook "FIX" "FIX.FIX_format_satisfies_any".
refine (satisfies_any_eq _ _ _ (generic_format_satisfies_any beta FIX_exp)).
intros x.
split.
apply FIX_format_generic.
apply generic_format_FIX.
Qed.

Global Instance FIX_exp_monotone : Monotone_exp FIX_exp.
Proof. hammer_hook "FIX" "FIX.FIX_exp_monotone".
intros ex ey H.
apply Z.le_refl.
Qed.

Theorem ulp_FIX :
forall x, ulp beta FIX_exp x = bpow emin.
Proof. hammer_hook "FIX" "FIX.ulp_FIX".
intros x; unfold ulp.
case Req_bool_spec; intros Zx.
case (negligible_exp_spec FIX_exp).
intros T; specialize (T (emin-1)%Z); contradict T.
unfold FIX_exp; omega.
intros n _; reflexivity.
reflexivity.
Qed.

End RND_FIX.
