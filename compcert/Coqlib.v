From Hammer Require Import Hammer.


















Require Export String.
Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.

Global Set Asymmetric Patterns.



Ltac inv H := inversion H; clear H; subst.

Ltac predSpec pred predspec x y :=
generalize (predspec x y); case (pred x y); intro.

Ltac caseEq name :=
generalize (eq_refl name); pattern name at -1 in |- *; case name.

Ltac destructEq name :=
destruct name eqn:?.

Ltac decEq :=
match goal with
| [ |- _ = _ ] => f_equal
| [ |- (?X ?A <> ?X ?B) ] =>
cut (A <> B); [intro; congruence | try discriminate]
end.

Ltac byContradiction :=
cut False; [contradiction|idtac].

Ltac omegaContradiction :=
cut False; [contradiction|omega].

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. hammer_hook "Coqlib" "Coqlib.modusponens". auto. Qed.

Ltac exploit x :=
refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _ _) _)
|| refine (modusponens _ _ (x _ _ _) _)
|| refine (modusponens _ _ (x _ _) _)
|| refine (modusponens _ _ (x _) _).



Definition peq: forall (x y: positive), {x = y} + {x <> y} := Pos.eq_dec.
Global Opaque peq.

Lemma peq_true:
forall (A: Type) (x: positive) (a b: A), (if peq x x then a else b) = a.
Proof. hammer_hook "Coqlib" "Coqlib.peq_true".
intros. case (peq x x); intros.
auto.
elim n; auto.
Qed.

Lemma peq_false:
forall (A: Type) (x y: positive) (a b: A), x <> y -> (if peq x y then a else b) = b.
Proof. hammer_hook "Coqlib" "Coqlib.peq_false".
intros. case (peq x y); intros.
elim H; auto.
auto.
Qed.

Definition Plt: positive -> positive -> Prop := Pos.lt.

Lemma Plt_ne:
forall (x y: positive), Plt x y -> x <> y.
Proof. hammer_hook "Coqlib" "Coqlib.Plt_ne".
unfold Plt; intros. red; intro. subst y. eelim Pos.lt_irrefl; eauto.
Qed.
Hint Resolve Plt_ne: coqlib.

Lemma Plt_trans:
forall (x y z: positive), Plt x y -> Plt y z -> Plt x z.
Proof. hammer_hook "Coqlib" "Coqlib.Plt_trans". exact ((Pos.lt_trans)). Qed.

Lemma Plt_succ:
forall (x: positive), Plt x (Pos.succ x).
Proof. hammer_hook "Coqlib" "Coqlib.Plt_succ".
unfold Plt; intros. apply Pos.lt_succ_r. apply Pos.le_refl.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_trans_succ:
forall (x y: positive), Plt x y -> Plt x (Pos.succ y).
Proof. hammer_hook "Coqlib" "Coqlib.Plt_trans_succ".
intros. apply Plt_trans with y. assumption. apply Plt_succ.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_succ_inv:
forall (x y: positive), Plt x (Pos.succ y) -> Plt x y \/ x = y.
Proof. hammer_hook "Coqlib" "Coqlib.Plt_succ_inv".
unfold Plt; intros. rewrite Pos.lt_succ_r in H.
apply Pos.le_lteq; auto.
Qed.

Definition plt (x y: positive) : {Plt x y} + {~ Plt x y}.
Proof. hammer_hook "Coqlib" "Coqlib.plt".
unfold Plt, Pos.lt; intros. destruct (Pos.compare x y).
- right; congruence.
- left; auto.
- right; congruence.
Defined.
Global Opaque plt.

Definition Ple: positive -> positive -> Prop := Pos.le.

Lemma Ple_refl: forall (p: positive), Ple p p.
Proof. hammer_hook "Coqlib" "Coqlib.Ple_refl". exact ((Pos.le_refl)). Qed.

Lemma Ple_trans: forall (p q r: positive), Ple p q -> Ple q r -> Ple p r.
Proof. hammer_hook "Coqlib" "Coqlib.Ple_trans". exact ((Pos.le_trans)). Qed.

Lemma Plt_Ple: forall (p q: positive), Plt p q -> Ple p q.
Proof. hammer_hook "Coqlib" "Coqlib.Plt_Ple". exact ((Pos.lt_le_incl)). Qed.

Lemma Ple_succ: forall (p: positive), Ple p (Pos.succ p).
Proof. hammer_hook "Coqlib" "Coqlib.Ple_succ".
intros. apply Plt_Ple. apply Plt_succ.
Qed.

Lemma Plt_Ple_trans:
forall (p q r: positive), Plt p q -> Ple q r -> Plt p r.
Proof. hammer_hook "Coqlib" "Coqlib.Plt_Ple_trans". exact ((Pos.lt_le_trans)). Qed.

Lemma Plt_strict: forall p, ~ Plt p p.
Proof. hammer_hook "Coqlib" "Coqlib.Plt_strict". exact ((Pos.lt_irrefl)). Qed.

Hint Resolve Ple_refl Plt_Ple Ple_succ Plt_strict: coqlib.

Ltac xomega := unfold Plt, Ple in *; zify; omega.
Ltac xomegaContradiction := exfalso; xomega.



Section POSITIVE_ITERATION.

Lemma Plt_wf: well_founded Plt.
Proof. hammer_hook "Coqlib" "Coqlib.Plt_wf".
apply well_founded_lt_compat with Pos.to_nat.
intros. apply nat_of_P_lt_Lt_compare_morphism. exact H.
Qed.

Variable A: Type.
Variable v1: A.
Variable f: positive -> A -> A.

Lemma Ppred_Plt:
forall x, x <> xH -> Plt (Pos.pred x) x.
Proof. hammer_hook "Coqlib" "Coqlib.Ppred_Plt".
intros. elim (Pos.succ_pred_or x); intro. contradiction.
set (y := Pos.pred x) in *. rewrite <- H0. apply Plt_succ.
Qed.

Let iter (x: positive) (P: forall y, Plt y x -> A) : A :=
match peq x xH with
| left EQ => v1
| right NOTEQ => f (Pos.pred x) (P (Pos.pred x) (Ppred_Plt x NOTEQ))
end.

Definition positive_rec : positive -> A :=
Fix Plt_wf (fun _ => A) iter.

Lemma unroll_positive_rec:
forall x,
positive_rec x = iter x (fun y _ => positive_rec y).
Proof. hammer_hook "Coqlib" "Coqlib.unroll_positive_rec".
unfold positive_rec. apply (Fix_eq Plt_wf (fun _ => A) iter).
intros. unfold iter. case (peq x 1); intro. auto. decEq. apply H.
Qed.

Lemma positive_rec_base:
positive_rec 1%positive = v1.
Proof. hammer_hook "Coqlib" "Coqlib.positive_rec_base".
rewrite unroll_positive_rec. unfold iter. case (peq 1 1); intro.
auto. elim n; auto.
Qed.

Lemma positive_rec_succ:
forall x, positive_rec (Pos.succ x) = f x (positive_rec x).
Proof. hammer_hook "Coqlib" "Coqlib.positive_rec_succ".
intro. rewrite unroll_positive_rec. unfold iter.
case (peq (Pos.succ x) 1); intro.
destruct x; simpl in e; discriminate.
rewrite Pos.pred_succ. auto.
Qed.

Lemma positive_Peano_ind:
forall (P: positive -> Prop),
P xH ->
(forall x, P x -> P (Pos.succ x)) ->
forall x, P x.
Proof. hammer_hook "Coqlib" "Coqlib.positive_Peano_ind".
intros.
apply (well_founded_ind Plt_wf P).
intros.
case (peq x0 xH); intro.
subst x0; auto.
elim (Pos.succ_pred_or x0); intro. contradiction. rewrite <- H2.
apply H0. apply H1. apply Ppred_Plt. auto.
Qed.

End POSITIVE_ITERATION.



Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z.eq_dec.

Lemma zeq_true:
forall (A: Type) (x: Z) (a b: A), (if zeq x x then a else b) = a.
Proof. hammer_hook "Coqlib" "Coqlib.zeq_true".
intros. case (zeq x x); intros.
auto.
elim n; auto.
Qed.

Lemma zeq_false:
forall (A: Type) (x y: Z) (a b: A), x <> y -> (if zeq x y then a else b) = b.
Proof. hammer_hook "Coqlib" "Coqlib.zeq_false".
intros. case (zeq x y); intros.
elim H; auto.
auto.
Qed.

Open Scope Z_scope.

Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_dec.

Lemma zlt_true:
forall (A: Type) (x y: Z) (a b: A),
x < y -> (if zlt x y then a else b) = a.
Proof. hammer_hook "Coqlib" "Coqlib.zlt_true".
intros. case (zlt x y); intros.
auto.
omegaContradiction.
Qed.

Lemma zlt_false:
forall (A: Type) (x y: Z) (a b: A),
x >= y -> (if zlt x y then a else b) = b.
Proof. hammer_hook "Coqlib" "Coqlib.zlt_false".
intros. case (zlt x y); intros.
omegaContradiction.
auto.
Qed.

Definition zle: forall (x y: Z), {x <= y} + {x > y} := Z_le_gt_dec.

Lemma zle_true:
forall (A: Type) (x y: Z) (a b: A),
x <= y -> (if zle x y then a else b) = a.
Proof. hammer_hook "Coqlib" "Coqlib.zle_true".
intros. case (zle x y); intros.
auto.
omegaContradiction.
Qed.

Lemma zle_false:
forall (A: Type) (x y: Z) (a b: A),
x > y -> (if zle x y then a else b) = b.
Proof. hammer_hook "Coqlib" "Coqlib.zle_false".
intros. case (zle x y); intros.
omegaContradiction.
auto.
Qed.



Lemma two_power_nat_O : two_power_nat O = 1.
Proof. hammer_hook "Coqlib" "Coqlib.two_power_nat_O". reflexivity. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof. hammer_hook "Coqlib" "Coqlib.two_power_nat_pos".
induction n. rewrite two_power_nat_O. omega.
rewrite two_power_nat_S. omega.
Qed.

Lemma two_power_nat_two_p:
forall x, two_power_nat x = two_p (Z.of_nat x).
Proof. hammer_hook "Coqlib" "Coqlib.two_power_nat_two_p".
induction x. auto.
rewrite two_power_nat_S. rewrite Nat2Z.inj_succ. rewrite two_p_S. omega. omega.
Qed.

Lemma two_p_monotone:
forall x y, 0 <= x <= y -> two_p x <= two_p y.
Proof. hammer_hook "Coqlib" "Coqlib.two_p_monotone".
intros.
replace (two_p x) with (two_p x * 1) by omega.
replace y with (x + (y - x)) by omega.
rewrite two_p_is_exp; try omega.
apply Zmult_le_compat_l.
assert (two_p (y - x) > 0). apply two_p_gt_ZERO. omega. omega.
assert (two_p x > 0). apply two_p_gt_ZERO. omega. omega.
Qed.

Lemma two_p_monotone_strict:
forall x y, 0 <= x < y -> two_p x < two_p y.
Proof. hammer_hook "Coqlib" "Coqlib.two_p_monotone_strict".
intros. assert (two_p x <= two_p (y - 1)). apply two_p_monotone; omega.
assert (two_p (y - 1) > 0). apply two_p_gt_ZERO. omega.
replace y with (Z.succ (y - 1)) by omega. rewrite two_p_S. omega. omega.
Qed.

Lemma two_p_strict:
forall x, x >= 0 -> x < two_p x.
Proof. hammer_hook "Coqlib" "Coqlib.two_p_strict".
intros x0 GT. pattern x0. apply natlike_ind.
simpl. omega.
intros. rewrite two_p_S; auto. generalize (two_p_gt_ZERO x H). omega.
omega.
Qed.

Lemma two_p_strict_2:
forall x, x >= 0 -> 2 * x - 1 < two_p x.
Proof. hammer_hook "Coqlib" "Coqlib.two_p_strict_2".
intros. assert (x = 0 \/ x - 1 >= 0) by omega. destruct H0.
subst. vm_compute. auto.
replace (two_p x) with (2 * two_p (x - 1)).
generalize (two_p_strict _ H0). omega.
rewrite <- two_p_S. decEq. omega. omega.
Qed.



Lemma Zmin_spec:
forall x y, Z.min x y = if zlt x y then x else y.
Proof. hammer_hook "Coqlib" "Coqlib.Zmin_spec".
intros. case (zlt x y); unfold Z.lt, Z.ge; intro z.
unfold Z.min. rewrite z. auto.
unfold Z.min. caseEq (x ?= y); intro.
apply Z.compare_eq. auto.
contradiction.
reflexivity.
Qed.

Lemma Zmax_spec:
forall x y, Z.max x y = if zlt y x then x else y.
Proof. hammer_hook "Coqlib" "Coqlib.Zmax_spec".
intros. case (zlt y x); unfold Z.lt, Z.ge; intro z.
unfold Z.max. rewrite <- (Zcompare_antisym y x).
rewrite z. simpl. auto.
unfold Z.max. rewrite <- (Zcompare_antisym y x).
caseEq (y ?= x); intro; simpl.
symmetry. apply Z.compare_eq. auto.
contradiction. reflexivity.
Qed.

Lemma Zmax_bound_l:
forall x y z, x <= y -> x <= Z.max y z.
Proof. hammer_hook "Coqlib" "Coqlib.Zmax_bound_l".
intros. generalize (Z.le_max_l y z). omega.
Qed.
Lemma Zmax_bound_r:
forall x y z, x <= z -> x <= Z.max y z.
Proof. hammer_hook "Coqlib" "Coqlib.Zmax_bound_r".
intros. generalize (Z.le_max_r y z). omega.
Qed.



Lemma Zmod_unique:
forall x y a b,
x = a * y + b -> 0 <= b < y -> x mod y = b.
Proof. hammer_hook "Coqlib" "Coqlib.Zmod_unique".
intros. subst x. rewrite Z.add_comm.
rewrite Z_mod_plus. apply Z.mod_small. auto. omega.
Qed.

Lemma Zdiv_unique:
forall x y a b,
x = a * y + b -> 0 <= b < y -> x / y = a.
Proof. hammer_hook "Coqlib" "Coqlib.Zdiv_unique".
intros. subst x. rewrite Z.add_comm.
rewrite Z_div_plus. rewrite (Zdiv_small b y H0). omega. omega.
Qed.

Lemma Zdiv_Zdiv:
forall a b c,
b > 0 -> c > 0 -> (a / b) / c = a / (b * c).
Proof. hammer_hook "Coqlib" "Coqlib.Zdiv_Zdiv".
intros. apply Z.div_div; omega.
Qed.

Lemma Zdiv_interval_1:
forall lo hi a b,
lo <= 0 -> hi > 0 -> b > 0 ->
lo * b <= a < hi * b ->
lo <= a/b < hi.
Proof. hammer_hook "Coqlib" "Coqlib.Zdiv_interval_1".
intros.
generalize (Z_div_mod_eq a b H1). generalize (Z_mod_lt a b H1). intros.
set (q := a/b) in *. set (r := a mod b) in *.
split.
assert (lo < (q + 1)).
apply Zmult_lt_reg_r with b. omega.
apply Z.le_lt_trans with a. omega.
replace ((q + 1) * b) with (b * q + b) by ring.
omega.
omega.
apply Zmult_lt_reg_r with b. omega.
replace (q * b) with (b * q) by ring.
omega.
Qed.

Lemma Zdiv_interval_2:
forall lo hi a b,
lo <= a <= hi -> lo <= 0 -> hi >= 0 -> b > 0 ->
lo <= a/b <= hi.
Proof. hammer_hook "Coqlib" "Coqlib.Zdiv_interval_2".
intros.
assert (lo <= a / b < hi+1).
apply Zdiv_interval_1. omega. omega. auto.
assert (lo * b <= lo * 1) by (apply Z.mul_le_mono_nonpos_l; omega).
replace (lo * 1) with lo in H3 by ring.
assert ((hi + 1) * 1 <= (hi + 1) * b) by (apply Z.mul_le_mono_nonneg_l; omega).
replace ((hi + 1) * 1) with (hi + 1) in H4 by ring.
omega.
omega.
Qed.

Lemma Zmod_recombine:
forall x a b,
a > 0 -> b > 0 ->
x mod (a * b) = ((x/b) mod a) * b + (x mod b).
Proof. hammer_hook "Coqlib" "Coqlib.Zmod_recombine".
intros. rewrite (Z.mul_comm a b). rewrite Z.rem_mul_r by omega. ring.
Qed.



Lemma Zdivide_interval:
forall a b c,
0 < c -> 0 <= a < b -> (c | a) -> (c | b) -> 0 <= a <= b - c.
Proof. hammer_hook "Coqlib" "Coqlib.Zdivide_interval".
intros. destruct H1 as [x EQ1]. destruct H2 as [y EQ2]. subst. destruct H0.
split. omega. exploit Zmult_lt_reg_r; eauto. intros.
replace (y * c - c) with ((y - 1) * c) by ring.
apply Zmult_le_compat_r; omega.
Qed.



Lemma Z_to_nat_neg:
forall n, n <= 0 -> Z.to_nat n = O.
Proof. hammer_hook "Coqlib" "Coqlib.Z_to_nat_neg".
destruct n; unfold Z.le; simpl; auto. congruence.
Qed.

Lemma Z_to_nat_max:
forall z, Z.of_nat (Z.to_nat z) = Z.max z 0.
Proof. hammer_hook "Coqlib" "Coqlib.Z_to_nat_max".
intros. destruct (zle 0 z).
- rewrite Z2Nat.id by auto. xomega.
- rewrite Z_to_nat_neg by omega. xomega.
Qed.



Definition align (n: Z) (amount: Z) :=
((n + amount - 1) / amount) * amount.

Lemma align_le: forall x y, y > 0 -> x <= align x y.
Proof. hammer_hook "Coqlib" "Coqlib.align_le".
intros. unfold align.
generalize (Z_div_mod_eq (x + y - 1) y H). intro.
replace ((x + y - 1) / y * y)
with ((x + y - 1) - (x + y - 1) mod y).
generalize (Z_mod_lt (x + y - 1) y H). omega.
rewrite Z.mul_comm. omega.
Qed.

Lemma align_divides: forall x y, y > 0 -> (y | align x y).
Proof. hammer_hook "Coqlib" "Coqlib.align_divides".
intros. unfold align. apply Z.divide_factor_r.
Qed.



Set Implicit Arguments.



Definition option_eq (A: Type) (eqA: forall (x y: A), {x=y} + {x<>y}):
forall (x y: option A), {x=y} + {x<>y}.
Proof. hammer_hook "Coqlib" "Coqlib.option_eq". decide equality. Defined.
Global Opaque option_eq.



Inductive option_rel (A B: Type) (R: A -> B -> Prop) : option A -> option B -> Prop :=
| option_rel_none: option_rel R None None
| option_rel_some: forall x y, R x y -> option_rel R (Some x) (Some y).



Definition option_map (A B: Type) (f: A -> B) (x: option A) : option B :=
match x with
| None => None
| Some y => Some (f y)
end.



Definition sum_left_map (A B C: Type) (f: A -> B) (x: A + C) : B + C :=
match x with
| inl y => inl C (f y)
| inr z => inr B z
end.



Hint Resolve in_eq in_cons: coqlib.

Lemma nth_error_in:
forall (A: Type) (n: nat) (l: list A) (x: A),
List.nth_error l n = Some x -> In x l.
Proof. hammer_hook "Coqlib" "Coqlib.nth_error_in".
induction n; simpl.
destruct l; intros.
discriminate.
injection H; intro; subst a. apply in_eq.
destruct l; intros.
discriminate.
apply in_cons. auto.
Qed.
Hint Resolve nth_error_in: coqlib.

Lemma nth_error_nil:
forall (A: Type) (idx: nat), nth_error (@nil A) idx = None.
Proof. hammer_hook "Coqlib" "Coqlib.nth_error_nil".
induction idx; simpl; intros; reflexivity.
Qed.
Hint Resolve nth_error_nil: coqlib.



Fixpoint list_length_z_aux (A: Type) (l: list A) (acc: Z) {struct l}: Z :=
match l with
| nil => acc
| hd :: tl => list_length_z_aux tl (Z.succ acc)
end.

Remark list_length_z_aux_shift:
forall (A: Type) (l: list A) n m,
list_length_z_aux l n = list_length_z_aux l m + (n - m).
Proof. hammer_hook "Coqlib" "Coqlib.list_length_z_aux_shift".
induction l; intros; simpl.
omega.
replace (n - m) with (Z.succ n - Z.succ m) by omega. auto.
Qed.

Definition list_length_z (A: Type) (l: list A) : Z :=
list_length_z_aux l 0.

Lemma list_length_z_cons:
forall (A: Type) (hd: A) (tl: list A),
list_length_z (hd :: tl) = list_length_z tl + 1.
Proof. hammer_hook "Coqlib" "Coqlib.list_length_z_cons".
intros. unfold list_length_z. simpl.
rewrite (list_length_z_aux_shift tl 1 0). omega.
Qed.

Lemma list_length_z_pos:
forall (A: Type) (l: list A),
list_length_z l >= 0.
Proof. hammer_hook "Coqlib" "Coqlib.list_length_z_pos".
induction l; simpl. unfold list_length_z; simpl. omega.
rewrite list_length_z_cons. omega.
Qed.

Lemma list_length_z_map:
forall (A B: Type) (f: A -> B) (l: list A),
list_length_z (map f l) = list_length_z l.
Proof. hammer_hook "Coqlib" "Coqlib.list_length_z_map".
induction l. reflexivity. simpl. repeat rewrite list_length_z_cons. congruence.
Qed.



Fixpoint list_nth_z (A: Type) (l: list A) (n: Z) {struct l}: option A :=
match l with
| nil => None
| hd :: tl => if zeq n 0 then Some hd else list_nth_z tl (Z.pred n)
end.

Lemma list_nth_z_in:
forall (A: Type) (l: list A) n x,
list_nth_z l n = Some x -> In x l.
Proof. hammer_hook "Coqlib" "Coqlib.list_nth_z_in".
induction l; simpl; intros.
congruence.
destruct (zeq n 0). left; congruence. right; eauto.
Qed.

Lemma list_nth_z_map:
forall (A B: Type) (f: A -> B) (l: list A) n,
list_nth_z (List.map f l) n = option_map f (list_nth_z l n).
Proof. hammer_hook "Coqlib" "Coqlib.list_nth_z_map".
induction l; simpl; intros.
auto.
destruct (zeq n 0). auto. eauto.
Qed.

Lemma list_nth_z_range:
forall (A: Type) (l: list A) n x,
list_nth_z l n = Some x -> 0 <= n < list_length_z l.
Proof. hammer_hook "Coqlib" "Coqlib.list_nth_z_range".
induction l; simpl; intros.
discriminate.
rewrite list_length_z_cons. destruct (zeq n 0).
generalize (list_length_z_pos l); omega.
exploit IHl; eauto. omega.
Qed.



Lemma incl_cons_inv:
forall (A: Type) (a: A) (b c: list A),
incl (a :: b) c -> incl b c.
Proof. hammer_hook "Coqlib" "Coqlib.incl_cons_inv".
unfold incl; intros. apply H. apply in_cons. auto.
Qed.
Hint Resolve incl_cons_inv: coqlib.

Lemma incl_app_inv_l:
forall (A: Type) (l1 l2 m: list A),
incl (l1 ++ l2) m -> incl l1 m.
Proof. hammer_hook "Coqlib" "Coqlib.incl_app_inv_l".
unfold incl; intros. apply H. apply in_or_app. left; assumption.
Qed.

Lemma incl_app_inv_r:
forall (A: Type) (l1 l2 m: list A),
incl (l1 ++ l2) m -> incl l2 m.
Proof. hammer_hook "Coqlib" "Coqlib.incl_app_inv_r".
unfold incl; intros. apply H. apply in_or_app. right; assumption.
Qed.

Hint Resolve  incl_tl incl_refl incl_app_inv_l incl_app_inv_r: coqlib.

Lemma incl_same_head:
forall (A: Type) (x: A) (l1 l2: list A),
incl l1 l2 -> incl (x::l1) (x::l2).
Proof. hammer_hook "Coqlib" "Coqlib.incl_same_head".
intros; red; simpl; intros. intuition.
Qed.



Lemma list_map_exten:
forall (A B: Type) (f f': A -> B) (l: list A),
(forall x, In x l -> f x = f' x) ->
List.map f' l = List.map f l.
Proof. hammer_hook "Coqlib" "Coqlib.list_map_exten".
induction l; simpl; intros.
reflexivity.
rewrite <- H. rewrite IHl. reflexivity.
intros. apply H. tauto.
tauto.
Qed.

Lemma list_map_compose:
forall (A B C: Type) (f: A -> B) (g: B -> C) (l: list A),
List.map g (List.map f l) = List.map (fun x => g(f x)) l.
Proof. hammer_hook "Coqlib" "Coqlib.list_map_compose".
induction l; simpl. reflexivity. rewrite IHl; reflexivity.
Qed.

Lemma list_map_identity:
forall (A: Type) (l: list A),
List.map (fun (x:A) => x) l = l.
Proof. hammer_hook "Coqlib" "Coqlib.list_map_identity".
induction l; simpl; congruence.
Qed.

Lemma list_map_nth:
forall (A B: Type) (f: A -> B) (l: list A) (n: nat),
nth_error (List.map f l) n = option_map f (nth_error l n).
Proof. hammer_hook "Coqlib" "Coqlib.list_map_nth".
induction l; simpl; intros.
repeat rewrite nth_error_nil. reflexivity.
destruct n; simpl. reflexivity. auto.
Qed.

Lemma list_length_map:
forall (A B: Type) (f: A -> B) (l: list A),
List.length (List.map f l) = List.length l.
Proof. hammer_hook "Coqlib" "Coqlib.list_length_map".
induction l; simpl; congruence.
Qed.

Lemma list_in_map_inv:
forall (A B: Type) (f: A -> B) (l: list A) (y: B),
In y (List.map f l) -> exists x:A, y = f x /\ In x l.
Proof. hammer_hook "Coqlib" "Coqlib.list_in_map_inv".
induction l; simpl; intros.
contradiction.
elim H; intro.
exists a; intuition auto.
generalize (IHl y H0). intros [x [EQ IN]].
exists x; tauto.
Qed.

Lemma list_append_map:
forall (A B: Type) (f: A -> B) (l1 l2: list A),
List.map f (l1 ++ l2) = List.map f l1 ++ List.map f l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_append_map".
induction l1; simpl; intros.
auto. rewrite IHl1. auto.
Qed.

Lemma list_append_map_inv:
forall (A B: Type) (f: A -> B) (m1 m2: list B) (l: list A),
List.map f l = m1 ++ m2 ->
exists l1, exists l2, List.map f l1 = m1 /\ List.map f l2 = m2 /\ l = l1 ++ l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_append_map_inv".
induction m1; simpl; intros.
exists (@nil A); exists l; auto.
destruct l; simpl in H; inv H.
exploit IHm1; eauto. intros [l1 [l2 [P [Q R]]]]. subst l.
exists (a0 :: l1); exists l2; intuition. simpl; congruence.
Qed.



Section LIST_FOLD.

Variables A B: Type.
Variable f: A -> B -> B.



Fixpoint list_fold_left (accu: B) (l: list A) : B :=
match l with nil => accu | x :: l' => list_fold_left (f x accu) l' end.



Definition list_fold_right (l: list A) (base: B) : B :=
list_fold_left base (List.rev' l).

Remark list_fold_left_app:
forall l1 l2 accu,
list_fold_left accu (l1 ++ l2) = list_fold_left (list_fold_left accu l1) l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_fold_left_app".
induction l1; simpl; intros.
auto.
rewrite IHl1. auto.
Qed.

Lemma list_fold_right_eq:
forall l base,
list_fold_right l base =
match l with nil => base | x :: l' => f x (list_fold_right l' base) end.
Proof. hammer_hook "Coqlib" "Coqlib.list_fold_right_eq".
unfold list_fold_right; intros.
destruct l.
auto.
unfold rev'. rewrite <- ! rev_alt. simpl.
rewrite list_fold_left_app. simpl. auto.
Qed.

Lemma list_fold_right_spec:
forall l base, list_fold_right l base = List.fold_right f base l.
Proof. hammer_hook "Coqlib" "Coqlib.list_fold_right_spec".
induction l; simpl; intros; rewrite list_fold_right_eq; congruence.
Qed.

End LIST_FOLD.



Lemma in_cns:
forall (A: Type) (x y: A) (l: list A), In x (y :: l) <-> y = x \/ In x l.
Proof. hammer_hook "Coqlib" "Coqlib.in_cns".
intros. simpl. tauto.
Qed.

Lemma in_app:
forall (A: Type) (x: A) (l1 l2: list A), In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof. hammer_hook "Coqlib" "Coqlib.in_app".
intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
Qed.

Lemma list_in_insert:
forall (A: Type) (x: A) (l1 l2: list A) (y: A),
In x (l1 ++ l2) -> In x (l1 ++ y :: l2).
Proof. hammer_hook "Coqlib" "Coqlib.list_in_insert".
intros. apply in_or_app; simpl. elim (in_app_or _ _ _ H); intro; auto.
Qed.



Definition list_disjoint (A: Type) (l1 l2: list A) : Prop :=
forall (x y: A), In x l1 -> In y l2 -> x <> y.

Lemma list_disjoint_cons_l:
forall (A: Type) (a: A) (l1 l2: list A),
list_disjoint l1 l2 -> ~In a l2 -> list_disjoint (a :: l1) l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_disjoint_cons_l".
unfold list_disjoint; simpl; intros. destruct H1. congruence. apply H; auto.
Qed.

Lemma list_disjoint_cons_r:
forall (A: Type) (a: A) (l1 l2: list A),
list_disjoint l1 l2 -> ~In a l1 -> list_disjoint l1 (a :: l2).
Proof. hammer_hook "Coqlib" "Coqlib.list_disjoint_cons_r".
unfold list_disjoint; simpl; intros. destruct H2. congruence. apply H; auto.
Qed.

Lemma list_disjoint_cons_left:
forall (A: Type) (a: A) (l1 l2: list A),
list_disjoint (a :: l1) l2 -> list_disjoint l1 l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_disjoint_cons_left".
unfold list_disjoint; simpl; intros. apply H; tauto.
Qed.

Lemma list_disjoint_cons_right:
forall (A: Type) (a: A) (l1 l2: list A),
list_disjoint l1 (a :: l2) -> list_disjoint l1 l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_disjoint_cons_right".
unfold list_disjoint; simpl; intros. apply H; tauto.
Qed.

Lemma list_disjoint_notin:
forall (A: Type) (l1 l2: list A) (a: A),
list_disjoint l1 l2 -> In a l1 -> ~(In a l2).
Proof. hammer_hook "Coqlib" "Coqlib.list_disjoint_notin".
unfold list_disjoint; intros; red; intros.
apply H with a a; auto.
Qed.

Lemma list_disjoint_sym:
forall (A: Type) (l1 l2: list A),
list_disjoint l1 l2 -> list_disjoint l2 l1.
Proof. hammer_hook "Coqlib" "Coqlib.list_disjoint_sym".
unfold list_disjoint; intros.
apply not_eq_sym. apply H; auto.
Qed.

Lemma list_disjoint_dec:
forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l1 l2: list A),
{list_disjoint l1 l2} + {~list_disjoint l1 l2}.
Proof. hammer_hook "Coqlib" "Coqlib.list_disjoint_dec".
induction l1; intros.
left; red; intros. elim H.
case (In_dec eqA_dec a l2); intro.
right; red; intro. apply (H a a); auto with coqlib.
case (IHl1 l2); intro.
left; red; intros. elim H; intro.
red; intro; subst a y. contradiction.
apply l; auto.
right; red; intros. elim n0. eapply list_disjoint_cons_left; eauto.
Defined.



Definition list_equiv (A : Type) (l1 l2: list A) : Prop :=
forall x, In x l1 <-> In x l2.



Inductive list_norepet (A: Type) : list A -> Prop :=
| list_norepet_nil:
list_norepet nil
| list_norepet_cons:
forall hd tl,
~(In hd tl) -> list_norepet tl -> list_norepet (hd :: tl).

Lemma list_norepet_dec:
forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l: list A),
{list_norepet l} + {~list_norepet l}.
Proof. hammer_hook "Coqlib" "Coqlib.list_norepet_dec".
induction l.
left; constructor.
destruct IHl.
case (In_dec eqA_dec a l); intro.
right. red; intro. inversion H. contradiction.
left. constructor; auto.
right. red; intro. inversion H. contradiction.
Defined.

Lemma list_map_norepet:
forall (A B: Type) (f: A -> B) (l: list A),
list_norepet l ->
(forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
list_norepet (List.map f l).
Proof. hammer_hook "Coqlib" "Coqlib.list_map_norepet".
induction 1; simpl; intros.
constructor.
constructor.
red; intro. generalize (list_in_map_inv f _ _ H2).
intros [x [EQ IN]]. generalize EQ. change (f hd <> f x).
apply H1. tauto. tauto.
red; intro; subst x. contradiction.
apply IHlist_norepet. intros. apply H1. tauto. tauto. auto.
Qed.

Remark list_norepet_append_commut:
forall (A: Type) (a b: list A),
list_norepet (a ++ b) -> list_norepet (b ++ a).
Proof. hammer_hook "Coqlib" "Coqlib.list_norepet_append_commut".
intro A.
assert (forall (x: A) (b: list A) (a: list A),
list_norepet (a ++ b) -> ~(In x a) -> ~(In x b) ->
list_norepet (a ++ x :: b)).
induction a; simpl; intros.
constructor; auto.
inversion H. constructor. red; intro.
elim (in_app_or _ _ _ H6); intro.
elim H4. apply in_or_app. tauto.
elim H7; intro. subst a. elim H0. left. auto.
elim H4. apply in_or_app. tauto.
auto.
induction a; simpl; intros.
rewrite <- app_nil_end. auto.
inversion H0. apply H. auto.
red; intro; elim H3. apply in_or_app. tauto.
red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma list_norepet_app:
forall (A: Type) (l1 l2: list A),
list_norepet (l1 ++ l2) <->
list_norepet l1 /\ list_norepet l2 /\ list_disjoint l1 l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_norepet_app".
induction l1; simpl; intros; split; intros.
intuition. constructor. red;simpl;auto.
tauto.
inversion H; subst. rewrite IHl1 in H3. rewrite in_app in H2.
intuition.
constructor; auto. red; intros. elim H2; intro. congruence. auto.
destruct H as [B [C D]]. inversion B; subst.
constructor. rewrite in_app. intuition. elim (D a a); auto. apply in_eq.
rewrite IHl1. intuition. red; intros. apply D; auto. apply in_cons; auto.
Qed.

Lemma list_norepet_append:
forall (A: Type) (l1 l2: list A),
list_norepet l1 -> list_norepet l2 -> list_disjoint l1 l2 ->
list_norepet (l1 ++ l2).
Proof. hammer_hook "Coqlib" "Coqlib.list_norepet_append".
generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_right:
forall (A: Type) (l1 l2: list A),
list_norepet (l1 ++ l2) -> list_norepet l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_norepet_append_right".
generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_left:
forall (A: Type) (l1 l2: list A),
list_norepet (l1 ++ l2) -> list_norepet l1.
Proof. hammer_hook "Coqlib" "Coqlib.list_norepet_append_left".
generalize list_norepet_app; firstorder.
Qed.



Inductive is_tail (A: Type): list A -> list A -> Prop :=
| is_tail_refl:
forall c, is_tail c c
| is_tail_cons:
forall i c1 c2, is_tail c1 c2 -> is_tail c1 (i :: c2).

Lemma is_tail_in:
forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> In i c2.
Proof. hammer_hook "Coqlib" "Coqlib.is_tail_in".
induction c2; simpl; intros.
inversion H.
inversion H. tauto. right; auto.
Qed.

Lemma is_tail_cons_left:
forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> is_tail c1 c2.
Proof. hammer_hook "Coqlib" "Coqlib.is_tail_cons_left".
induction c2; intros; inversion H.
constructor. constructor. constructor. auto.
Qed.

Hint Resolve is_tail_refl is_tail_cons is_tail_in is_tail_cons_left: coqlib.

Lemma is_tail_incl:
forall (A: Type) (l1 l2: list A), is_tail l1 l2 -> incl l1 l2.
Proof. hammer_hook "Coqlib" "Coqlib.is_tail_incl".
induction 1; eauto with coqlib.
Qed.

Lemma is_tail_trans:
forall (A: Type) (l1 l2: list A),
is_tail l1 l2 -> forall (l3: list A), is_tail l2 l3 -> is_tail l1 l3.
Proof. hammer_hook "Coqlib" "Coqlib.is_tail_trans".
induction 1; intros. auto. apply IHis_tail. eapply is_tail_cons_left; eauto.
Qed.



Section FORALL2.

Variable A: Type.
Variable B: Type.
Variable P: A -> B -> Prop.

Inductive list_forall2: list A -> list B -> Prop :=
| list_forall2_nil:
list_forall2 nil nil
| list_forall2_cons:
forall a1 al b1 bl,
P a1 b1 ->
list_forall2 al bl ->
list_forall2 (a1 :: al) (b1 :: bl).

Lemma list_forall2_app:
forall a2 b2 a1 b1,
list_forall2 a1 b1 -> list_forall2 a2 b2 ->
list_forall2 (a1 ++ a2) (b1 ++ b2).
Proof. hammer_hook "Coqlib" "Coqlib.list_forall2_app".
induction 1; intros; simpl. auto. constructor; auto.
Qed.

Lemma list_forall2_length:
forall l1 l2,
list_forall2 l1 l2 -> length l1 = length l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_forall2_length".
induction 1; simpl; congruence.
Qed.

Lemma list_forall2_in_left:
forall x1 l1 l2,
list_forall2 l1 l2 -> In x1 l1 -> exists x2, In x2 l2 /\ P x1 x2.
Proof. hammer_hook "Coqlib" "Coqlib.list_forall2_in_left".
induction 1; simpl; intros. contradiction. destruct H1.
subst; exists b1; auto.
exploit IHlist_forall2; eauto. intros (x2 & U & V); exists x2; auto.
Qed.

Lemma list_forall2_in_right:
forall x2 l1 l2,
list_forall2 l1 l2 -> In x2 l2 -> exists x1, In x1 l1 /\ P x1 x2.
Proof. hammer_hook "Coqlib" "Coqlib.list_forall2_in_right".
induction 1; simpl; intros. contradiction. destruct H1.
subst; exists a1; auto.
exploit IHlist_forall2; eauto. intros (x1 & U & V); exists x1; auto.
Qed.

End FORALL2.

Lemma list_forall2_imply:
forall (A B: Type) (P1: A -> B -> Prop) (l1: list A) (l2: list B),
list_forall2 P1 l1 l2 ->
forall (P2: A -> B -> Prop),
(forall v1 v2, In v1 l1 -> In v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
list_forall2 P2 l1 l2.
Proof. hammer_hook "Coqlib" "Coqlib.list_forall2_imply".
induction 1; intros.
constructor.
constructor. auto with coqlib. apply IHlist_forall2; auto.
intros. auto with coqlib.
Qed.



Fixpoint list_drop (A: Type) (n: nat) (x: list A) {struct n} : list A :=
match n with
| O => x
| S n' => match x with nil => nil | hd :: tl => list_drop n' tl end
end.

Lemma list_drop_incl:
forall (A: Type) (x: A) n (l: list A), In x (list_drop n l) -> In x l.
Proof. hammer_hook "Coqlib" "Coqlib.list_drop_incl".
induction n; simpl; intros. auto.
destruct l; auto with coqlib.
Qed.

Lemma list_drop_norepet:
forall (A: Type) n (l: list A), list_norepet l -> list_norepet (list_drop n l).
Proof. hammer_hook "Coqlib" "Coqlib.list_drop_norepet".
induction n; simpl; intros. auto.
inv H. constructor. auto.
Qed.

Lemma list_map_drop:
forall (A B: Type) (f: A -> B) n (l: list A),
list_drop n (map f l) = map f (list_drop n l).
Proof. hammer_hook "Coqlib" "Coqlib.list_map_drop".
induction n; simpl; intros. auto.
destruct l; simpl; auto.
Qed.



Fixpoint list_repeat {A: Type} (n: nat) (x: A) {struct n} :=
match n with
| O => nil
| S m => x :: list_repeat m x
end.

Lemma length_list_repeat:
forall (A: Type) n (x: A), length (list_repeat n x) = n.
Proof. hammer_hook "Coqlib" "Coqlib.length_list_repeat".
induction n; simpl; intros. auto. decEq; auto.
Qed.

Lemma in_list_repeat:
forall (A: Type) n (x: A) y, In y (list_repeat n x) -> y = x.
Proof. hammer_hook "Coqlib" "Coqlib.in_list_repeat".
induction n; simpl; intros. elim H. destruct H; auto.
Qed.



Definition proj_sumbool {P Q: Prop} (a: {P} + {Q}) : bool :=
if a then true else false.

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_true:
forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = true -> P.
Proof. hammer_hook "Coqlib" "Coqlib.proj_sumbool_true".
intros P Q a. destruct a; simpl. auto. congruence.
Qed.

Lemma proj_sumbool_is_true:
forall (P: Prop) (a: {P}+{~P}), P -> proj_sumbool a = true.
Proof. hammer_hook "Coqlib" "Coqlib.proj_sumbool_is_true".
intros. unfold proj_sumbool. destruct a. auto. contradiction.
Qed.

Ltac InvBooleans :=
match goal with
| [ H: _ && _ = true |- _ ] =>
destruct (andb_prop _ _ H); clear H; InvBooleans
| [ H: _ || _ = false |- _ ] =>
destruct (orb_false_elim _ _ H); clear H; InvBooleans
| [ H: proj_sumbool ?x = true |- _ ] =>
generalize (proj_sumbool_true _ H); clear H; intro; InvBooleans
| _ => idtac
end.

Section DECIDABLE_EQUALITY.

Variable A: Type.
Variable dec_eq: forall (x y: A), {x=y} + {x<>y}.
Variable B: Type.

Lemma dec_eq_true:
forall (x: A) (ifso ifnot: B),
(if dec_eq x x then ifso else ifnot) = ifso.
Proof. hammer_hook "Coqlib" "Coqlib.dec_eq_true".
intros. destruct (dec_eq x x). auto. congruence.
Qed.

Lemma dec_eq_false:
forall (x y: A) (ifso ifnot: B),
x <> y -> (if dec_eq x y then ifso else ifnot) = ifnot.
Proof. hammer_hook "Coqlib" "Coqlib.dec_eq_false".
intros. destruct (dec_eq x y). congruence. auto.
Qed.

Lemma dec_eq_sym:
forall (x y: A) (ifso ifnot: B),
(if dec_eq x y then ifso else ifnot) =
(if dec_eq y x then ifso else ifnot).
Proof. hammer_hook "Coqlib" "Coqlib.dec_eq_sym".
intros. destruct (dec_eq x y).
subst y. rewrite dec_eq_true. auto.
rewrite dec_eq_false; auto.
Qed.

End DECIDABLE_EQUALITY.

Section DECIDABLE_PREDICATE.

Variable P: Prop.
Variable dec: {P} + {~P}.
Variable A: Type.

Lemma pred_dec_true:
forall (a b: A), P -> (if dec then a else b) = a.
Proof. hammer_hook "Coqlib" "Coqlib.pred_dec_true".
intros. destruct dec. auto. contradiction.
Qed.

Lemma pred_dec_false:
forall (a b: A), ~P -> (if dec then a else b) = b.
Proof. hammer_hook "Coqlib" "Coqlib.pred_dec_false".
intros. destruct dec. contradiction. auto.
Qed.

End DECIDABLE_PREDICATE.



Require Import Relations.



Section LEX_ORDER.

Variable A: Type.
Variable B: Type.
Variable ordA: A -> A -> Prop.
Variable ordB: B -> B -> Prop.

Inductive lex_ord: A*B -> A*B -> Prop :=
| lex_ord_left: forall a1 b1 a2 b2,
ordA a1 a2 -> lex_ord (a1,b1) (a2,b2)
| lex_ord_right: forall a b1 b2,
ordB b1 b2 -> lex_ord (a,b1) (a,b2).

Lemma wf_lex_ord:
well_founded ordA -> well_founded ordB -> well_founded lex_ord.
Proof. hammer_hook "Coqlib" "Coqlib.wf_lex_ord".
intros Awf Bwf.
assert (forall a, Acc ordA a -> forall b, Acc ordB b -> Acc lex_ord (a, b)).
induction 1. induction 1. constructor; intros. inv H3.
apply H0. auto. apply Bwf.
apply H2; auto.
red; intros. destruct a as [a b]. apply H; auto.
Qed.

Lemma transitive_lex_ord:
transitive _ ordA -> transitive _ ordB -> transitive _ lex_ord.
Proof. hammer_hook "Coqlib" "Coqlib.transitive_lex_ord".
intros trA trB; red; intros.
inv H; inv H0.
left; eapply trA; eauto.
left; auto.
left; auto.
right; eapply trB; eauto.
Qed.

End LEX_ORDER.



Inductive nlist (A: Type) : Type :=
| nbase: A -> nlist A
| ncons: A -> nlist A -> nlist A.

Definition nfirst {A: Type} (l: nlist A) :=
match l with nbase a => a | ncons a l' => a end.

Fixpoint nlast {A: Type} (l: nlist A) :=
match l with nbase a => a | ncons a l' => nlast l' end.

Fixpoint nIn {A: Type} (x: A) (l: nlist A) : Prop :=
match l with
| nbase a => a = x
| ncons a l => a = x \/ nIn x l
end.

Inductive nlist_forall2 {A B: Type} (R: A -> B -> Prop) : nlist A -> nlist B -> Prop :=
| nbase_forall2: forall a b, R a b -> nlist_forall2 R (nbase a) (nbase b)
| ncons_forall2: forall a l b m, R a b -> nlist_forall2 R l m -> nlist_forall2 R (ncons a l) (ncons b m).

Lemma nlist_forall2_imply:
forall (A B: Type) (P1: A -> B -> Prop) (l1: nlist A) (l2: nlist B),
nlist_forall2 P1 l1 l2 ->
forall (P2: A -> B -> Prop),
(forall v1 v2, nIn v1 l1 -> nIn v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
nlist_forall2 P2 l1 l2.
Proof. hammer_hook "Coqlib" "Coqlib.nlist_forall2_imply".
induction 1; simpl; intros; constructor; auto.
Qed.
