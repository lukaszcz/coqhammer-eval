From Hammer Require Import Hammer.









Require Export Compare_dec.
Require Export Peano_dec.
Require Import Sumbool.

Local Open Scope nat_scope.

Implicit Types m n x y : nat.



Definition notzerop n := sumbool_not _ _ (zerop n).
Definition lt_ge_dec : forall x y, {x < y} + {x >= y} :=
fun n m => sumbool_not _ _ (le_lt_dec m n).

Definition nat_lt_ge_bool x y := bool_of_sumbool (lt_ge_dec x y).
Definition nat_ge_lt_bool x y :=
bool_of_sumbool (sumbool_not _ _ (lt_ge_dec x y)).

Definition nat_le_gt_bool x y := bool_of_sumbool (le_gt_dec x y).
Definition nat_gt_le_bool x y :=
bool_of_sumbool (sumbool_not _ _ (le_gt_dec x y)).

Definition nat_eq_bool x y := bool_of_sumbool (eq_nat_dec x y).
Definition nat_noteq_bool x y :=
bool_of_sumbool (sumbool_not _ _ (eq_nat_dec x y)).

Definition zerop_bool x := bool_of_sumbool (zerop x).
Definition notzerop_bool x := bool_of_sumbool (notzerop x).
