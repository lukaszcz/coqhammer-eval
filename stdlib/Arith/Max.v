From Hammer Require Import Hammer.











Require Import PeanoNat.

Local Open Scope nat_scope.
Implicit Types m n p : nat.

Notation max := Nat.max (only parsing).

Definition max_0_l := Nat.max_0_l.
Definition max_0_r := Nat.max_0_r.
Definition succ_max_distr := Nat.succ_max_distr.
Definition plus_max_distr_l := Nat.add_max_distr_l.
Definition plus_max_distr_r := Nat.add_max_distr_r.
Definition max_case_strong := Nat.max_case_strong.
Definition max_spec := Nat.max_spec.
Definition max_dec := Nat.max_dec.
Definition max_case := Nat.max_case.
Definition max_idempotent := Nat.max_id.
Definition max_assoc := Nat.max_assoc.
Definition max_comm := Nat.max_comm.
Definition max_l := Nat.max_l.
Definition max_r := Nat.max_r.
Definition le_max_l := Nat.le_max_l.
Definition le_max_r := Nat.le_max_r.
Definition max_lub_l := Nat.max_lub_l.
Definition max_lub_r := Nat.max_lub_r.
Definition max_lub := Nat.max_lub.



Notation max_case2 := max_case (only parsing).
Notation max_SS := Nat.succ_max_distr (only parsing).


Hint Resolve
Nat.max_l Nat.max_r Nat.le_max_l Nat.le_max_r : arith.

Hint Resolve
Nat.min_l Nat.min_r Nat.le_min_l Nat.le_min_r : arith.
