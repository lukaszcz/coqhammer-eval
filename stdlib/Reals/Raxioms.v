From Hammer Require Import Hammer.













Require Export ZArith_base.
Require Export Rdefinitions.
Local Open Scope R_scope.










Axiom Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Hint Resolve Rplus_comm: real.


Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Hint Resolve Rplus_assoc: real.


Axiom Rplus_opp_r : forall r:R, r + - r = 0.
Hint Resolve Rplus_opp_r: real.


Axiom Rplus_0_l : forall r:R, 0 + r = r.
Hint Resolve Rplus_0_l: real.






Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Hint Resolve Rmult_comm: real.


Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Hint Resolve Rmult_assoc: real.


Axiom Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
Hint Resolve Rinv_l: real.


Axiom Rmult_1_l : forall r:R, 1 * r = r.
Hint Resolve Rmult_1_l: real.


Axiom R1_neq_R0 : 1 <> 0.
Hint Resolve R1_neq_R0: real.






Axiom
Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Hint Resolve Rmult_plus_distr_l: real.









Axiom total_order_T : forall r1 r2:R, {r1 < r2} + {r1 = r2} + {r1 > r2}.






Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.


Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.


Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.


Axiom
Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

Hint Resolve Rlt_asym Rplus_lt_compat_l Rmult_lt_compat_l: real.






Fixpoint INR (n:nat) : R :=
match n with
| O => 0
| S O => 1
| S n => INR n + 1
end.
Arguments INR n%nat.







Axiom archimed : forall r:R, IZR (up r) > r /\ IZR (up r) - r <= 1.






Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.


Definition bound (E:R -> Prop) :=  exists m : R, is_upper_bound E m.


Definition is_lub (E:R -> Prop) (m:R) :=
is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).


Axiom
completeness :
forall E:R -> Prop,
bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.
