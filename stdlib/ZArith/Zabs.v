From Hammer Require Import Hammer.















Require Import Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Znat.
Require Import ZArith_dec.

Local Open Scope Z_scope.




Notation Zabs_eq := Z.abs_eq (compat "8.3").
Notation Zabs_non_eq := Z.abs_neq (compat "8.3").
Notation Zabs_Zopp := Z.abs_opp (compat "8.3").
Notation Zabs_pos := Z.abs_nonneg (compat "8.3").
Notation Zabs_involutive := Z.abs_involutive (compat "8.3").
Notation Zabs_eq_case := Z.abs_eq_cases (compat "8.3").
Notation Zabs_triangle := Z.abs_triangle (compat "8.3").
Notation Zsgn_Zabs := Z.sgn_abs (compat "8.3").
Notation Zabs_Zsgn := Z.abs_sgn (compat "8.3").
Notation Zabs_Zmult := Z.abs_mul (compat "8.3").
Notation Zabs_square := Z.abs_square (compat "8.3").



Lemma Zabs_ind :
forall (P:Z -> Prop) (n:Z),
(n >= 0 -> P n) -> (n <= 0 -> P (- n)) -> P (Z.abs n).
Proof. hammer_hook "Zabs" "Zabs.Zabs_ind".  
intros. apply Z.abs_case_strong; Z.swap_greater; trivial.
intros x y Hx; now subst.
Qed.

Theorem Zabs_intro : forall P (n:Z), P (- n) -> P n -> P (Z.abs n).
Proof. hammer_hook "Zabs" "Zabs.Zabs_intro".  
now destruct n.
Qed.

Definition Zabs_dec : forall x:Z, {x = Z.abs x} + {x = - Z.abs x}.
Proof. hammer_hook "Zabs" "Zabs.Zabs_dec".  
destruct x; auto.
Defined.

Lemma Zabs_spec x :
0 <= x /\ Z.abs x = x \/
0 > x /\ Z.abs x = -x.
Proof. hammer_hook "Zabs" "Zabs.Zabs_spec".  
Z.swap_greater. apply Z.abs_spec.
Qed.



Notation Zsgn_Zmult := Z.sgn_mul (compat "8.3").
Notation Zsgn_Zopp := Z.sgn_opp (compat "8.3").
Notation Zsgn_pos := Z.sgn_pos_iff (compat "8.3").
Notation Zsgn_neg := Z.sgn_neg_iff (compat "8.3").
Notation Zsgn_null := Z.sgn_null_iff (compat "8.3").



Lemma Zsgn_spec x :
0 < x /\ Z.sgn x = 1 \/
0 = x /\ Z.sgn x = 0 \/
0 > x /\ Z.sgn x = -1.
Proof. hammer_hook "Zabs" "Zabs.Zsgn_spec".  
intros. Z.swap_greater. apply Z.sgn_spec.
Qed.



Notation inj_Zabs_nat := Zabs2Nat.id_abs (compat "8.3").
Notation Zabs_nat_Z_of_nat := Zabs2Nat.id (compat "8.3").
Notation Zabs_nat_mult := Zabs2Nat.inj_mul (compat "8.3").
Notation Zabs_nat_Zsucc := Zabs2Nat.inj_succ (compat "8.3").
Notation Zabs_nat_Zplus := Zabs2Nat.inj_add (compat "8.3").
Notation Zabs_nat_Zminus := (fun n m => Zabs2Nat.inj_sub m n) (compat "8.3").
Notation Zabs_nat_compare := Zabs2Nat.inj_compare (compat "8.3").

Lemma Zabs_nat_le n m : 0 <= n <= m -> (Z.abs_nat n <= Z.abs_nat m)%nat.
Proof. hammer_hook "Zabs" "Zabs.Zabs_nat_le".  
intros (H,H'). apply Zabs2Nat.inj_le; trivial. now transitivity n.
Qed.

Lemma Zabs_nat_lt n m : 0 <= n < m -> (Z.abs_nat n < Z.abs_nat m)%nat.
Proof. hammer_hook "Zabs" "Zabs.Zabs_nat_lt".  
intros (H,H'). apply Zabs2Nat.inj_lt; trivial.
transitivity n; trivial. now apply Z.lt_le_incl.
Qed.
