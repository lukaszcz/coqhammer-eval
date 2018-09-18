From Hammer Require Import Hammer.









Require Import BinPos BinNat PeanoNat Pnat.



Module N2Nat.



Lemma id a : N.of_nat (N.to_nat a) = a.
Proof. hammer_hook "Nnat" "Nnat.N2Nat.id".  
destruct a as [| p]; simpl; trivial.
destruct (Pos2Nat.is_succ p) as (n,H). rewrite H. simpl. f_equal.
apply Pos2Nat.inj. rewrite H. apply SuccNat2Pos.id_succ.
Qed.



Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj".  
intro H. rewrite <- (id a), <- (id a'). now f_equal.
Qed.

Lemma inj_iff a a' : N.to_nat a = N.to_nat a' <-> a = a'.
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_iff".  
split. apply inj. intros; now subst.
Qed.



Lemma inj_double a : N.to_nat (N.double a) = 2*(N.to_nat a).
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_double".  
destruct a; simpl N.to_nat; trivial. apply Pos2Nat.inj_xO.
Qed.

Lemma inj_succ_double a : N.to_nat (N.succ_double a) = S (2*(N.to_nat a)).
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_succ_double".  
destruct a; simpl N.to_nat; trivial. apply Pos2Nat.inj_xI.
Qed.

Lemma inj_succ a : N.to_nat (N.succ a) = S (N.to_nat a).
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_succ".  
destruct a; simpl; trivial. apply Pos2Nat.inj_succ.
Qed.

Lemma inj_add a a' :
N.to_nat (a + a') = N.to_nat a + N.to_nat a'.
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_add".  
destruct a, a'; simpl; trivial. apply Pos2Nat.inj_add.
Qed.

Lemma inj_mul a a' :
N.to_nat (a * a') = N.to_nat a * N.to_nat a'.
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_mul".  
destruct a, a'; simpl; trivial. apply Pos2Nat.inj_mul.
Qed.

Lemma inj_sub a a' :
N.to_nat (a - a') = N.to_nat a - N.to_nat a'.
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_sub".  
destruct a as [|a], a' as [|a']; simpl; rewrite ?Nat.sub_0_r; trivial.
destruct (Pos.compare_spec a a').
- subst. now rewrite Pos.sub_mask_diag, Nat.sub_diag.
- rewrite Pos.sub_mask_neg; trivial. apply Pos2Nat.inj_lt in H.
simpl; symmetry; apply Nat.sub_0_le. now apply Nat.lt_le_incl.
- destruct (Pos.sub_mask_pos' _ _ H) as (q & -> & Hq).
simpl; symmetry; apply Nat.add_sub_eq_l. now rewrite <- Hq, Pos2Nat.inj_add.
Qed.

Lemma inj_pred a : N.to_nat (N.pred a) = Nat.pred (N.to_nat a).
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_pred".  
rewrite <- Nat.sub_1_r, N.pred_sub. apply inj_sub.
Qed.

Lemma inj_div2 a : N.to_nat (N.div2 a) = Nat.div2 (N.to_nat a).
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_div2".  
destruct a as [|[p|p| ]]; trivial.
- unfold N.div2, N.to_nat. now rewrite Pos2Nat.inj_xI, Nat.div2_succ_double.
- unfold N.div2, N.to_nat. now rewrite Pos2Nat.inj_xO, Nat.div2_double.
Qed.

Lemma inj_compare a a' :
(a ?= a')%N = (N.to_nat a ?= N.to_nat a').
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_compare".  
destruct a, a'; simpl; trivial.
- now destruct (Pos2Nat.is_succ p) as (n,->).
- now destruct (Pos2Nat.is_succ p) as (n,->).
- apply Pos2Nat.inj_compare.
Qed.

Lemma inj_max a a' :
N.to_nat (N.max a a') = Nat.max (N.to_nat a) (N.to_nat a').
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_max".  
unfold N.max. rewrite inj_compare; symmetry.
case Nat.compare_spec; intros.
- now apply Nat.max_r, Nat.eq_le_incl.
- now apply Nat.max_r, Nat.lt_le_incl.
- now apply Nat.max_l, Nat.lt_le_incl.
Qed.

Lemma inj_min a a' :
N.to_nat (N.min a a') = Nat.min (N.to_nat a) (N.to_nat a').
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_min".  
unfold N.min; rewrite inj_compare. symmetry.
case Nat.compare_spec; intros.
- now apply Nat.min_l, Nat.eq_le_incl.
- now apply Nat.min_l, Nat.lt_le_incl.
- now apply Nat.min_r, Nat.lt_le_incl.
Qed.

Lemma inj_iter a {A} (f:A->A) (x:A) :
N.iter a f x = Nat.iter (N.to_nat a) f x.
Proof. hammer_hook "Nnat" "Nnat.N2Nat.inj_iter".  
destruct a as [|a]. trivial. apply Pos2Nat.inj_iter.
Qed.

End N2Nat.

Hint Rewrite N2Nat.inj_double N2Nat.inj_succ_double
N2Nat.inj_succ N2Nat.inj_add N2Nat.inj_mul N2Nat.inj_sub
N2Nat.inj_pred N2Nat.inj_div2 N2Nat.inj_max N2Nat.inj_min
N2Nat.id
: Nnat.




Module Nat2N.



Lemma id n : N.to_nat (N.of_nat n) = n.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.id".  
induction n; simpl; trivial. apply SuccNat2Pos.id_succ.
Qed.

Hint Rewrite id : Nnat.
Ltac nat2N := apply N2Nat.inj; now autorewrite with Nnat.



Lemma inj n n' : N.of_nat n = N.of_nat n' -> n = n'.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj".  
intros H. rewrite <- (id n), <- (id n'). now f_equal.
Qed.

Lemma inj_iff n n' : N.of_nat n = N.of_nat n' <-> n = n'.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_iff".  
split. apply inj. intros; now subst.
Qed.



Lemma inj_double n : N.of_nat (2*n) = N.double (N.of_nat n).
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_double".   nat2N. Qed.

Lemma inj_succ_double n : N.of_nat (S (2*n)) = N.succ_double (N.of_nat n).
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_succ_double".   nat2N. Qed.

Lemma inj_succ n : N.of_nat (S n) = N.succ (N.of_nat n).
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_succ".   nat2N. Qed.

Lemma inj_pred n : N.of_nat (Nat.pred n) = N.pred (N.of_nat n).
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_pred".   nat2N. Qed.

Lemma inj_add n n' : N.of_nat (n+n') = (N.of_nat n + N.of_nat n')%N.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_add".   nat2N. Qed.

Lemma inj_sub n n' : N.of_nat (n-n') = (N.of_nat n - N.of_nat n')%N.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_sub".   nat2N. Qed.

Lemma inj_mul n n' : N.of_nat (n*n') = (N.of_nat n * N.of_nat n')%N.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_mul".   nat2N. Qed.

Lemma inj_div2 n : N.of_nat (Nat.div2 n) = N.div2 (N.of_nat n).
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_div2".   nat2N. Qed.

Lemma inj_compare n n' :
(n ?= n') = (N.of_nat n ?= N.of_nat n')%N.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_compare".   now rewrite N2Nat.inj_compare, !id. Qed.

Lemma inj_min n n' :
N.of_nat (Nat.min n n') = N.min (N.of_nat n) (N.of_nat n').
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_min".   nat2N. Qed.

Lemma inj_max n n' :
N.of_nat (Nat.max n n') = N.max (N.of_nat n) (N.of_nat n').
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_max".   nat2N. Qed.

Lemma inj_iter n {A} (f:A->A) (x:A) :
Nat.iter n f x = N.iter (N.of_nat n) f x.
Proof. hammer_hook "Nnat" "Nnat.Nat2N.inj_iter".   now rewrite N2Nat.inj_iter, !id. Qed.

End Nat2N.

Hint Rewrite Nat2N.id : Nnat.



Notation nat_of_N_inj := N2Nat.inj (compat "8.3").
Notation N_of_nat_of_N := N2Nat.id (compat "8.3").
Notation nat_of_Ndouble := N2Nat.inj_double (compat "8.3").
Notation nat_of_Ndouble_plus_one := N2Nat.inj_succ_double (compat "8.3").
Notation nat_of_Nsucc := N2Nat.inj_succ (compat "8.3").
Notation nat_of_Nplus := N2Nat.inj_add (compat "8.3").
Notation nat_of_Nmult := N2Nat.inj_mul (compat "8.3").
Notation nat_of_Nminus := N2Nat.inj_sub (compat "8.3").
Notation nat_of_Npred := N2Nat.inj_pred (compat "8.3").
Notation nat_of_Ndiv2 := N2Nat.inj_div2 (compat "8.3").
Notation nat_of_Ncompare := N2Nat.inj_compare (compat "8.3").
Notation nat_of_Nmax := N2Nat.inj_max (compat "8.3").
Notation nat_of_Nmin := N2Nat.inj_min (compat "8.3").

Notation nat_of_N_of_nat := Nat2N.id (compat "8.3").
Notation N_of_nat_inj := Nat2N.inj (compat "8.3").
Notation N_of_double := Nat2N.inj_double (compat "8.3").
Notation N_of_double_plus_one := Nat2N.inj_succ_double (compat "8.3").
Notation N_of_S := Nat2N.inj_succ (compat "8.3").
Notation N_of_pred := Nat2N.inj_pred (compat "8.3").
Notation N_of_plus := Nat2N.inj_add (compat "8.3").
Notation N_of_minus := Nat2N.inj_sub (compat "8.3").
Notation N_of_mult := Nat2N.inj_mul (compat "8.3").
Notation N_of_div2 := Nat2N.inj_div2 (compat "8.3").
Notation N_of_nat_compare := Nat2N.inj_compare (compat "8.3").
Notation N_of_min := Nat2N.inj_min (compat "8.3").
Notation N_of_max := Nat2N.inj_max (compat "8.3").
