From Hammer Require Import Hammer.











Require Import BinInt Zcompare Zorder.

Local Open Scope Z_scope.





Notation Zmin_case := Z.min_case (compat "8.3").
Notation Zmin_case_strong := Z.min_case_strong (compat "8.3").
Notation Zle_min_l := Z.le_min_l (compat "8.3").
Notation Zle_min_r := Z.le_min_r (compat "8.3").
Notation Zmin_glb := Z.min_glb (compat "8.3").
Notation Zmin_glb_lt := Z.min_glb_lt (compat "8.3").
Notation Zle_min_compat_r := Z.min_le_compat_r (compat "8.3").
Notation Zle_min_compat_l := Z.min_le_compat_l (compat "8.3").
Notation Zmin_idempotent := Z.min_id (compat "8.3").
Notation Zmin_n_n := Z.min_id (compat "8.3").
Notation Zmin_comm := Z.min_comm (compat "8.3").
Notation Zmin_assoc := Z.min_assoc (compat "8.3").
Notation Zmin_irreducible_inf := Z.min_dec (compat "8.3").
Notation Zsucc_min_distr := Z.succ_min_distr (compat "8.3").
Notation Zmin_SS := Z.succ_min_distr (compat "8.3").
Notation Zplus_min_distr_r := Z.add_min_distr_r (compat "8.3").
Notation Zmin_plus := Z.add_min_distr_r (compat "8.3").
Notation Zpos_min := Pos2Z.inj_min (compat "8.3").



Lemma Zmin_spec x y :
x <= y /\ Z.min x y = x  \/  x > y /\ Z.min x y = y.
Proof. hammer_hook "Zmin" "Zmin.Zmin_spec".  
Z.swap_greater. rewrite Z.min_comm. destruct (Z.min_spec y x); auto.
Qed.

Lemma Zmin_irreducible n m : Z.min n m = n \/ Z.min n m = m.
Proof. hammer_hook "Zmin" "Zmin.Zmin_irreducible".   destruct (Z.min_dec n m); auto. Qed.

Notation Zmin_or := Zmin_irreducible (compat "8.3").

Lemma Zmin_le_prime_inf n m p : Z.min n m <= p -> {n <= p} + {m <= p}.
Proof. hammer_hook "Zmin" "Zmin.Zmin_le_prime_inf".   apply Z.min_case; auto. Qed.

Lemma Zpos_min_1 p : Z.min 1 (Zpos p) = 1.
Proof. hammer_hook "Zmin" "Zmin.Zpos_min_1".  
now destruct p.
Qed.
