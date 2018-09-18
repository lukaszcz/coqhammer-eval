From Hammer Require Import Hammer.














Require Import BinInt.

Open Scope Z_scope.



Definition Zeven (z:Z) :=
match z with
| Z0 => True
| Zpos (xO _) => True
| Zneg (xO _) => True
| _ => False
end.

Definition Zodd (z:Z) :=
match z with
| Zpos xH => True
| Zneg xH => True
| Zpos (xI _) => True
| Zneg (xI _) => True
| _ => False
end.

Lemma Zeven_equiv z : Zeven z <-> Z.Even z.
Proof. hammer_hook "Zeven" "Zeven.Zeven_equiv".
rewrite <- Z.even_spec.
destruct z as [|p|p]; try destruct p; simpl; intuition.
Qed.

Lemma Zodd_equiv z : Zodd z <-> Z.Odd z.
Proof. hammer_hook "Zeven" "Zeven.Zodd_equiv".
rewrite <- Z.odd_spec.
destruct z as [|p|p]; try destruct p; simpl; intuition.
Qed.

Theorem Zeven_ex_iff n : Zeven n <-> exists m, n = 2*m.
Proof. hammer_hook "Zeven" "Zeven.Zeven_ex_iff".  exact ((Zeven_equiv n)). Qed.

Theorem Zodd_ex_iff n : Zodd n <-> exists m, n = 2*m + 1.
Proof. hammer_hook "Zeven" "Zeven.Zodd_ex_iff".  exact ((Zodd_equiv n)). Qed.



Lemma Zeven_bool_iff n : Z.even n = true <-> Zeven n.
Proof. hammer_hook "Zeven" "Zeven.Zeven_bool_iff".
now rewrite Z.even_spec, Zeven_equiv.
Qed.

Lemma Zodd_bool_iff n : Z.odd n = true <-> Zodd n.
Proof. hammer_hook "Zeven" "Zeven.Zodd_bool_iff".
now rewrite Z.odd_spec, Zodd_equiv.
Qed.

Ltac boolify_even_odd := rewrite <- ?Zeven_bool_iff, <- ?Zodd_bool_iff.

Lemma Zodd_even_bool n : Z.odd n = negb (Z.even n).
Proof. hammer_hook "Zeven" "Zeven.Zodd_even_bool".
symmetry. apply Z.negb_even.
Qed.

Lemma Zeven_odd_bool n : Z.even n = negb (Z.odd n).
Proof. hammer_hook "Zeven" "Zeven.Zeven_odd_bool".
symmetry. apply Z.negb_odd.
Qed.

Definition Zeven_odd_dec n : {Zeven n} + {Zodd n}.
Proof. hammer_hook "Zeven" "Zeven.Zeven_odd_dec".
destruct n as [|p|p]; try destruct p; simpl; (now left) || (now right).
Defined.

Definition Zeven_dec n : {Zeven n} + {~ Zeven n}.
Proof. hammer_hook "Zeven" "Zeven.Zeven_dec".
destruct n as [|p|p]; try destruct p; simpl; (now left) || (now right).
Defined.

Definition Zodd_dec n : {Zodd n} + {~ Zodd n}.
Proof. hammer_hook "Zeven" "Zeven.Zodd_dec".
destruct n as [|p|p]; try destruct p; simpl; (now left) || (now right).
Defined.

Lemma Zeven_not_Zodd n : Zeven n -> ~ Zodd n.
Proof. hammer_hook "Zeven" "Zeven.Zeven_not_Zodd".
boolify_even_odd. rewrite <- Z.negb_odd. destruct Z.odd; intuition.
Qed.

Lemma Zodd_not_Zeven n : Zodd n -> ~ Zeven n.
Proof. hammer_hook "Zeven" "Zeven.Zodd_not_Zeven".
boolify_even_odd. rewrite <- Z.negb_odd. destruct Z.odd; intuition.
Qed.

Lemma Zeven_Sn n : Zodd n -> Zeven (Z.succ n).
Proof. hammer_hook "Zeven" "Zeven.Zeven_Sn".
boolify_even_odd. now rewrite Z.even_succ.
Qed.

Lemma Zodd_Sn n : Zeven n -> Zodd (Z.succ n).
Proof. hammer_hook "Zeven" "Zeven.Zodd_Sn".
boolify_even_odd. now rewrite Z.odd_succ.
Qed.

Lemma Zeven_pred n : Zodd n -> Zeven (Z.pred n).
Proof. hammer_hook "Zeven" "Zeven.Zeven_pred".
boolify_even_odd. now rewrite Z.even_pred.
Qed.

Lemma Zodd_pred n : Zeven n -> Zodd (Z.pred n).
Proof. hammer_hook "Zeven" "Zeven.Zodd_pred".
boolify_even_odd. now rewrite Z.odd_pred.
Qed.

Hint Unfold Zeven Zodd: zarith.

Lemma Zdiv2_odd_eqn n : n = 2*(Z.div2 n) + if Z.odd n then 1 else 0.
Proof. hammer_hook "Zeven" "Zeven.Zdiv2_odd_eqn".  exact ((Z.div2_odd n)). Qed.

Lemma Zeven_div2 n : Zeven n -> n = 2 * Z.div2 n.
Proof. hammer_hook "Zeven" "Zeven.Zeven_div2".
boolify_even_odd. rewrite <- Z.negb_odd, Bool.negb_true_iff.
intros Hn. rewrite (Zdiv2_odd_eqn n) at 1. now rewrite Hn, Z.add_0_r.
Qed.

Lemma Zodd_div2 n : Zodd n -> n = 2 * Z.div2 n + 1.
Proof. hammer_hook "Zeven" "Zeven.Zodd_div2".
boolify_even_odd.
intros Hn. rewrite (Zdiv2_odd_eqn n) at 1. now rewrite Hn.
Qed.





Lemma Zquot2_odd_eqn n : n = 2*(Z.quot2 n) + if Z.odd n then Z.sgn n else 0.
Proof. hammer_hook "Zeven" "Zeven.Zquot2_odd_eqn".
now destruct n as [ |[p|p| ]|[p|p| ]].
Qed.

Lemma Zeven_quot2 n : Zeven n -> n = 2 * Z.quot2 n.
Proof. hammer_hook "Zeven" "Zeven.Zeven_quot2".
intros Hn. apply Zeven_bool_iff in Hn.
rewrite (Zquot2_odd_eqn n) at 1.
now rewrite Zodd_even_bool, Hn, Z.add_0_r.
Qed.

Lemma Zodd_quot2 n : n >= 0 -> Zodd n -> n = 2 * Z.quot2 n + 1.
Proof. hammer_hook "Zeven" "Zeven.Zodd_quot2".
intros Hn Hn'. apply Zodd_bool_iff in Hn'.
rewrite (Zquot2_odd_eqn n) at 1. rewrite Hn'. f_equal.
destruct n; (now destruct Hn) || easy.
Qed.

Lemma Zodd_quot2_neg n : n <= 0 -> Zodd n -> n = 2 * Z.quot2 n - 1.
Proof. hammer_hook "Zeven" "Zeven.Zodd_quot2_neg".
intros Hn Hn'. apply Zodd_bool_iff in Hn'.
rewrite (Zquot2_odd_eqn n) at 1; rewrite Hn'. unfold Z.sub. f_equal.
destruct n; (now destruct Hn) || easy.
Qed.

Lemma Zquot2_opp n : Z.quot2 (-n) = - Z.quot2 n.
Proof. hammer_hook "Zeven" "Zeven.Zquot2_opp".
now destruct n as [ |[p|p| ]|[p|p| ]].
Qed.

Lemma Zquot2_quot n : Z.quot2 n = n ÷ 2.
Proof. hammer_hook "Zeven" "Zeven.Zquot2_quot".
assert (AUX : forall m, 0 < m -> Z.quot2 m = m ÷ 2).
{
intros m Hm.
apply Z.quot_unique with (if Z.odd m then Z.sgn m else 0).
now apply Z.lt_le_incl.
rewrite Z.sgn_pos by trivial.
destruct (Z.odd m); now split.
apply Zquot2_odd_eqn.
}
destruct (Z.lt_trichotomy 0 n) as [POS|[NUL|NEG]].
- now apply AUX.
- now subst.
- apply Z.opp_inj. rewrite <- Z.quot_opp_l, <- Zquot2_opp.
apply AUX. now destruct n. easy.
Qed.



Lemma Z_modulo_2 n : {y | n = 2 * y} + {y | n = 2 * y + 1}.
Proof. hammer_hook "Zeven" "Zeven.Z_modulo_2".
destruct (Zeven_odd_dec n) as [Hn|Hn].
- left. exists (Z.div2 n). exact (Zeven_div2 n Hn).
- right. exists (Z.div2 n). exact (Zodd_div2 n Hn).
Qed.

Lemma Zsplit2 n :
{p : Z * Z | let (x1, x2) := p in n = x1 + x2 /\ (x1 = x2 \/ x2 = x1 + 1)}.
Proof. hammer_hook "Zeven" "Zeven.Zsplit2".
destruct (Z_modulo_2 n) as [(y,Hy)|(y,Hy)];
rewrite <- Z.add_diag in Hy.
- exists (y, y). split. assumption. now left.
- exists (y, y + 1). split. now rewrite Z.add_assoc. now right.
Qed.

Theorem Zeven_ex n : Zeven n -> exists m, n = 2 * m.
Proof. hammer_hook "Zeven" "Zeven.Zeven_ex".
exists (Z.div2 n); apply Zeven_div2; auto.
Qed.

Theorem Zodd_ex n : Zodd n -> exists m, n = 2 * m + 1.
Proof. hammer_hook "Zeven" "Zeven.Zodd_ex".
exists (Z.div2 n); apply Zodd_div2; auto.
Qed.

Theorem Zeven_2p p : Zeven (2 * p).
Proof. hammer_hook "Zeven" "Zeven.Zeven_2p".
now destruct p.
Qed.

Theorem Zodd_2p_plus_1 p : Zodd (2 * p + 1).
Proof. hammer_hook "Zeven" "Zeven.Zodd_2p_plus_1".
destruct p as [|p|p]; now try destruct p.
Qed.

Theorem Zeven_plus_Zodd a b : Zeven a -> Zodd b -> Zodd (a + b).
Proof. hammer_hook "Zeven" "Zeven.Zeven_plus_Zodd".
boolify_even_odd. rewrite <- Z.negb_odd, Bool.negb_true_iff.
intros Ha Hb. now rewrite Z.odd_add, Ha, Hb.
Qed.

Theorem Zeven_plus_Zeven a b : Zeven a -> Zeven b -> Zeven (a + b).
Proof. hammer_hook "Zeven" "Zeven.Zeven_plus_Zeven".
boolify_even_odd. intros Ha Hb. now rewrite Z.even_add, Ha, Hb.
Qed.

Theorem Zodd_plus_Zeven a b : Zodd a -> Zeven b -> Zodd (a + b).
Proof. hammer_hook "Zeven" "Zeven.Zodd_plus_Zeven".
intros. rewrite Z.add_comm. now apply Zeven_plus_Zodd.
Qed.

Theorem Zodd_plus_Zodd a b : Zodd a -> Zodd b -> Zeven (a + b).
Proof. hammer_hook "Zeven" "Zeven.Zodd_plus_Zodd".
boolify_even_odd. rewrite <- 2 Z.negb_even, 2 Bool.negb_true_iff.
intros Ha Hb. now rewrite Z.even_add, Ha, Hb.
Qed.

Theorem Zeven_mult_Zeven_l a b : Zeven a -> Zeven (a * b).
Proof. hammer_hook "Zeven" "Zeven.Zeven_mult_Zeven_l".
boolify_even_odd. intros Ha. now rewrite Z.even_mul, Ha.
Qed.

Theorem Zeven_mult_Zeven_r a b : Zeven b -> Zeven (a * b).
Proof. hammer_hook "Zeven" "Zeven.Zeven_mult_Zeven_r".
intros. rewrite Z.mul_comm. now apply Zeven_mult_Zeven_l.
Qed.

Theorem Zodd_mult_Zodd a b : Zodd a -> Zodd b -> Zodd (a * b).
Proof. hammer_hook "Zeven" "Zeven.Zodd_mult_Zodd".
boolify_even_odd. intros Ha Hb. now rewrite Z.odd_mul, Ha, Hb.
Qed.


Close Scope Z_scope.
