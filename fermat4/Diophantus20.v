From Hammer Require Import Hammer.

From Fermat4 Require Export Descent.
From Fermat4 Require Export Pythagorean.





Lemma multiple4_2: forall u v : Z,
Zodd v -> Zodd u -> v <= u -> rel_prime u v -> 1 < u -> 1 < v ->
exists two : Z * Z,
let (s, w) := two in
(u - v = 4 * s /\ u + v = 2 * w \/
u - v = 2 * w /\ u + v = 4 * s) /\ 0 < s /\ 0 < w /\ rel_prime s w.
Proof. hammer_hook "Diophantus20" "Diophantus20.multiple4_2".
intros; elim (Zodd_mult u v H0 H); intros; elim H5; clear H5; intros;
elim_hyps; split with (x,x0); intuition; cut (u <> 1); auto with zarith;
intro; cut (u <> -1); auto with zarith; intro.
apply (Zmult_lt_0_reg_r 4 x); auto with zarith; rewrite Zmult_comm;
rewrite <- H5; generalize (relp_neq _ _ H7 H8 H2); auto with zarith.
apply (gcd2_rel_prime (u - v) (u + v) x x0); auto; apply gcd2_relp_odd; auto.
apply (Zmult_lt_0_reg_r 2 x0); auto with zarith; rewrite Zmult_comm;
rewrite <- H5; generalize (relp_neq _ _ H7 H8 H2); auto with zarith.
apply (gcd2_rel_prime (u + v) (u - v) x x0); auto; apply Zis_gcd_sym;
apply gcd2_relp_odd; auto.
Qed.

Lemma for_exists_ab : forall u v m n : Z,
v <= u -> u * u = m * m + n * n -> v * v = n * n - m * m -> 1 < u -> 1 < v ->
Zodd v -> Zodd u -> rel_prime u v ->
exists two : Z * Z,
let (a, b) := two in
(u - v = 4 * (a * a) /\ u + v = 2 * (b * b) \/
u - v = 2 * (b * b) /\ u + v = 4 * (a * a)) /\ 0 < a /\ 0 < b.
Proof. hammer_hook "Diophantus20" "Diophantus20.for_exists_ab".
intros u v m n Huv H H0 H1 H2 H3 H4 H5;
elim (multiple4_2 u v H3 H4 Huv H5 H1 H2); intro; elim x; intros;
elim_hyps; (cut (is_sqr (a * b));
[ intro Hab; elim (prop4 a b (Zlt_le_weak 0 a H7) (Zlt_le_weak 0 b H8) H9
Hab); intros; elim H11; intros Ha H11'; elim H11'; clear H11';
intros a0 H11'; elim H11'; clear H11'; intros H11' Ha0; elim H12;
intros Hb H12'; elim H12'; clear H12'; intros b0 H12'; elim H12';
clear H12'; intros H12' Hb0; split with (a0,b0); intuition;
[ rewrite <- H11' in H7; generalize (sqr_poss a0 H7); intro;
auto with zarith
| rewrite <- H12' in H8; generalize (sqr_poss b0 H8); intro;
auto with zarith ]
| apply (is_sqr_compat 2); try discriminate;
replace (2 * 2 * (a * b)) with (m * m);
[ apply is_sqr_sqr
| apply (Zmult_eq_reg_l 2); try discriminate;
replace (2 * (m * m)) with ((u * u) - (v * v));
[ replace (u * u - v * v) with ((u - v) * (u + v));
[ rewrite H6; rewrite H10; ring | ring ]
| replace (2 * (m * m)) with ((m * m + n * n) - (n * n - m * m));
[ rewrite H; rewrite H0; ring | ring ] ] ] ]).
Qed.





Lemma for_mba_pytha1: forall m n u v a b : Z,
u * u = m * m + n * n -> v * v = n * n - m * m -> u - v = 4 * (a * a) ->
u + v = 2 * (b * b) -> b * b * (b * b) + 2 * (a * a) * (2 * (a * a)) = n * n.
Proof. hammer_hook "Diophantus20" "Diophantus20.for_mba_pytha1".
intros; cut (2 * n * n = u * u + v * v).
intro; cut (u = 2 * a * a + b * b).
intro; cut (v = b * b - 2 * a * a).
intro; rewrite H4 in H3; rewrite H5 in H3; symmetry;
apply (Zmult_eq_reg_l 2).
replace (2 * (n * n)) with (2 * n * n); [ rewrite H3; ring | ring ].
discriminate.
apply (Zmult_eq_reg_l 2).
replace (2 * v) with (u + v - (u - v));
[ rewrite H2; rewrite H1; ring | ring ].
discriminate.
apply (Zmult_eq_reg_l 2).
replace (2 * u) with (u + v + (u - v));
[ rewrite H2; rewrite H1; ring | ring ].
discriminate.
replace (2 * n * n) with (m * m + n * n + (n * n - m * m));
[ rewrite H; rewrite H0; ring | ring ].
Qed.

Lemma for_mba_pytha2: forall m n u v a b : Z,
u * u = m * m + n * n -> v * v = n * n - m * m -> u - v = 2 * (b * b) ->
u + v = 4 * (a * a) -> b * b * (b * b) + 2 * (a * a) * (2 * (a * a)) = n * n.
Proof. hammer_hook "Diophantus20" "Diophantus20.for_mba_pytha2".
intros; cut (2 * n * n = u * u + v * v).
intro; cut (u = 2 * a * a + b * b).
intro; cut (v = 2 * a * a - b * b).
intro; rewrite H4 in H3; rewrite H5 in H3; symmetry;
apply (Zmult_eq_reg_l 2).
replace (2 * (n * n)) with (2 * n * n); [ rewrite H3; ring | ring ].
discriminate.
apply (Zmult_eq_reg_l 2).
replace (2 * v) with (u + v - (u - v));
[ rewrite H2; rewrite H1; ring | ring ].
discriminate.
apply (Zmult_eq_reg_l 2).
replace (2 * u) with (u + v + (u - v));
[ rewrite H2; rewrite H1; ring | ring ].
discriminate.
replace (2 * n * n) with (m * m + n * n + (n * n - m * m));
[ rewrite H; rewrite H0; ring | ring ].
Qed.
