From Hammer Require Import Hammer.









Require Import QArith.

Lemma Qopp_lt_compat: forall p q : Q, p < q -> - q < - p.
Proof. hammer_hook "Qround" "Qround.Qopp_lt_compat".  
intros (a1,a2) (b1,b2); unfold Qle, Qlt; simpl.
rewrite !Z.mul_opp_l; omega.
Qed.

Hint Resolve Qopp_lt_compat : qarith.



Local Coercion inject_Z : Z >-> Q.

Definition Qfloor (x:Q) := let (n,d) := x in Z.div n (Zpos d).
Definition Qceiling (x:Q) := (-(Qfloor (-x)))%Z.

Lemma Qfloor_Z : forall z:Z, Qfloor z = z.
Proof. hammer_hook "Qround" "Qround.Qfloor_Z".  
intros z.
simpl.
auto with *.
Qed.

Lemma Qceiling_Z : forall z:Z, Qceiling z = z.
Proof. hammer_hook "Qround" "Qround.Qceiling_Z".  
intros z.
unfold Qceiling.
simpl.
rewrite Zdiv_1_r.
auto with *.
Qed.

Lemma Qfloor_le : forall x, Qfloor x <= x.
Proof. hammer_hook "Qround" "Qround.Qfloor_le".  
intros [n d].
simpl.
unfold Qle.
simpl.
replace (n*1)%Z with n by ring.
rewrite Z.mul_comm.
apply Z_mult_div_ge.
auto with *.
Qed.

Hint Resolve Qfloor_le : qarith.

Lemma Qle_ceiling : forall x, x <= Qceiling x.
Proof. hammer_hook "Qround" "Qround.Qle_ceiling".  
intros x.
apply Qle_trans with (- - x).
rewrite Qopp_involutive.
auto with *.
change (Qceiling x:Q) with (-(Qfloor(-x))).
auto with *.
Qed.

Hint Resolve Qle_ceiling : qarith.

Lemma Qle_floor_ceiling : forall x, Qfloor x <= Qceiling x.
Proof. hammer_hook "Qround" "Qround.Qle_floor_ceiling".  
eauto with qarith.
Qed.

Lemma Qlt_floor : forall x, x < (Qfloor x+1)%Z.
Proof. hammer_hook "Qround" "Qround.Qlt_floor".  
intros [n d].
simpl.
unfold Qlt.
simpl.
replace (n*1)%Z with n by ring.
ring_simplify.
replace (n / ' d * ' d + ' d)%Z with
(('d * (n / 'd) + n mod 'd) + 'd - n mod 'd)%Z by ring.
rewrite <- Z_div_mod_eq; auto with*.
rewrite <- Z.lt_add_lt_sub_r.
destruct (Z_mod_lt n ('d)); auto with *.
Qed.

Hint Resolve Qlt_floor : qarith.

Lemma Qceiling_lt : forall x, (Qceiling x-1)%Z < x.
Proof. hammer_hook "Qround" "Qround.Qceiling_lt".  
intros x.
unfold Qceiling.
replace (- Qfloor (- x) - 1)%Z with (-(Qfloor (-x) + 1))%Z by ring.
change ((- (Qfloor (- x) + 1))%Z:Q) with (-(Qfloor (- x) + 1)%Z).
apply Qlt_le_trans with (- - x); auto with *.
rewrite Qopp_involutive.
auto with *.
Qed.

Hint Resolve Qceiling_lt : qarith.

Lemma Qfloor_resp_le : forall x y, x <= y -> (Qfloor x <= Qfloor y)%Z.
Proof. hammer_hook "Qround" "Qround.Qfloor_resp_le".  
intros [xn xd] [yn yd] Hxy.
unfold Qle in *.
simpl in *.
rewrite <- (Zdiv_mult_cancel_r xn ('xd) ('yd)); auto with *.
rewrite <- (Zdiv_mult_cancel_r yn ('yd) ('xd)); auto with *.
rewrite (Z.mul_comm ('yd) ('xd)).
apply Z_div_le; auto with *.
Qed.

Hint Resolve Qfloor_resp_le : qarith.

Lemma Qceiling_resp_le : forall x y, x <= y -> (Qceiling x <= Qceiling y)%Z.
Proof. hammer_hook "Qround" "Qround.Qceiling_resp_le".  
intros x y Hxy.
unfold Qceiling.
cut (Qfloor (-y) <= Qfloor (-x))%Z; auto with *.
Qed.

Hint Resolve Qceiling_resp_le : qarith.

Add Morphism Qfloor with signature Qeq ==> eq as Qfloor_comp.
Proof.
intros x y H.
apply Z.le_antisymm.
auto with *.
symmetry in H; auto with *.
Qed.

Add Morphism Qceiling with signature Qeq ==> eq as Qceiling_comp.
Proof.
intros x y H.
apply Z.le_antisymm.
auto with *.
symmetry in H; auto with *.
Qed.

Lemma Zdiv_Qdiv (n m: Z): (n / m)%Z = Qfloor (n / m).
Proof. hammer_hook "Qround" "Qround.Zdiv_Qdiv".  
unfold Qfloor. intros. simpl.
destruct m as [ | | p]; simpl.
now rewrite Zdiv_0_r, Z.mul_0_r.
now rewrite Z.mul_1_r.
rewrite <- Z.opp_eq_mul_m1.
rewrite <- (Z.opp_involutive (Zpos p)).
now rewrite Zdiv_opp_opp.
Qed.
