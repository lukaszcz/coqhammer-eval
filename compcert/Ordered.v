From Hammer Require Import Hammer.


















Require Import FSets.
From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Integers.



Module OrderedPositive <: OrderedType.

Definition t := positive.
Definition eq (x y: t) := x = y.
Definition lt := Plt.

Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Ordered" "Ordered.OrderedPositive.eq_refl". exact ((@eq_refl t)). Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Ordered" "Ordered.OrderedPositive.eq_sym". exact ((@eq_sym t)). Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedPositive.eq_trans". exact ((@eq_trans t)). Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedPositive.lt_trans". exact (Plt_trans). Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedPositive.lt_not_eq". exact (Plt_ne). Qed.
Lemma compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedPositive.compare".
intros. destruct (Pos.compare x y) as [] eqn:E.
apply EQ. red. apply Pos.compare_eq_iff. assumption.
apply LT. assumption.
apply GT. apply Pos.compare_gt_iff. assumption.
Defined.

Definition eq_dec : forall x y, { eq x y } + { ~ eq x y } := peq.

End OrderedPositive.



Module OrderedZ <: OrderedType.

Definition t := Z.
Definition eq (x y: t) := x = y.
Definition lt := Z.lt.

Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Ordered" "Ordered.OrderedZ.eq_refl". exact ((@eq_refl t)). Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Ordered" "Ordered.OrderedZ.eq_sym". exact ((@eq_sym t)). Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedZ.eq_trans". exact ((@eq_trans t)). Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedZ.lt_trans". exact (Z.lt_trans). Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedZ.lt_not_eq". unfold lt, eq, t; intros. omega. Qed.
Lemma compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedZ.compare".
intros. destruct (Z.compare x y) as [] eqn:E.
apply EQ. red. apply Z.compare_eq_iff. assumption.
apply LT. assumption.
apply GT. apply Z.compare_gt_iff. assumption.
Defined.

Definition eq_dec : forall x y, { eq x y } + { ~ eq x y } := zeq.

End OrderedZ.



Module OrderedInt <: OrderedType.

Definition t := int.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := Int.unsigned x < Int.unsigned y.

Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Ordered" "Ordered.OrderedInt.eq_refl". exact ((@eq_refl t)). Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Ordered" "Ordered.OrderedInt.eq_sym". exact ((@eq_sym t)). Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedInt.eq_trans". exact ((@eq_trans t)). Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedInt.lt_trans".
unfold lt; intros. omega.
Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedInt.lt_not_eq".
unfold lt,eq; intros; red; intros. subst. omega.
Qed.
Lemma compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedInt.compare".
intros. destruct (zlt (Int.unsigned x) (Int.unsigned y)).
apply LT. auto.
destruct (Int.eq_dec x y).
apply EQ. auto.
apply GT.
assert (Int.unsigned x <> Int.unsigned y).
red; intros. rewrite <- (Int.repr_unsigned x) in n. rewrite <- (Int.repr_unsigned y) in n. congruence.
red. omega.
Defined.

Definition eq_dec : forall x y, { eq x y } + { ~ eq x y } := Int.eq_dec.

End OrderedInt.



Module OrderedIndexed(A: INDEXED_TYPE) <: OrderedType.

Definition t := A.t.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := Plt (A.index x) (A.index y).

Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Ordered" "Ordered.OrderedIndexed.eq_refl". exact ((@eq_refl t)). Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Ordered" "Ordered.OrderedIndexed.eq_sym". exact ((@eq_sym t)). Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedIndexed.eq_trans". exact ((@eq_trans t)). Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedIndexed.lt_trans".
unfold lt; intros. eapply Plt_trans; eauto.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedIndexed.lt_not_eq".
unfold lt; unfold eq; intros.
red; intro. subst y. apply Plt_strict with (A.index x). auto.
Qed.

Lemma compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedIndexed.compare".
intros. case (OrderedPositive.compare (A.index x) (A.index y)); intro.
apply LT. exact l.
apply EQ. red; red in e. apply A.index_inj; auto.
apply GT. exact l.
Defined.

Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Proof. hammer_hook "Ordered" "Ordered.OrderedPositive.eq_dec".
intros. case (peq (A.index x) (A.index y)); intros.
left. apply A.index_inj; auto.
right; red; unfold eq; intros; subst. congruence.
Defined.

End OrderedIndexed.



Module OrderedPair (A B: OrderedType) <: OrderedType.

Definition t := (A.t * B.t)%type.

Definition eq (x y: t) :=
A.eq (fst x) (fst y) /\ B.eq (snd x) (snd y).

Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Ordered" "Ordered.OrderedPair.eq_refl".
intros; split; auto.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Ordered" "Ordered.OrderedPair.eq_sym".
unfold eq; intros. intuition auto.
Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedPair.eq_trans".
unfold eq; intros. intuition eauto.
Qed.

Definition lt (x y: t) :=
A.lt (fst x) (fst y) \/
(A.eq (fst x) (fst y) /\ B.lt (snd x) (snd y)).

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Ordered" "Ordered.OrderedPair.lt_trans".
unfold lt; intros.
elim H; elim H0; intros.

left. apply A.lt_trans with (fst y); auto.

left.  elim H1; intros.
case (A.compare (fst x) (fst z)); intro.
assumption.
generalize (A.lt_not_eq H2); intro. elim H5.
apply A.eq_trans with (fst z). auto. auto.
generalize (@A.lt_not_eq (fst z) (fst y)); intro.
elim H5. apply A.lt_trans with (fst x); auto.
apply A.eq_sym; auto.

left. elim H2; intros.
case (A.compare (fst x) (fst z)); intro.
assumption.
generalize (A.lt_not_eq H1); intro. elim H5.
apply A.eq_trans with (fst x).
apply A.eq_sym. auto. auto.
generalize (@A.lt_not_eq (fst y) (fst x)); intro.
elim H5. apply A.lt_trans with (fst z); auto.
apply A.eq_sym; auto.

right. elim H1; elim H2; intros.
split. apply A.eq_trans with (fst y); auto.
apply B.lt_trans with (snd y); auto.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedPair.lt_not_eq".
unfold lt, eq, not; intros.
elim H0; intros.
elim H; intro.
apply (@A.lt_not_eq _ _ H3 H1).
elim H3; intros.
apply (@B.lt_not_eq _ _ H5 H2).
Qed.

Lemma compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Ordered" "Ordered.OrderedPair.compare".
intros.
case (A.compare (fst x) (fst y)); intro.
apply LT. red. left. auto.
case (B.compare (snd x) (snd y)); intro.
apply LT. red. right. tauto.
apply EQ. red. tauto.
apply GT. red. right. split. apply A.eq_sym. auto. auto.
apply GT. red. left. auto.
Defined.

Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Proof. hammer_hook "Ordered" "Ordered.OrderedZ.eq_dec".
unfold eq; intros.
case (A.eq_dec (fst x) (fst y)); intros.
case (B.eq_dec (snd x) (snd y)); intros.
left; auto.
right; intuition.
right; intuition.
Defined.

End OrderedPair.

