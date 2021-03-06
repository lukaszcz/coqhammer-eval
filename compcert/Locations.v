From Hammer Require Import Hammer.















Require Import OrderedType.
From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Ordered.
From compcert Require Import AST.
From compcert Require Import Values.
From compcert Require Export Machregs.













Inductive slot: Type :=
| Local
| Incoming
| Outgoing.



Lemma slot_eq: forall (p q: slot), {p = q} + {p <> q}.
Proof. hammer_hook "Locations" "Locations.slot_eq".
decide equality.
Defined.

Open Scope Z_scope.

Definition typesize (ty: typ) : Z :=
match ty with
| Tint => 1
| Tlong => 2
| Tfloat => 2
| Tsingle => 1
| Tany32 => 1
| Tany64 => 2
end.

Lemma typesize_pos:
forall (ty: typ), typesize ty > 0.
Proof. hammer_hook "Locations" "Locations.typesize_pos".
destruct ty; compute; auto.
Qed.

Definition typealign (ty: typ) : Z :=
match ty with
| Tint => 1
| Tlong => 2
| Tfloat => 1
| Tsingle => 1
| Tany32 => 1
| Tany64 => 1
end.

Lemma typealign_pos:
forall (ty: typ), typealign ty > 0.
Proof. hammer_hook "Locations" "Locations.typealign_pos".
destruct ty; compute; auto.
Qed.

Lemma typealign_typesize:
forall (ty: typ), (typealign ty | typesize ty).
Proof. hammer_hook "Locations" "Locations.typealign_typesize".
intros. exists (typesize ty / typealign ty); destruct ty; reflexivity.
Qed.





Inductive loc : Type :=
| R (r: mreg)
| S (sl: slot) (pos: Z) (ty: typ).

Module Loc.

Definition type (l: loc) : typ :=
match l with
| R r => mreg_type r
| S sl pos ty => ty
end.

Lemma eq: forall (p q: loc), {p = q} + {p <> q}.
Proof. hammer_hook "Locations" "Locations.Loc.eq".
decide equality.
apply mreg_eq.
apply typ_eq.
apply zeq.
apply slot_eq.
Defined.


Definition diff (l1 l2: loc) : Prop :=
match l1, l2 with
| R r1, R r2 =>
r1 <> r2
| S s1 d1 t1, S s2 d2 t2 =>
s1 <> s2 \/ d1 + typesize t1 <= d2 \/ d2 + typesize t2 <= d1
| _, _ =>
True
end.

Lemma same_not_diff:
forall l, ~(diff l l).
Proof. hammer_hook "Locations" "Locations.Loc.same_not_diff".
destruct l; unfold diff; auto.
red; intros. destruct H; auto. generalize (typesize_pos ty); omega.
Qed.

Lemma diff_not_eq:
forall l1 l2, diff l1 l2 -> l1 <> l2.
Proof. hammer_hook "Locations" "Locations.Loc.diff_not_eq".
unfold not; intros. subst l2. elim (same_not_diff l1 H).
Qed.

Lemma diff_sym:
forall l1 l2, diff l1 l2 -> diff l2 l1.
Proof. hammer_hook "Locations" "Locations.Loc.diff_sym".
destruct l1; destruct l2; unfold diff; auto.
intuition.
Qed.

Definition diff_dec (l1 l2: loc) : { Loc.diff l1 l2 } + { ~Loc.diff l1 l2 }.
Proof. hammer_hook "Locations" "Locations.Loc.diff_dec".
intros. destruct l1; destruct l2; simpl.
- destruct (mreg_eq r r0). right; tauto. left; auto.
- left; auto.
- left; auto.
- destruct (slot_eq sl sl0).
destruct (zle (pos + typesize ty) pos0).
left; auto.
destruct (zle (pos0 + typesize ty0) pos).
left; auto.
right; red; intros [P | [P | P]]. congruence. omega. omega.
left; auto.
Defined.



Fixpoint notin (l: loc) (ll: list loc) {struct ll} : Prop :=
match ll with
| nil => True
| l1 :: ls => diff l l1 /\ notin l ls
end.

Lemma notin_iff:
forall l ll, notin l ll <-> (forall l', In l' ll -> Loc.diff l l').
Proof. hammer_hook "Locations" "Locations.Loc.notin_iff".
induction ll; simpl.
tauto.
rewrite IHll. intuition. subst a. auto.
Qed.

Lemma notin_not_in:
forall l ll, notin l ll -> ~(In l ll).
Proof. hammer_hook "Locations" "Locations.Loc.notin_not_in".
intros; red; intros. rewrite notin_iff in H.
elim (diff_not_eq l l); auto.
Qed.

Lemma notin_dec (l: loc) (ll: list loc) : {notin l ll} + {~notin l ll}.
Proof. hammer_hook "Locations" "Locations.Loc.notin_dec".
induction ll; simpl.
left; auto.
destruct (diff_dec l a).
destruct IHll.
left; auto.
right; tauto.
right; tauto.
Defined.



Definition disjoint (l1 l2: list loc) : Prop :=
forall x1 x2, In x1 l1 -> In x2 l2 -> diff x1 x2.

Lemma disjoint_cons_left:
forall a l1 l2,
disjoint (a :: l1) l2 -> disjoint l1 l2.
Proof. hammer_hook "Locations" "Locations.Loc.disjoint_cons_left".
unfold disjoint; intros. auto with coqlib.
Qed.
Lemma disjoint_cons_right:
forall a l1 l2,
disjoint l1 (a :: l2) -> disjoint l1 l2.
Proof. hammer_hook "Locations" "Locations.Loc.disjoint_cons_right".
unfold disjoint; intros. auto with coqlib.
Qed.

Lemma disjoint_sym:
forall l1 l2, disjoint l1 l2 -> disjoint l2 l1.
Proof. hammer_hook "Locations" "Locations.Loc.disjoint_sym".
unfold disjoint; intros. apply diff_sym; auto.
Qed.

Lemma in_notin_diff:
forall l1 l2 ll, notin l1 ll -> In l2 ll -> diff l1 l2.
Proof. hammer_hook "Locations" "Locations.Loc.in_notin_diff".
intros. rewrite notin_iff in H. auto.
Qed.

Lemma notin_disjoint:
forall l1 l2,
(forall x, In x l1 -> notin x l2) -> disjoint l1 l2.
Proof. hammer_hook "Locations" "Locations.Loc.notin_disjoint".
intros; red; intros. exploit H; eauto. rewrite notin_iff; intros. auto.
Qed.

Lemma disjoint_notin:
forall l1 l2 x, disjoint l1 l2 -> In x l1 -> notin x l2.
Proof. hammer_hook "Locations" "Locations.Loc.disjoint_notin".
intros; rewrite notin_iff; intros. red in H. auto.
Qed.



Inductive norepet : list loc -> Prop :=
| norepet_nil:
norepet nil
| norepet_cons:
forall hd tl, notin hd tl -> norepet tl -> norepet (hd :: tl).

Lemma norepet_dec (ll: list loc) : {norepet ll} + {~norepet ll}.
Proof. hammer_hook "Locations" "Locations.Loc.norepet_dec".
induction ll.
left; constructor.
destruct (notin_dec a ll).
destruct IHll.
left; constructor; auto.
right; red; intros P; inv P; contradiction.
right; red; intros P; inv P; contradiction.
Defined.



Definition no_overlap (l1 l2 : list loc) :=
forall r, In r l1 -> forall s, In s l2 ->  r = s \/ Loc.diff r s.

End Loc.





Set Implicit Arguments.

Module Locmap.

Definition t := loc -> val.

Definition init (x: val) : t := fun (_: loc) => x.

Definition get (l: loc) (m: t) : val := m l.



Definition set (l: loc) (v: val) (m: t) : t :=
fun (p: loc) =>
if Loc.eq l p then
match l with R r => v | S sl ofs ty => Val.load_result (chunk_of_type ty) v end
else if Loc.diff_dec l p then
m p
else Vundef.

Lemma gss: forall l v m,
(set l v m) l =
match l with R r => v | S sl ofs ty => Val.load_result (chunk_of_type ty) v end.
Proof. hammer_hook "Locations" "Locations.Locmap.gss".
intros. unfold set. apply dec_eq_true.
Qed.

Lemma gss_reg: forall r v m, (set (R r) v m) (R r) = v.
Proof. hammer_hook "Locations" "Locations.Locmap.gss_reg".
intros. unfold set. rewrite dec_eq_true. auto.
Qed.

Lemma gss_typed: forall l v m, Val.has_type v (Loc.type l) -> (set l v m) l = v.
Proof. hammer_hook "Locations" "Locations.Locmap.gss_typed".
intros. rewrite gss. destruct l. auto. apply Val.load_result_same; auto.
Qed.

Lemma gso: forall l v m p, Loc.diff l p -> (set l v m) p = m p.
Proof. hammer_hook "Locations" "Locations.Locmap.gso".
intros. unfold set. destruct (Loc.eq l p).
subst p. elim (Loc.same_not_diff _ H).
destruct (Loc.diff_dec l p).
auto.
contradiction.
Qed.

Fixpoint undef (ll: list loc) (m: t) {struct ll} : t :=
match ll with
| nil => m
| l1 :: ll' => undef ll' (set l1 Vundef m)
end.

Lemma guo: forall ll l m, Loc.notin l ll -> (undef ll m) l = m l.
Proof. hammer_hook "Locations" "Locations.Locmap.guo".
induction ll; simpl; intros. auto.
destruct H. rewrite IHll; auto. apply gso. apply Loc.diff_sym; auto.
Qed.

Lemma gus: forall ll l m, In l ll -> (undef ll m) l = Vundef.
Proof. hammer_hook "Locations" "Locations.Locmap.gus".
assert (P: forall ll l m, m l = Vundef -> (undef ll m) l = Vundef).
induction ll; simpl; intros. auto. apply IHll.
unfold set. destruct (Loc.eq a l).
destruct a. auto. destruct ty; reflexivity.
destruct (Loc.diff_dec a l); auto.
induction ll; simpl; intros. contradiction.
destruct H. apply P. subst a. apply gss_typed. exact I.
auto.
Qed.

Definition getpair (p: rpair loc) (m: t) : val :=
match p with
| One l => m l
| Twolong l1 l2 => Val.longofwords (m l1) (m l2)
end.

Definition setpair (p: rpair mreg) (v: val) (m: t) : t :=
match p with
| One r => set (R r) v m
| Twolong hi lo => set (R lo) (Val.loword  v) (set (R hi) (Val.hiword v) m)
end.

Lemma getpair_exten:
forall p ls1 ls2,
(forall l, In l (regs_of_rpair p) -> ls2 l = ls1 l) ->
getpair p ls2 = getpair p ls1.
Proof. hammer_hook "Locations" "Locations.Locmap.getpair_exten".
intros. destruct p; simpl.
apply H; simpl; auto.
f_equal; apply H; simpl; auto.
Qed.

Lemma gpo:
forall p v m l,
forall_rpair (fun r => Loc.diff l (R r)) p -> setpair p v m l = m l.
Proof. hammer_hook "Locations" "Locations.Locmap.gpo".
intros; destruct p; simpl in *.
- apply gso. apply Loc.diff_sym; auto.
- destruct H. rewrite ! gso by (apply Loc.diff_sym; auto). auto.
Qed.

Fixpoint setres (res: builtin_res mreg) (v: val) (m: t) : t :=
match res with
| BR r => set (R r) v m
| BR_none => m
| BR_splitlong hi lo =>
setres lo (Val.loword v) (setres hi (Val.hiword v) m)
end.

End Locmap.



Module IndexedTyp <: INDEXED_TYPE.
Definition t := typ.
Definition index (x: t) :=
match x with
| Tany32 => 1%positive
| Tint => 2%positive
| Tsingle => 3%positive
| Tany64 => 4%positive
| Tfloat => 5%positive
| Tlong => 6%positive
end.
Lemma index_inj: forall x y, index x = index y -> x = y.
Proof. hammer_hook "Locations" "Locations.IndexedTyp.index_inj". destruct x; destruct y; simpl; congruence. Qed.
Definition eq := typ_eq.
End IndexedTyp.

Module OrderedTyp := OrderedIndexed(IndexedTyp).

Module IndexedSlot <: INDEXED_TYPE.
Definition t := slot.
Definition index (x: t) :=
match x with Local => 1%positive | Incoming => 2%positive | Outgoing => 3%positive end.
Lemma index_inj: forall x y, index x = index y -> x = y.
Proof. hammer_hook "Locations" "Locations.IndexedSlot.index_inj". destruct x; destruct y; simpl; congruence. Qed.
Definition eq := slot_eq.
End IndexedSlot.

Module OrderedSlot := OrderedIndexed(IndexedSlot).

Module OrderedLoc <: OrderedType.
Definition t := loc.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) :=
match x, y with
| R r1, R r2 => Plt (IndexedMreg.index r1) (IndexedMreg.index r2)
| R _, S _ _ _ => True
| S _ _ _, R _ => False
| S sl1 ofs1 ty1, S sl2 ofs2 ty2 =>
OrderedSlot.lt sl1 sl2 \/ (sl1 = sl2 /\
(ofs1 < ofs2 \/ (ofs1 = ofs2 /\ OrderedTyp.lt ty1 ty2)))
end.
Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.eq_refl". exact ((@eq_refl t)). Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.eq_sym". exact ((@eq_sym t)). Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.eq_trans". exact ((@eq_trans t)). Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.lt_trans".
unfold lt; intros.
destruct x; destruct y; destruct z; try tauto.
eapply Plt_trans; eauto.
destruct H.
destruct H0. left; eapply OrderedSlot.lt_trans; eauto.
destruct H0. subst sl0. auto.
destruct H. subst sl.
destruct H0. auto.
destruct H.
right.  split. auto.
intuition.
right; split. congruence. eapply OrderedTyp.lt_trans; eauto.
Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.lt_not_eq".
unfold lt, eq; intros; red; intros. subst y.
destruct x.
eelim Plt_strict; eauto.
destruct H. eelim OrderedSlot.lt_not_eq; eauto. red; auto.
destruct H. destruct H0. omega.
destruct H0. eelim OrderedTyp.lt_not_eq; eauto. red; auto.
Qed.
Definition compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.compare".
intros. destruct x; destruct y.
- destruct (OrderedPositive.compare (IndexedMreg.index r) (IndexedMreg.index r0)).
+ apply LT. red. auto.
+ apply EQ. red. f_equal. apply IndexedMreg.index_inj. auto.
+ apply GT. red. auto.
- apply LT. red; auto.
- apply GT. red; auto.
- destruct (OrderedSlot.compare sl sl0).
+ apply LT. red; auto.
+ destruct (OrderedZ.compare pos pos0).
* apply LT. red. auto.
* destruct (OrderedTyp.compare ty ty0).
apply LT. red; auto.
apply EQ. red; red in e; red in e0; red in e1. congruence.
apply GT. red; auto.
* apply GT. red. auto.
+ apply GT. red; auto.
Defined.
Definition eq_dec := Loc.eq.



Definition diff_low_bound (l: loc) : loc :=
match l with
| R mr => l
| S sl ofs ty => S sl (ofs - 1) Tany64
end.

Definition diff_high_bound (l: loc) : loc :=
match l with
| R mr => l
| S sl ofs ty => S sl (ofs + typesize ty - 1) Tlong
end.

Lemma outside_interval_diff:
forall l l', lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l' -> Loc.diff l l'.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.outside_interval_diff".
intros.
destruct l as [mr | sl ofs ty]; destruct l' as [mr' | sl' ofs' ty']; simpl in *; auto.
- assert (IndexedMreg.index mr <> IndexedMreg.index mr').
{ destruct H. apply not_eq_sym. apply Plt_ne; auto. apply Plt_ne; auto. }
congruence.
- assert (RANGE: forall ty, 1 <= typesize ty <= 2).
{ intros; unfold typesize. destruct ty0; omega.  }
destruct H.
+ destruct H. left. apply not_eq_sym. apply OrderedSlot.lt_not_eq; auto.
destruct H. right.
destruct H0. right. generalize (RANGE ty'); omega.
destruct H0.
assert (ty' = Tint \/ ty' = Tsingle \/ ty' = Tany32).
{ unfold OrderedTyp.lt in H1. destruct ty'; auto; compute in H1; congruence. }
right. destruct H2 as [E|[E|E]]; subst ty'; simpl typesize; omega.
+ destruct H. left. apply OrderedSlot.lt_not_eq; auto.
destruct H. right.
destruct H0. left; omega.
destruct H0. exfalso. destruct ty'; compute in H1; congruence.
Qed.

Lemma diff_outside_interval:
forall l l', Loc.diff l l' -> lt l' (diff_low_bound l) \/ lt (diff_high_bound l) l'.
Proof. hammer_hook "Locations" "Locations.OrderedLoc.diff_outside_interval".
intros.
destruct l as [mr | sl ofs ty]; destruct l' as [mr' | sl' ofs' ty']; simpl in *; auto.
- unfold Plt, Pos.lt. destruct (Pos.compare (IndexedMreg.index mr) (IndexedMreg.index mr')) eqn:C.
elim H. apply IndexedMreg.index_inj. apply Pos.compare_eq_iff. auto.
auto.
rewrite Pos.compare_antisym. rewrite C. auto.
- destruct (OrderedSlot.compare sl sl'); auto.
destruct H. contradiction.
destruct H.
right; right; split; auto. left; omega.
left; right; split; auto.
assert (EITHER: typesize ty' = 1 /\ OrderedTyp.lt ty' Tany64 \/ typesize ty' = 2).
{ destruct ty'; compute; auto. }
destruct (zlt ofs' (ofs - 1)). left; auto.
destruct EITHER as [[P Q] | P].
right; split; auto. omega.
left; omega.
Qed.

End OrderedLoc.

