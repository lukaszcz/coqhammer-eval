From Hammer Require Import Hammer.













Require Import DecidableTypeEx.
Require Export FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.



Module WFacts_fun (Import E : DecidableType)(Import M : WSfun E).

Notation eq_dec := E.eq_dec.
Definition eqb x y := if eq_dec x y then true else false.



Section IffSpec.
Variable s s' s'' : t.
Variable x y z : elt.

Lemma In_eq_iff : E.eq x y -> (In x s <-> In y s).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.In_eq_iff".  
split; apply In_1; auto.
Qed.

Lemma mem_iff : In x s <-> mem x s = true.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.mem_iff".  
split; [apply mem_1|apply mem_2].
Qed.

Lemma not_mem_iff : ~In x s <-> mem x s = false.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.not_mem_iff".  
rewrite mem_iff; destruct (mem x s); intuition.
Qed.

Lemma equal_iff : s[=]s' <-> equal s s' = true.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.equal_iff".  
split; [apply equal_1|apply equal_2].
Qed.

Lemma subset_iff : s[<=]s' <-> subset s s' = true.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.subset_iff".  
split; [apply subset_1|apply subset_2].
Qed.

Lemma empty_iff : In x empty <-> False.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.empty_iff".  
intuition; apply (empty_1 H).
Qed.

Lemma is_empty_iff : Empty s <-> is_empty s = true.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.is_empty_iff".  
split; [apply is_empty_1|apply is_empty_2].
Qed.

Lemma singleton_iff : In y (singleton x) <-> E.eq x y.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.singleton_iff".  
split; [apply singleton_1|apply singleton_2].
Qed.

Lemma add_iff : In y (add x s) <-> E.eq x y \/ In y s.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.add_iff".  
split; [ | destruct 1; [apply add_1|apply add_2]]; auto.
destruct (eq_dec x y) as [E|E]; auto.
intro H; right; exact (add_3 E H).
Qed.

Lemma add_neq_iff : ~ E.eq x y -> (In y (add x s)  <-> In y s).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.add_neq_iff".  
split; [apply add_3|apply add_2]; auto.
Qed.

Lemma remove_iff : In y (remove x s) <-> In y s /\ ~E.eq x y.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.remove_iff".  
split; [split; [apply remove_3 with x |] | destruct 1; apply remove_2]; auto.
intro.
apply (remove_1 H0 H).
Qed.

Lemma remove_neq_iff : ~ E.eq x y -> (In y (remove x s) <-> In y s).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.remove_neq_iff".  
split; [apply remove_3|apply remove_2]; auto.
Qed.

Lemma union_iff : In x (union s s') <-> In x s \/ In x s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.union_iff".  
split; [apply union_1 | destruct 1; [apply union_2|apply union_3]]; auto.
Qed.

Lemma inter_iff : In x (inter s s') <-> In x s /\ In x s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.inter_iff".  
split; [split; [apply inter_1 with s' | apply inter_2 with s] | destruct 1; apply inter_3]; auto.
Qed.

Lemma diff_iff : In x (diff s s') <-> In x s /\ ~ In x s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.diff_iff".  
split; [split; [apply diff_1 with s' | apply diff_2 with s] | destruct 1; apply diff_3]; auto.
Qed.

Variable f : elt->bool.

Lemma filter_iff :  compat_bool E.eq f -> (In x (filter f s) <-> In x s /\ f x = true).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.filter_iff".  
split; [split; [apply filter_1 with f | apply filter_2 with s] | destruct 1; apply filter_3]; auto.
Qed.

Lemma for_all_iff : compat_bool E.eq f ->
(For_all (fun x => f x = true) s <-> for_all f s = true).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.for_all_iff".  
split; [apply for_all_1 | apply for_all_2]; auto.
Qed.

Lemma exists_iff : compat_bool E.eq f ->
(Exists (fun x => f x = true) s <-> exists_ f s = true).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.exists_iff".  
split; [apply exists_1 | apply exists_2]; auto.
Qed.

Lemma elements_iff : In x s <-> InA E.eq x (elements s).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.elements_iff".  
split; [apply elements_1 | apply elements_2].
Qed.

End IffSpec.



Ltac set_iff :=
repeat (progress (
rewrite add_iff || rewrite remove_iff || rewrite singleton_iff
|| rewrite union_iff || rewrite inter_iff || rewrite diff_iff
|| rewrite empty_iff)).



Section BoolSpec.
Variable s s' s'' : t.
Variable x y z : elt.

Lemma mem_b : E.eq x y -> mem x s = mem y s.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.mem_b".  
intros.
generalize (mem_iff s x) (mem_iff s y)(In_eq_iff s H).
destruct (mem x s); destruct (mem y s); intuition.
Qed.

Lemma empty_b : mem y empty = false.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.empty_b".  
generalize (empty_iff y)(mem_iff empty y).
destruct (mem y empty); intuition.
Qed.

Lemma add_b : mem y (add x s) = eqb x y || mem y s.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.add_b".  
generalize (mem_iff (add x s) y)(mem_iff s y)(add_iff s x y); unfold eqb.
destruct (eq_dec x y); destruct (mem y s); destruct (mem y (add x s)); intuition.
Qed.

Lemma add_neq_b : ~ E.eq x y -> mem y (add x s) = mem y s.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.add_neq_b".  
intros; generalize (mem_iff (add x s) y)(mem_iff s y)(add_neq_iff s H).
destruct (mem y s); destruct (mem y (add x s)); intuition.
Qed.

Lemma remove_b : mem y (remove x s) = mem y s && negb (eqb x y).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.remove_b".  
generalize (mem_iff (remove x s) y)(mem_iff s y)(remove_iff s x y); unfold eqb.
destruct (eq_dec x y); destruct (mem y s); destruct (mem y (remove x s)); simpl; intuition.
Qed.

Lemma remove_neq_b : ~ E.eq x y -> mem y (remove x s) = mem y s.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.remove_neq_b".  
intros; generalize (mem_iff (remove x s) y)(mem_iff s y)(remove_neq_iff s H).
destruct (mem y s); destruct (mem y (remove x s)); intuition.
Qed.

Lemma singleton_b : mem y (singleton x) = eqb x y.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.singleton_b".  
generalize (mem_iff (singleton x) y)(singleton_iff x y); unfold eqb.
destruct (eq_dec x y); destruct (mem y (singleton x)); intuition.
Qed.

Lemma union_b : mem x (union s s') = mem x s || mem x s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.union_b".  
generalize (mem_iff (union s s') x)(mem_iff s x)(mem_iff s' x)(union_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (union s s')); intuition.
Qed.

Lemma inter_b : mem x (inter s s') = mem x s && mem x s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.inter_b".  
generalize (mem_iff (inter s s') x)(mem_iff s x)(mem_iff s' x)(inter_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (inter s s')); intuition.
Qed.

Lemma diff_b : mem x (diff s s') = mem x s && negb (mem x s').
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.diff_b".  
generalize (mem_iff (diff s s') x)(mem_iff s x)(mem_iff s' x)(diff_iff s s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (diff s s')); simpl; intuition.
Qed.

Lemma elements_b : mem x s = existsb (eqb x) (elements s).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.elements_b".  
generalize (mem_iff s x)(elements_iff s x)(existsb_exists (eqb x) (elements s)).
rewrite InA_alt.
destruct (mem x s); destruct (existsb (eqb x) (elements s)); auto; intros.
symmetry.
rewrite H1.
destruct H0 as (H0,_).
destruct H0 as (a,(Ha1,Ha2)); [ intuition |].
exists a; intuition.
unfold eqb; destruct (eq_dec x a); auto.
rewrite <- H.
rewrite H0.
destruct H1 as (H1,_).
destruct H1 as (a,(Ha1,Ha2)); [intuition|].
exists a; intuition.
unfold eqb in *; destruct (eq_dec x a); auto; discriminate.
Qed.

Variable f : elt->bool.

Lemma filter_b : compat_bool E.eq f -> mem x (filter f s) = mem x s && f x.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.filter_b".  
intros.
generalize (mem_iff (filter f s) x)(mem_iff s x)(filter_iff s x H).
destruct (mem x s); destruct (mem x (filter f s)); destruct (f x); simpl; intuition.
Qed.

Lemma for_all_b : compat_bool E.eq f ->
for_all f s = forallb f (elements s).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.for_all_b".  
intros.
generalize (forallb_forall f (elements s))(for_all_iff s H)(elements_iff s).
unfold For_all.
destruct (forallb f (elements s)); destruct (for_all f s); auto; intros.
rewrite <- H1; intros.
destruct H0 as (H0,_).
rewrite (H2 x0) in H3.
rewrite (InA_alt E.eq x0 (elements s)) in H3.
destruct H3 as (a,(Ha1,Ha2)).
rewrite (H _ _ Ha1).
apply H0; auto.
symmetry.
rewrite H0; intros.
destruct H1 as (_,H1).
apply H1; auto.
rewrite H2.
rewrite InA_alt; eauto.
Qed.

Lemma exists_b : compat_bool E.eq f ->
exists_ f s = existsb f (elements s).
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.exists_b".  
intros.
generalize (existsb_exists f (elements s))(exists_iff s H)(elements_iff s).
unfold Exists.
destruct (existsb f (elements s)); destruct (exists_ f s); auto; intros.
rewrite <- H1; intros.
destruct H0 as (H0,_).
destruct H0 as (a,(Ha1,Ha2)); auto.
exists a; split; auto.
rewrite H2; rewrite InA_alt; eauto.
symmetry.
rewrite H0.
destruct H1 as (_,H1).
destruct H1 as (a,(Ha1,Ha2)); auto.
rewrite (H2 a) in Ha1.
rewrite (InA_alt E.eq a (elements s)) in Ha1.
destruct Ha1 as (b,(Hb1,Hb2)).
exists b; auto.
rewrite <- (H _ _ Hb1); auto.
Qed.

End BoolSpec.



Instance E_ST : Equivalence E.eq.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.E_ST".  
constructor ; red; [apply E.eq_refl|apply E.eq_sym|apply E.eq_trans].
Qed.

Instance Equal_ST : Equivalence Equal.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.Equal_ST".  
constructor ; red; [apply eq_refl | apply eq_sym | apply eq_trans].
Qed.

Instance In_m : Proper (E.eq ==> Equal ==> iff) In.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.In_m".  
unfold Equal; intros x y H s s' H0.
rewrite (In_eq_iff s H); auto.
Qed.

Instance is_empty_m : Proper (Equal==> Logic.eq) is_empty.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.is_empty_m".  
unfold Equal; intros s s' H.
generalize (is_empty_iff s)(is_empty_iff s').
destruct (is_empty s); destruct (is_empty s');
unfold Empty; auto; intros.
symmetry.
rewrite <- H1; intros a Ha.
rewrite <- (H a) in Ha.
destruct H0 as (_,H0).
exact (H0 Logic.eq_refl _ Ha).
rewrite <- H0; intros a Ha.
rewrite (H a) in Ha.
destruct H1 as (_,H1).
exact (H1 Logic.eq_refl _ Ha).
Qed.

Instance Empty_m : Proper (Equal ==> iff) Empty.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.Empty_m".  
repeat red; intros; do 2 rewrite is_empty_iff; rewrite H; intuition.
Qed.

Instance mem_m : Proper (E.eq ==> Equal ==> Logic.eq) mem.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.mem_m".  
unfold Equal; intros x y H s s' H0.
generalize (H0 x); clear H0; rewrite (In_eq_iff s' H).
generalize (mem_iff s x)(mem_iff s' y).
destruct (mem x s); destruct (mem y s'); intuition.
Qed.

Instance singleton_m : Proper (E.eq ==> Equal) singleton.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.singleton_m".  
unfold Equal; intros x y H a.
do 2 rewrite singleton_iff; split; intros.
apply E.eq_trans with x; auto.
apply E.eq_trans with y; auto.
Qed.

Instance add_m : Proper (E.eq==>Equal==>Equal) add.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.add_m".  
unfold Equal; intros x y H s s' H0 a.
do 2 rewrite add_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance remove_m : Proper (E.eq==>Equal==>Equal) remove.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.remove_m".  
unfold Equal; intros x y H s s' H0 a.
do 2 rewrite remove_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance union_m : Proper (Equal==>Equal==>Equal) union.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.union_m".  
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite union_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance inter_m : Proper (Equal==>Equal==>Equal) inter.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.inter_m".  
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite inter_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance diff_m : Proper (Equal==>Equal==>Equal) diff.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.diff_m".  
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite diff_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance Subset_m : Proper (Equal==>Equal==>iff) Subset.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.Subset_m".  
unfold Equal, Subset; firstorder.
Qed.

Instance subset_m : Proper (Equal ==> Equal ==> Logic.eq) subset.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.subset_m".  
intros s s' H s'' s''' H0.
generalize (subset_iff s s'') (subset_iff s' s''').
destruct (subset s s''); destruct (subset s' s'''); auto; intros.
rewrite H in H1; rewrite H0 in H1; intuition.
rewrite H in H1; rewrite H0 in H1; intuition.
Qed.

Instance equal_m : Proper (Equal ==> Equal ==> Logic.eq) equal.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.equal_m".  
intros s s' H s'' s''' H0.
generalize (equal_iff s s'') (equal_iff s' s''').
destruct (equal s s''); destruct (equal s' s'''); auto; intros.
rewrite H in H1; rewrite H0 in H1; intuition.
rewrite H in H1; rewrite H0 in H1; intuition.
Qed.




Lemma Subset_refl : forall s, s[<=]s.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.Subset_refl".   red; auto. Qed.

Lemma Subset_trans : forall s s' s'', s[<=]s'->s'[<=]s''->s[<=]s''.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.Subset_trans".   unfold Subset; eauto. Qed.

Add Relation t Subset
reflexivity proved by Subset_refl
transitivity proved by Subset_trans
as SubsetSetoid.

Instance In_s_m : Morphisms.Proper (E.eq ==> Subset ++> Basics.impl) In | 1.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.In_s_m".  
simpl_relation. eauto with set.
Qed.

Add Morphism Empty with signature Subset --> Basics.impl as Empty_s_m.
Proof.
unfold Subset, Empty, Basics.impl; firstorder.
Qed.

Add Morphism add with signature E.eq ==> Subset ++> Subset as add_s_m.
Proof.
unfold Subset; intros x y H s s' H0 a.
do 2 rewrite add_iff; rewrite H; intuition.
Qed.

Add Morphism remove with signature E.eq ==> Subset ++> Subset as remove_s_m.
Proof.
unfold Subset; intros x y H s s' H0 a.
do 2 rewrite remove_iff; rewrite H; intuition.
Qed.

Add Morphism union with signature Subset ++> Subset ++> Subset as union_s_m.
Proof.
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite union_iff; intuition.
Qed.

Add Morphism inter with signature Subset ++> Subset ++> Subset as inter_s_m.
Proof.
unfold Equal; intros s s' H s'' s''' H0 a.
do 2 rewrite inter_iff; intuition.
Qed.

Add Morphism diff with signature Subset ++> Subset --> Subset as diff_s_m.
Proof.
unfold Subset; intros s s' H s'' s''' H0 a.
do 2 rewrite diff_iff; intuition.
Qed.



Lemma filter_equal : forall f, compat_bool E.eq f ->
forall s s', s[=]s' -> filter f s [=] filter f s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.filter_equal".  
unfold Equal; intros; repeat rewrite filter_iff; auto; rewrite H0; tauto.
Qed.

Lemma filter_ext : forall f f', compat_bool E.eq f -> (forall x, f x = f' x) ->
forall s s', s[=]s' -> filter f s [=] filter f' s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.filter_ext".  
intros f f' Hf Hff' s s' Hss' x. do 2 (rewrite filter_iff; auto).
rewrite Hff', Hss'; intuition.
repeat red; intros; rewrite <- 2 Hff'; auto.
Qed.

Lemma filter_subset : forall f, compat_bool E.eq f ->
forall s s', s[<=]s' -> filter f s [<=] filter f s'.
Proof. hammer_hook "FSetFacts" "FSetFacts.WFacts_fun.filter_subset".  
unfold Subset; intros; rewrite filter_iff in *; intuition.
Qed.





End WFacts_fun.



Module WFacts (M:WS) := WFacts_fun M.E M.
Module Facts := WFacts.
