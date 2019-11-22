From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.








Inductive tm : Type :=
| C : nat -> tm
| P : tm -> tm -> tm.



Fixpoint evalF (t : tm) : nat :=
match t with
| C n => n
| P a1 a2 => evalF a1 + evalF a2
end.



Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
| E_Const : forall n,
C n ==> n
| E_Plus : forall t1 t2 n1 n2,
t1 ==> n1 ->
t2 ==> n2 ->
P t1 t2 ==> (n1 + n2)
where " t '==>' n " := (eval t n).

Module SimpleArith1.



Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
P (C n1) (C n2) --> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
t1 --> t1' ->
P t1 t2 --> P t1' t2
| ST_Plus2 : forall n1 t2 t2',
t2 --> t2' ->
P (C n1) t2 --> P (C n1) t2'

where " t '-->' t' " := (step t t').







Example test_step_1 :
P
(P (C 0) (C 3))
(P (C 2) (C 4))
-->
P
(C (0 + 3))
(P (C 2) (C 4)).
Proof. hammer_hook "Smallstep" "Smallstep.SimpleArith1.test_step_1".
apply ST_Plus1. apply ST_PlusConstConst.  Qed.



Example test_step_2 :
P
(C 0)
(P
(C 2)
(P (C 0) (C 3)))
-->
P
(C 0)
(P
(C 2)
(C (0 + 3))).
Proof. hammer_hook "Smallstep" "Smallstep.SimpleArith1.test_step_2".
Admitted.


End SimpleArith1.






Definition relation (X : Type) := X -> X -> Prop.









Definition deterministic {X : Type} (R : relation X) :=
forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
deterministic step.
Proof. hammer_hook "Smallstep" "Smallstep.SimpleArith2.step_deterministic".
unfold deterministic. intros x y1 y2 Hy1 Hy2.
generalize dependent y2.
induction Hy1; intros y2 Hy2.
-  inversion Hy2.
+  reflexivity.
+  inversion H2.
+  inversion H2.
-  inversion Hy2.
+
rewrite <- H0 in Hy1. inversion Hy1.
+
rewrite <- (IHHy1 t1'0).
reflexivity. assumption.
+
rewrite <- H in Hy1. inversion Hy1.
-  inversion Hy2.
+
rewrite <- H1 in Hy1. inversion Hy1.
+  inversion H2.
+
rewrite <- (IHHy1 t2'0).
reflexivity. assumption.
Qed.

End SimpleArith2.



Ltac solve_by_inverts n :=
match goal with | H : ?T |- _ =>
match type of T with Prop =>
solve [
inversion H;
match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
end end.



Ltac solve_by_invert :=
solve_by_inverts 1.



Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof. hammer_hook "Smallstep" "Smallstep.SimpleArith3.step_deterministic_alt".
intros x y1 y2 Hy1 Hy2.
generalize dependent y2.
induction Hy1; intros y2 Hy2;
inversion Hy2; subst; try solve_by_invert.
-  reflexivity.
-
apply IHHy1 in H2. rewrite H2. reflexivity.
-
apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.












Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).







Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
P (C n1) (C n2)
--> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
t1 --> t1' ->
P t1 t2 --> P t1' t2
| ST_Plus2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
P v1 t2 --> P v1 t2'

where " t '-->' t' " := (step t t').





Theorem step_deterministic :
deterministic step.
Proof. hammer_hook "Smallstep" "Smallstep.step_deterministic".
Admitted.











Theorem strong_progress : forall t,
value t \/ (exists t', t --> t').
Proof. hammer_hook "Smallstep" "Smallstep.strong_progress".
induction t.
-  left. apply v_const.
-  right. destruct IHt1 as [IHt1 | [t1' Ht1]].
+  destruct IHt2 as [IHt2 | [t2' Ht2]].
*  inversion IHt1. inversion IHt2.
exists (C (n + n0)).
apply ST_PlusConstConst.
*
exists (P t1 t2').
apply ST_Plus2. apply IHt1. apply Ht2.
+
exists (P t1' t2).
apply ST_Plus1. apply Ht1.
Qed.





Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
~ exists t', R t t'.





Lemma value_is_nf : forall v,
value v -> normal_form step v.
Proof. hammer_hook "Smallstep" "Smallstep.value_is_nf".
unfold normal_form. intros v H. inversion H.
intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
normal_form step t -> value t.
Proof. hammer_hook "Smallstep" "Smallstep.nf_is_value".
unfold normal_form. intros t H.
assert (G : value t \/ exists t', t --> t').
{ apply strong_progress. }
destruct G as [G | G].
-  apply G.
-  exfalso. apply H. assumption.
Qed.

Corollary nf_same_as_value : forall t,
normal_form step t <-> value t.
Proof. hammer_hook "Smallstep" "Smallstep.nf_same_as_value".
split. apply nf_is_value. apply value_is_nf.
Qed.







Module Temp1.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n)
| v_funny : forall t1 n2,
value (P t1 (C n2)).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
P (C n1) (C n2) --> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
t1 --> t1' ->
P t1 t2 --> P t1' t2
| ST_Plus2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
P v1 t2 --> P v1 t2'

where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
exists v, value v /\ ~ normal_form step v.
Proof. hammer_hook "Smallstep" "Smallstep.Temp1.value_not_same_as_normal_form".
Admitted.
End Temp1.





Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_Funny : forall n,
C n --> P (C n) (C 0)
| ST_PlusConstConst : forall n1 n2,
P (C n1) (C n2) --> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
t1 --> t1' ->
P t1 t2 --> P t1' t2
| ST_Plus2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
P v1 t2 --> P v1 t2'

where " t '-->' t' " := (step t t').

Lemma value_not_same_as_normal_form :
exists v, value v /\ ~ normal_form step v.
Proof. hammer_hook "Smallstep" "Smallstep.Temp2.value_not_same_as_normal_form".
Admitted.

End Temp2.




Module Temp3.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
P (C n1) (C n2) --> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
t1 --> t1' ->
P t1 t2 --> P t1' t2

where " t '-->' t' " := (step t t').



Lemma value_not_same_as_normal_form :
exists t, ~ value t /\ normal_form step t.
Proof. hammer_hook "Smallstep" "Smallstep.Temp3.value_not_same_as_normal_form".
Admitted.

End Temp3.





Module Temp4.



Inductive tm : Type :=
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
| v_tru : value tru
| v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_IfTrue : forall t1 t2,
test tru t1 t2 --> t1
| ST_IfFalse : forall t1 t2,
test fls t1 t2 --> t2
| ST_If : forall t1 t1' t2 t3,
t1 --> t1' ->
test t1 t2 t3 --> test t1' t2 t3

where " t '-->' t' " := (step t t').



Definition bool_step_prop1 :=
fls --> fls.



Definition bool_step_prop2 :=
test
tru
(test tru tru tru)
(test fls fls fls)
-->
tru.



Definition bool_step_prop3 :=
test
(test tru tru tru)
(test tru tru tru)
fls
-->
test
tru
(test tru tru tru)
fls.




Definition manual_grade_for_smallstep_bools : option (nat*string) := None.




Theorem strong_progress : forall t,
value t \/ (exists t', t --> t').
Proof. hammer_hook "Smallstep" "Smallstep.Temp4.strong_progress".
Admitted.



Theorem step_deterministic :
deterministic step.
Proof. hammer_hook "Smallstep" "Smallstep.Temp4.step_deterministic".
Admitted.


Module Temp5.





Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_IfTrue : forall t1 t2,
test tru t1 t2 --> t1
| ST_IfFalse : forall t1 t2,
test fls t1 t2 --> t2
| ST_If : forall t1 t1' t2 t3,
t1 --> t1' ->
test t1 t2 t3 --> test t1' t2 t3


where " t '-->' t' " := (step t t').

Definition bool_step_prop4 :=
test
(test tru tru tru)
fls
fls
-->
fls.

Example bool_step_prop4_holds :
bool_step_prop4.
Proof. hammer_hook "Smallstep" "Smallstep.Temp4.Temp5.bool_step_prop4_holds".
Admitted.








End Temp5.
End Temp4.








Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : forall (x : X), multi R x x
| multi_step : forall (x y z : X),
R x y ->
multi R y z ->
multi R x z.







Notation " t '-->*' t' " := (multi step t t') (at level 40).





Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
R x y -> (multi R) x y.
Proof. hammer_hook "Smallstep" "Smallstep.multi_R".
intros X R x y H.
apply multi_step with y. apply H. apply multi_refl.
Qed.



Theorem multi_trans :
forall (X : Type) (R : relation X) (x y z : X),
multi R x y  ->
multi R y z ->
multi R x z.
Proof. hammer_hook "Smallstep" "Smallstep.multi_trans".
intros X R x y z G H.
induction G.
-  assumption.
-
apply multi_step with y. assumption.
apply IHG. assumption.
Qed.








Lemma test_multistep_1:
P
(P (C 0) (C 3))
(P (C 2) (C 4))
-->*
C ((0 + 3) + (2 + 4)).
Proof. hammer_hook "Smallstep" "Smallstep.test_multistep_1".
apply multi_step with
(P (C (0 + 3))
(P (C 2) (C 4))).
{ apply ST_Plus1. apply ST_PlusConstConst. }
apply multi_step with
(P (C (0 + 3))
(C (2 + 4))).
{ apply ST_Plus2. apply v_const. apply ST_PlusConstConst. }
apply multi_R.
{ apply ST_PlusConstConst. }
Qed.



Lemma test_multistep_1':
P
(P (C 0) (C 3))
(P (C 2) (C 4))
-->*
C ((0 + 3) + (2 + 4)).
Proof. hammer_hook "Smallstep" "Smallstep.test_multistep_1'".
eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
eapply multi_step. { apply ST_Plus2. apply v_const.
apply ST_PlusConstConst. }
eapply multi_step. { apply ST_PlusConstConst. }
apply multi_refl.
Qed.


Lemma test_multistep_2:
C 3 -->* C 3.
Proof. hammer_hook "Smallstep" "Smallstep.test_multistep_2".
Admitted.



Lemma test_multistep_3:
P (C 0) (C 3)
-->*
P (C 0) (C 3).
Proof. hammer_hook "Smallstep" "Smallstep.test_multistep_3".
Admitted.



Lemma test_multistep_4:
P
(C 0)
(P
(C 2)
(P (C 0) (C 3)))
-->*
P
(C 0)
(C (2 + (0 + 3))).
Proof. hammer_hook "Smallstep" "Smallstep.test_multistep_4".
Admitted.







Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
(t -->* t' /\ step_normal_form t').




Theorem normal_forms_unique:
deterministic normal_form_of.
Proof. hammer_hook "Smallstep" "Smallstep.normal_forms_unique".

unfold deterministic. unfold normal_form_of.
intros x y1 y2 P1 P2.
inversion P1 as [P11 P12]; clear P1.
inversion P2 as [P21 P22]; clear P2.
generalize dependent y2.
Admitted.




Definition normalizing {X : Type} (R : relation X) :=
forall t, exists t',
(multi R) t t' /\ normal_form R t'.



Lemma multistep_congr_1 : forall t1 t1' t2,
t1 -->* t1' ->
P t1 t2 -->* P t1' t2.
Proof. hammer_hook "Smallstep" "Smallstep.multistep_congr_1".
intros t1 t1' t2 H. induction H.
-  apply multi_refl.
-  apply multi_step with (P y t2).
+ apply ST_Plus1. apply H.
+ apply IHmulti.
Qed.


Lemma multistep_congr_2 : forall t1 t2 t2',
value t1 ->
t2 -->* t2' ->
P t1 t2 -->* P t1 t2'.
Proof. hammer_hook "Smallstep" "Smallstep.multistep_congr_2".
Admitted.




Theorem step_normalizing :
normalizing step.
Proof. hammer_hook "Smallstep" "Smallstep.step_normalizing".
unfold normalizing.
induction t.
-
exists (C n).
split.
+  apply multi_refl.
+

rewrite nf_same_as_value. apply v_const.
-
destruct IHt1 as [t1' [Hsteps1 Hnormal1]].
destruct IHt2 as [t2' [Hsteps2 Hnormal2]].
rewrite nf_same_as_value in Hnormal1.
rewrite nf_same_as_value in Hnormal2.
inversion Hnormal1 as [n1 H1].
inversion Hnormal2 as [n2 H2].
rewrite <- H1 in Hsteps1.
rewrite <- H2 in Hsteps2.
exists (C (n1 + n2)).
split.
+
apply multi_trans with (P (C n1) t2).
* apply multistep_congr_1. apply Hsteps1.
* apply multi_trans with
(P (C n1) (C n2)).
{ apply multistep_congr_2. apply v_const. apply Hsteps2. }
apply multi_R. { apply ST_PlusConstConst. }
+
rewrite nf_same_as_value. apply v_const.
Qed.







Theorem eval__multistep : forall t n,
t ==> n -> t -->* C n.





Proof. hammer_hook "Smallstep" "Smallstep.eval__multistep".
Admitted.





Definition manual_grade_for_eval__multistep_inf : option (nat*string) := None.





Lemma step__eval : forall t t' n,
t --> t' ->
t' ==> n ->
t  ==> n.
Proof. hammer_hook "Smallstep" "Smallstep.step__eval".
intros t t' n Hs. generalize dependent n.
Admitted.







Theorem multistep__eval : forall t t',
normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof. hammer_hook "Smallstep" "Smallstep.multistep__eval".
Admitted.







Theorem evalF_eval : forall t n,
evalF t = n <-> t ==> n.
Proof. hammer_hook "Smallstep" "Smallstep.evalF_eval".
Admitted.




Module Combined.

Inductive tm : Type :=
| C : nat -> tm
| P : tm -> tm -> tm
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n)
| v_tru : value tru
| v_fls : value fls.

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
P (C n1) (C n2) --> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
t1 --> t1' ->
P t1 t2 --> P t1' t2
| ST_Plus2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
P v1 t2 --> P v1 t2'
| ST_IfTrue : forall t1 t2,
test tru t1 t2 --> t1
| ST_IfFalse : forall t1 t2,
test fls t1 t2 --> t2
| ST_If : forall t1 t1' t2 t3,
t1 --> t1' ->
test t1 t2 t3 --> test t1' t2 t3

where " t '-->' t' " := (step t t').





End Combined.


Definition manual_grade_for_combined_properties : option (nat*string) := None.









Inductive aval : aexp -> Prop :=
| av_num : forall n, aval (ANum n).



Reserved Notation " t '/' st '-->a' t' "
(at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
| AS_Id : forall st i,
AId i / st -->a ANum (st i)
| AS_Plus1 : forall st a1 a1' a2,
a1 / st -->a a1' ->
(APlus a1 a2) / st -->a (APlus a1' a2)
| AS_Plus2 : forall st v1 a2 a2',
aval v1 ->
a2 / st -->a a2' ->
(APlus v1 a2) / st -->a (APlus v1 a2')
| AS_Plus : forall st n1 n2,
APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
| AS_Minus1 : forall st a1 a1' a2,
a1 / st -->a a1' ->
(AMinus a1 a2) / st -->a (AMinus a1' a2)
| AS_Minus2 : forall st v1 a2 a2',
aval v1 ->
a2 / st -->a a2' ->
(AMinus v1 a2) / st -->a (AMinus v1 a2')
| AS_Minus : forall st n1 n2,
(AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
| AS_Mult1 : forall st a1 a1' a2,
a1 / st -->a a1' ->
(AMult a1 a2) / st -->a (AMult a1' a2)
| AS_Mult2 : forall st v1 a2 a2',
aval v1 ->
a2 / st -->a a2' ->
(AMult v1 a2) / st -->a (AMult v1 a2')
| AS_Mult : forall st n1 n2,
(AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))

where " t '/' st '-->a' t' " := (astep st t t').

Reserved Notation " t '/' st '-->b' t' "
(at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
a1 / st -->a a1' ->
(BEq a1 a2) / st -->b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
aval v1 ->
a2 / st -->a a2' ->
(BEq v1 a2) / st -->b (BEq v1 a2')
| BS_Eq : forall st n1 n2,
(BEq (ANum n1) (ANum n2)) / st -->b
(if (n1 =? n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
a1 / st -->a a1' ->
(BLe a1 a2) / st -->b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
aval v1 ->
a2 / st -->a a2' ->
(BLe v1 a2) / st -->b (BLe v1 a2')
| BS_LtEq : forall st n1 n2,
(BLe (ANum n1) (ANum n2)) / st -->b
(if (n1 <=? n2) then BTrue else BFalse)
| BS_NotStep : forall st b1 b1',
b1 / st -->b b1' ->
(BNot b1) / st -->b (BNot b1')
| BS_NotTrue : forall st,
(BNot BTrue) / st -->b BFalse
| BS_NotFalse : forall st,
(BNot BFalse) / st -->b BTrue
| BS_AndTrueStep : forall st b2 b2',
b2 / st -->b b2' ->
(BAnd BTrue b2) / st -->b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
b1 / st -->b b1' ->
(BAnd b1 b2) / st -->b (BAnd b1' b2)
| BS_AndTrueTrue : forall st,
(BAnd BTrue BTrue) / st -->b BTrue
| BS_AndTrueFalse : forall st,
(BAnd BTrue BFalse) / st -->b BFalse
| BS_AndFalse : forall st b2,
(BAnd BFalse b2) / st -->b BFalse

where " t '/' st '-->b' t' " := (bstep st t t').





Reserved Notation " t '/' st '-->' t' '/' st' "
(at level 40, st at level 39, t' at level 39).

Open Scope imp_scope.
Inductive cstep : (com * state) -> (com * state) -> Prop :=
| CS_AssStep : forall st i a a',
a / st -->a a' ->
(i ::= a) / st --> (i ::= a') / st
| CS_Ass : forall st i n,
(i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
| CS_SeqStep : forall st c1 c1' st' c2,
c1 / st --> c1' / st' ->
(c1 ;; c2) / st --> (c1' ;; c2) / st'
| CS_SeqFinish : forall st c2,
(SKIP ;; c2) / st --> c2 / st
| CS_IfStep : forall st b b' c1 c2,
b / st -->b b' ->
TEST b  THEN c1 ELSE c2 FI / st
-->
(TEST b' THEN c1 ELSE c2 FI) / st
| CS_IfTrue : forall st c1 c2,
TEST BTrue THEN c1 ELSE c2 FI / st --> c1 / st
| CS_IfFalse : forall st c1 c2,
TEST BFalse THEN c1 ELSE c2 FI / st --> c2 / st
| CS_While : forall st b c1,
WHILE b DO c1 END / st
-->
(TEST b THEN c1;; WHILE b DO c1 END ELSE SKIP FI) / st

where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Close Scope imp_scope.






Module CImp.

Inductive com : Type :=
| CSkip : com
| CAss : string -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CPar : com -> com -> com.

Notation "'SKIP'" :=
CSkip.
Notation "x '::=' a" :=
(CAss x a) (at level 60).
Notation "c1 ;; c2" :=
(CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
(CWhile b c) (at level 80, right associativity).
Notation "'TEST' b 'THEN' c1 'ELSE' c2 'FI'" :=
(CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
(CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=

| CS_AssStep : forall st i a a',
a / st -->a a' ->
(i ::= a) / st --> (i ::= a') / st
| CS_Ass : forall st i n,
(i ::= (ANum n)) / st --> SKIP / (i !-> n ; st)
| CS_SeqStep : forall st c1 c1' st' c2,
c1 / st --> c1' / st' ->
(c1 ;; c2) / st --> (c1' ;; c2) / st'
| CS_SeqFinish : forall st c2,
(SKIP ;; c2) / st --> c2 / st
| CS_IfStep : forall st b b' c1 c2,
b /st -->b b' ->
(TEST b THEN c1 ELSE c2 FI) / st
--> (TEST b' THEN c1 ELSE c2 FI) / st
| CS_IfTrue : forall st c1 c2,
(TEST BTrue THEN c1 ELSE c2 FI) / st --> c1 / st
| CS_IfFalse : forall st c1 c2,
(TEST BFalse THEN c1 ELSE c2 FI) / st --> c2 / st
| CS_While : forall st b c1,
(WHILE b DO c1 END) / st
--> (TEST b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

| CS_Par1 : forall st c1 c1' c2 st',
c1 / st --> c1' / st' ->
(PAR c1 WITH c2 END) / st --> (PAR c1' WITH c2 END) / st'
| CS_Par2 : forall st c1 c2 c2' st',
c2 / st --> c2' / st' ->
(PAR c1 WITH c2 END) / st --> (PAR c1 WITH c2' END) / st'
| CS_ParDone : forall st,
(PAR SKIP WITH SKIP END) / st --> SKIP / st
where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
(multi cstep  (t,st) (t',st'))
(at level 40, st at level 39, t' at level 39).



Definition par_loop : com :=
PAR
Y ::= 1
WITH
WHILE Y = 0 DO
X ::= X + 1
END
END.



Example par_loop_example_0:
exists st',
par_loop / empty_st  -->* SKIP / st'
/\ st' X = 0.
Proof. hammer_hook "Smallstep" "Smallstep.CImp.par_loop_example_0".
eapply ex_intro. split.
unfold par_loop.
eapply multi_step. apply CS_Par1.
apply CS_Ass.
eapply multi_step. apply CS_Par2. apply CS_While.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq1. apply AS_Id.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq. simpl.
eapply multi_step. apply CS_Par2. apply CS_IfFalse.
eapply multi_step. apply CS_ParDone.
eapply multi_refl.
reflexivity. Qed.



Example par_loop_example_2:
exists st',
par_loop / empty_st -->* SKIP / st'
/\ st' X = 2.
Proof. hammer_hook "Smallstep" "Smallstep.CImp.par_loop_example_2".
eapply ex_intro. split.
eapply multi_step. apply CS_Par2. apply CS_While.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq1. apply AS_Id.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq. simpl.
eapply multi_step. apply CS_Par2. apply CS_IfTrue.
eapply multi_step. apply CS_Par2. apply CS_SeqStep.
apply CS_AssStep. apply AS_Plus1. apply AS_Id.
eapply multi_step. apply CS_Par2. apply CS_SeqStep.
apply CS_AssStep. apply AS_Plus.
eapply multi_step. apply CS_Par2. apply CS_SeqStep.
apply CS_Ass.
eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

eapply multi_step. apply CS_Par2. apply CS_While.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq1. apply AS_Id.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq. simpl.
eapply multi_step. apply CS_Par2. apply CS_IfTrue.
eapply multi_step. apply CS_Par2. apply CS_SeqStep.
apply CS_AssStep. apply AS_Plus1. apply AS_Id.
eapply multi_step. apply CS_Par2. apply CS_SeqStep.
apply CS_AssStep. apply AS_Plus.
eapply multi_step. apply CS_Par2. apply CS_SeqStep.
apply CS_Ass.

eapply multi_step. apply CS_Par1. apply CS_Ass.
eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
eapply multi_step. apply CS_Par2. apply CS_While.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq1. apply AS_Id.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq. simpl.
eapply multi_step. apply CS_Par2. apply CS_IfFalse.
eapply multi_step. apply CS_ParDone.
eapply multi_refl.
reflexivity. Qed.




Lemma par_body_n__Sn : forall n st,
st X = n /\ st Y = 0 ->
par_loop / st -->* par_loop / (X !-> S n ; st).
Proof. hammer_hook "Smallstep" "Smallstep.CImp.par_body_n__Sn".
Admitted.



Lemma par_body_n : forall n st,
st X = 0 /\ st Y = 0 ->
exists st',
par_loop / st -->*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof. hammer_hook "Smallstep" "Smallstep.CImp.par_body_n".
Admitted.




Theorem par_loop_any_X:
forall n, exists st',
par_loop / empty_st -->*  SKIP / st'
/\ st' X = n.
Proof. hammer_hook "Smallstep" "Smallstep.CImp.par_loop_any_X".
intros n.
destruct (par_body_n n empty_st).
split; unfold t_update; reflexivity.

rename x into st.
inversion H as [H' [HX HY]]; clear H.
exists (Y !-> 1 ; st). split.
eapply multi_trans with (par_loop,st). apply H'.
eapply multi_step. apply CS_Par1. apply CS_Ass.
eapply multi_step. apply CS_Par2. apply CS_While.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq1. apply AS_Id. rewrite t_update_eq.
eapply multi_step. apply CS_Par2. apply CS_IfStep.
apply BS_Eq. simpl.
eapply multi_step. apply CS_Par2. apply CS_IfFalse.
eapply multi_step. apply CS_ParDone.
apply multi_refl.

rewrite t_update_neq. assumption. intro X; inversion X.
Qed.

End CImp.






Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
| SS_Push : forall st stk n p',
stack_step st (SPush n :: p', stk)      (p', n :: stk)
| SS_Load : forall st stk i p',
stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
| SS_Plus : forall st stk n m p',
stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
| SS_Minus : forall st stk n m p',
stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
| SS_Mult : forall st stk n m p',
stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st,
deterministic (stack_step st).
Proof. hammer_hook "Smallstep" "Smallstep.stack_step_deterministic".
unfold deterministic. intros st x y1 y2 H1 H2.
induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).



Definition compiler_is_correct_statement : Prop
. Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof. hammer_hook "Smallstep" "Smallstep.compiler_is_correct".
Admitted.







Example step_example1 :
(P (C 3) (P (C 3) (C 4)))
-->* (C 10).
Proof. hammer_hook "Smallstep" "Smallstep.step_example1".
apply multi_step with (P (C 3) (C 7)).
apply ST_Plus2.
apply v_const.
apply ST_PlusConstConst.
apply multi_step with (C 10).
apply ST_PlusConstConst.
apply multi_refl.
Qed.



Hint Constructors step value.
Example step_example1' :
(P (C 3) (P (C 3) (C 4)))
-->* (C 10).
Proof. hammer_hook "Smallstep" "Smallstep.step_example1'".
eapply multi_step. auto. simpl.
eapply multi_step. auto. simpl.
apply multi_refl.
Qed.



Tactic Notation "print_goal" :=
match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
repeat (print_goal; eapply multi_step ;
[ (eauto 10; fail) | (instantiate; simpl)]);
apply multi_refl.

Example step_example1'' :
(P (C 3) (P (C 3) (C 4)))
-->* (C 10).
Proof. hammer_hook "Smallstep" "Smallstep.step_example1''".
normalize.

Qed.



Example step_example1''' : exists e',
(P (C 3) (P (C 3) (C 4)))
-->* e'.
Proof. hammer_hook "Smallstep" "Smallstep.step_example1'''".
eapply ex_intro. normalize.

Qed.


Theorem normalize_ex : exists e',
(P (C 3) (P (C 2) (C 1)))
-->* e' /\ value e'.
Proof. hammer_hook "Smallstep" "Smallstep.normalize_ex".
Admitted.




Theorem normalize_ex' : exists e',
(P (C 3) (P (C 2) (C 1)))
-->* e' /\ value e'.
Proof. hammer_hook "Smallstep" "Smallstep.normalize_ex'".
Admitted.



