From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From Coq Require Import Strings.String.

































































































































Module STLCExtended.






Inductive ty : Type :=
| Arrow : ty -> ty -> ty
| Nat  : ty
| Sum  : ty -> ty -> ty
| List : ty -> ty
| Unit : ty
| Prod : ty -> ty -> ty.

Inductive tm : Type :=

| var : string -> tm
| app : tm -> tm -> tm
| abs : string -> ty -> tm -> tm

| const : nat -> tm
| scc : tm -> tm
| prd : tm -> tm
| mlt : tm -> tm -> tm
| test0  : tm -> tm -> tm -> tm

| tinl : ty -> tm -> tm
| tinr : ty -> tm -> tm
| tcase : tm -> string -> tm -> string -> tm -> tm


| tnil : ty -> tm
| tcons : tm -> tm -> tm
| tlcase : tm -> tm -> string -> string -> tm -> tm


| unit : tm




| pair : tm -> tm -> tm
| fst : tm -> tm
| snd : tm -> tm

| tlet : string -> tm -> tm -> tm


| tfix  : tm -> tm.






Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
match t with

| var y =>
if eqb_string x y then s else t
| abs y T t1 =>
abs y T (if eqb_string x y then t1 else (subst x s t1))
| app t1 t2 =>
app (subst x s t1) (subst x s t2)

| const n =>
const n
| scc t1 =>
scc (subst x s t1)
| prd t1 =>
prd (subst x s t1)
| mlt t1 t2 =>
mlt (subst x s t1) (subst x s t2)
| test0 t1 t2 t3 =>
test0 (subst x s t1) (subst x s t2) (subst x s t3)

| tinl T t1 =>
tinl T (subst x s t1)
| tinr T t1 =>
tinr T (subst x s t1)
| tcase t0 y1 t1 y2 t2 =>
tcase (subst x s t0)
y1 (if eqb_string x y1 then t1 else (subst x s t1))
y2 (if eqb_string x y2 then t2 else (subst x s t2))

| tnil T =>
tnil T
| tcons t1 t2 =>
tcons (subst x s t1) (subst x s t2)
| tlcase t1 t2 y1 y2 t3 =>
tlcase (subst x s t1) (subst x s t2) y1 y2
(if eqb_string x y1 then
t3
else if eqb_string x y2 then t3
else (subst x s t3))

| unit => unit









| _ => t
end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).






Inductive value : tm -> Prop :=

| v_abs : forall x T11 t12,
value (abs x T11 t12)

| v_nat : forall n1,
value (const n1)

| v_inl : forall v T,
value v ->
value (tinl T v)
| v_inr : forall v T,
value v ->
value (tinr T v)

| v_lnil : forall T, value (tnil T)
| v_lcons : forall v1 vl,
value v1 ->
value vl ->
value (tcons v1 vl)

| v_unit : value unit

| v_pair : forall v1 v2,
value v1 ->
value v2 ->
value (pair v1 v2).

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=

| ST_AppAbs : forall x T11 t12 v2,
value v2 ->
(app (abs x T11 t12) v2) --> [x:=v2]t12
| ST_App1 : forall t1 t1' t2,
t1 --> t1' ->
(app t1 t2) --> (app t1' t2)
| ST_App2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
(app v1 t2) --> (app v1 t2')

| ST_Succ1 : forall t1 t1',
t1 --> t1' ->
(scc t1) --> (scc t1')
| ST_SuccNat : forall n1,
(scc (const n1)) --> (const (S n1))
| ST_Pred : forall t1 t1',
t1 --> t1' ->
(prd t1) --> (prd t1')
| ST_PredNat : forall n1,
(prd (const n1)) --> (const (pred n1))
| ST_Mult1 : forall t1 t1' t2,
t1 --> t1' ->
(mlt t1 t2) --> (mlt t1' t2)
| ST_Mult2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
(mlt v1 t2) --> (mlt v1 t2')
| ST_Mulconsts : forall n1 n2,
(mlt (const n1) (const n2)) --> (const (mult n1 n2))
| ST_Test01 : forall t1 t1' t2 t3,
t1 --> t1' ->
(test0 t1 t2 t3) --> (test0 t1' t2 t3)
| ST_Test0Zero : forall t2 t3,
(test0 (const 0) t2 t3) --> t2
| ST_Test0Nonzero : forall n t2 t3,
(test0 (const (S n)) t2 t3) --> t3

| ST_Inl : forall t1 t1' T,
t1 --> t1' ->
(tinl T t1) --> (tinl T t1')
| ST_Inr : forall t1 t1' T,
t1 --> t1' ->
(tinr T t1) --> (tinr T t1')
| ST_Case : forall t0 t0' x1 t1 x2 t2,
t0 --> t0' ->
(tcase t0 x1 t1 x2 t2) --> (tcase t0' x1 t1 x2 t2)
| ST_CaseInl : forall v0 x1 t1 x2 t2 T,
value v0 ->
(tcase (tinl T v0) x1 t1 x2 t2) --> [x1:=v0]t1
| ST_CaseInr : forall v0 x1 t1 x2 t2 T,
value v0 ->
(tcase (tinr T v0) x1 t1 x2 t2) --> [x2:=v0]t2

| ST_Cons1 : forall t1 t1' t2,
t1 --> t1' ->
(tcons t1 t2) --> (tcons t1' t2)
| ST_Cons2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
(tcons v1 t2) --> (tcons v1 t2')
| ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
t1 --> t1' ->
(tlcase t1 t2 x1 x2 t3) --> (tlcase t1' t2 x1 x2 t3)
| ST_LcaseNil : forall T t2 x1 x2 t3,
(tlcase (tnil T) t2 x1 x2 t3) --> t2
| ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
value v1 ->
value vl ->
(tlcase (tcons v1 vl) t2 x1 x2 t3)
--> (subst x2 vl (subst x1 v1 t3))










where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.




Definition context := partial_map ty.



Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=

| T_Var : forall Gamma x T,
Gamma x = Some T ->
Gamma |- (var x) \in T
| T_Abs : forall Gamma x T11 T12 t12,
(update Gamma x T11) |- t12 \in T12 ->
Gamma |- (abs x T11 t12) \in (Arrow T11 T12)
| T_App : forall T1 T2 Gamma t1 t2,
Gamma |- t1 \in (Arrow T1 T2) ->
Gamma |- t2 \in T1 ->
Gamma |- (app t1 t2) \in T2

| T_Nat : forall Gamma n1,
Gamma |- (const n1) \in Nat
| T_Succ : forall Gamma t1,
Gamma |- t1 \in Nat ->
Gamma |- (scc t1) \in Nat
| T_Pred : forall Gamma t1,
Gamma |- t1 \in Nat ->
Gamma |- (prd t1) \in Nat
| T_Mult : forall Gamma t1 t2,
Gamma |- t1 \in Nat ->
Gamma |- t2 \in Nat ->
Gamma |- (mlt t1 t2) \in Nat
| T_Test0 : forall Gamma t1 t2 t3 T1,
Gamma |- t1 \in Nat ->
Gamma |- t2 \in T1 ->
Gamma |- t3 \in T1 ->
Gamma |- (test0 t1 t2 t3) \in T1

| T_Inl : forall Gamma t1 T1 T2,
Gamma |- t1 \in T1 ->
Gamma |- (tinl T2 t1) \in (Sum T1 T2)
| T_Inr : forall Gamma t2 T1 T2,
Gamma |- t2 \in T2 ->
Gamma |- (tinr T1 t2) \in (Sum T1 T2)
| T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
Gamma |- t0 \in (Sum T1 T2) ->
(update Gamma x1 T1) |- t1 \in T ->
(update Gamma x2 T2) |- t2 \in T ->
Gamma |- (tcase t0 x1 t1 x2 t2) \in T

| T_Nil : forall Gamma T,
Gamma |- (tnil T) \in (List T)
| T_Cons : forall Gamma t1 t2 T1,
Gamma |- t1 \in T1 ->
Gamma |- t2 \in (List T1) ->
Gamma |- (tcons t1 t2) \in (List T1)
| T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
Gamma |- t1 \in (List T1) ->
Gamma |- t2 \in T2 ->
(update (update Gamma x2 (List T1)) x1 T1) |- t3 \in T2 ->
Gamma |- (tlcase t1 t2 x1 x2 t3) \in T2

| T_Unit : forall Gamma,
Gamma |- unit \in Unit










where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.


Definition manual_grade_for_extensions_definition : option (nat*string) := None.







Module Examples.






Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".



Hint Extern 2 (has_type _ (app _ _) _) =>
eapply T_App; auto.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
eapply T_Lcase; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.




Module Numtest.


Definition test :=
test0
(prd
(scc
(prd
(mlt
(const 2)
(const 0)))))
(const 5)
(const 6).

Example typechecks :
empty |- test \in Nat.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Numtest.typechecks".
unfold test.

auto 10.
Admitted.

Example numtest_reduces :
test -->* const 5.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Numtest.numtest_reduces".

Admitted.

End Numtest.




Module Prodtest.


Definition test :=
snd
(fst
(pair
(pair
(const 5)
(const 6))
(const 7))).

Example typechecks :
empty |- test \in Nat.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Prodtest.typechecks". unfold test. eauto 15.  Admitted.


Example reduces :
test -->* const 6.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Prodtest.reduces".

Admitted.


End Prodtest.




Module LetTest.


Definition test :=
tlet
x
(prd (const 6))
(scc (var x)).

Example typechecks :
empty |- test \in Nat.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.LetTest.typechecks". unfold test. eauto 15.  Admitted.


Example reduces :
test -->* const 6.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.LetTest.reduces".

Admitted.


End LetTest.




Module Sumtest1.



Definition test :=
tcase (tinl Nat (const 5))
x (var x)
y (var y).

Example typechecks :
empty |- test \in Nat.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Sumtest1.typechecks". unfold test. eauto 15.  Admitted.

Example reduces :
test -->* (const 5).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Sumtest1.reduces".

Admitted.

End Sumtest1.

Module Sumtest2.



Definition test :=
tlet
processSum
(abs x (Sum Nat Nat)
(tcase (var x)
n (var n)
n (test0 (var n) (const 1) (const 0))))
(pair
(app (var processSum) (tinl Nat (const 5)))
(app (var processSum) (tinr Nat (const 5)))).

Example typechecks :
empty |- test \in (Prod Nat Nat).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Sumtest2.typechecks". unfold test. eauto 15.  Admitted.

Example reduces :
test -->* (pair (const 5) (const 0)).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.Sumtest2.reduces".

Admitted.

End Sumtest2.




Module ListTest.



Definition test :=
tlet l
(tcons (const 5) (tcons (const 6) (tnil Nat)))
(tlcase (var l)
(const 0)
x y (mlt (var x) (var x))).

Example typechecks :
empty |- test \in Nat.
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.ListTest.typechecks". unfold test. eauto 20.  Admitted.

Example reduces :
test -->* (const 25).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.ListTest.reduces".

Admitted.

End ListTest.




Module FixTest1.


Definition fact :=
tfix
(abs f (Arrow Nat Nat)
(abs a Nat
(test0
(var a)
(const 1)
(mlt
(var a)
(app (var f) (prd (var a))))))).



Example typechecks :
empty |- fact \in (Arrow Nat Nat).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest1.typechecks". unfold fact. auto 10.  Admitted.


Example reduces :
(app fact (const 4)) -->* (const 24).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest1.reduces".

Admitted.


End FixTest1.

Module FixTest2.


Definition map :=
abs g (Arrow Nat Nat)
(tfix
(abs f (Arrow (List Nat) (List Nat))
(abs l (List Nat)
(tlcase (var l)
(tnil Nat)
a l (tcons (app (var g) (var a))
(app (var f) (var l))))))).

Example typechecks :
empty |- map \in
(Arrow (Arrow Nat Nat)
(Arrow (List Nat)
(List Nat))).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest2.typechecks". unfold map. auto 10.  Admitted.


Example reduces :
app (app map (abs a Nat (scc (var a))))
(tcons (const 1) (tcons (const 2) (tnil Nat)))
-->* (tcons (const 2) (tcons (const 3) (tnil Nat))).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest2.reduces".

Admitted.


End FixTest2.

Module FixTest3.



Definition equal :=
tfix
(abs eq (Arrow Nat (Arrow Nat Nat))
(abs m Nat
(abs n Nat
(test0 (var m)
(test0 (var n) (const 1) (const 0))
(test0 (var n)
(const 0)
(app (app (var eq)
(prd (var m)))
(prd (var n)))))))).

Example typechecks :
empty |- equal \in (Arrow Nat (Arrow Nat Nat)).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest3.typechecks". unfold equal. auto 10.  Admitted.


Example reduces :
(app (app equal (const 4)) (const 4)) -->* (const 1).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest3.reduces".

Admitted.


Example reduces2 :
(app (app equal (const 4)) (const 5)) -->* (const 0).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest3.reduces2".

Admitted.

End FixTest3.

Module FixTest4.



Definition eotest :=
tlet evenodd
(tfix
(abs eo (Prod (Arrow Nat Nat) (Arrow Nat Nat))
(pair
(abs n Nat
(test0 (var n)
(const 1)
(app (snd (var eo)) (prd (var n)))))
(abs n Nat
(test0 (var n)
(const 0)
(app (fst (var eo)) (prd (var n))))))))
(tlet even (fst (var evenodd))
(tlet odd (snd (var evenodd))
(pair
(app (var even) (const 3))
(app (var even) (const 4))))).

Example typechecks :
empty |- eotest \in (Prod Nat Nat).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest4.typechecks". unfold eotest. eauto 30.  Admitted.


Example reduces :
eotest -->* (pair (const 0) (const 1)).
Proof. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.Examples.FixTest4.reduces".

Admitted.


End FixTest4.

End Examples.












Theorem progress : forall t T,
empty |- t \in T ->
value t \/ exists t', t --> t'.
Proof with eauto. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.progress".
intros t T Ht.
remember empty as Gamma.
generalize dependent HeqGamma.
induction Ht; intros HeqGamma; subst.
-

inversion H.
-

left...
-

right.
destruct IHHt1; subst...
+
destruct IHHt2; subst...
*

inversion H; subst; try solve_by_invert.
exists (subst x t2 t12)...
*

inversion H0 as [t2' Hstp]. exists (app t1 t2')...
+

inversion H as [t1' Hstp]. exists (app t1' t2)...
-
left...
-
right.
destruct IHHt...
+
inversion H; subst; try solve_by_invert.
exists (const (S n1))...
+
inversion H as [t1' Hstp].
exists (scc t1')...
-
right.
destruct IHHt...
+
inversion H; subst; try solve_by_invert.
exists (const (pred n1))...
+
inversion H as [t1' Hstp].
exists (prd t1')...
-
right.
destruct IHHt1...
+
destruct IHHt2...
*
inversion H; subst; try solve_by_invert.
inversion H0; subst; try solve_by_invert.
exists (const (mult n1 n0))...
*
inversion H0 as [t2' Hstp].
exists (mlt t1 t2')...
+
inversion H as [t1' Hstp].
exists (mlt t1' t2)...
-
right.
destruct IHHt1...
+
inversion H; subst; try solve_by_invert.
destruct n1 as [|n1'].
*
exists t2...
*
exists t3...
+
inversion H as [t1' H0].
exists (test0 t1' t2 t3)...
-
destruct IHHt...
+
right. inversion H as [t1' Hstp]...

-
destruct IHHt...
+
right. inversion H as [t1' Hstp]...

-
right.
destruct IHHt1...
+
inversion H; subst; try solve_by_invert.
*
exists ([x1:=v]t1)...
*
exists ([x2:=v]t2)...
+
inversion H as [t0' Hstp].
exists (tcase t0' x1 t1 x2 t2)...
-
left...
-
destruct IHHt1...
+
destruct IHHt2...
*
right. inversion H0 as [t2' Hstp].
exists (tcons t1 t2')...
+
right. inversion H as [t1' Hstp].
exists (tcons t1' t2)...
-
right.
destruct IHHt1...
+
inversion H; subst; try solve_by_invert.
*
exists t2...
*
exists ([x2:=vl]([x1:=v1]t3))...
+
inversion H as [t1' Hstp].
exists (tlcase t1' t2 x1 x2 t3)...
-
left...









Admitted.


Definition manual_grade_for_progress : option (nat*string) := None.







Inductive appears_free_in : string -> tm -> Prop :=
| afi_var : forall x,
appears_free_in x (var x)
| afi_app1 : forall x t1 t2,
appears_free_in x t1 -> appears_free_in x (app t1 t2)
| afi_app2 : forall x t1 t2,
appears_free_in x t2 -> appears_free_in x (app t1 t2)
| afi_abs : forall x y T11 t12,
y <> x  ->
appears_free_in x t12 ->
appears_free_in x (abs y T11 t12)

| afi_succ : forall x t,
appears_free_in x t ->
appears_free_in x (scc t)
| afi_pred : forall x t,
appears_free_in x t ->
appears_free_in x (prd t)
| afi_mult1 : forall x t1 t2,
appears_free_in x t1 ->
appears_free_in x (mlt t1 t2)
| afi_mult2 : forall x t1 t2,
appears_free_in x t2 ->
appears_free_in x (mlt t1 t2)
| afi_test01 : forall x t1 t2 t3,
appears_free_in x t1 ->
appears_free_in x (test0 t1 t2 t3)
| afi_test02 : forall x t1 t2 t3,
appears_free_in x t2 ->
appears_free_in x (test0 t1 t2 t3)
| afi_test03 : forall x t1 t2 t3,
appears_free_in x t3 ->
appears_free_in x (test0 t1 t2 t3)

| afi_inl : forall x t T,
appears_free_in x t ->
appears_free_in x (tinl T t)
| afi_inr : forall x t T,
appears_free_in x t ->
appears_free_in x (tinr T t)
| afi_case0 : forall x t0 x1 t1 x2 t2,
appears_free_in x t0 ->
appears_free_in x (tcase t0 x1 t1 x2 t2)
| afi_case1 : forall x t0 x1 t1 x2 t2,
x1 <> x ->
appears_free_in x t1 ->
appears_free_in x (tcase t0 x1 t1 x2 t2)
| afi_case2 : forall x t0 x1 t1 x2 t2,
x2 <> x ->
appears_free_in x t2 ->
appears_free_in x (tcase t0 x1 t1 x2 t2)

| afi_cons1 : forall x t1 t2,
appears_free_in x t1 ->
appears_free_in x (tcons t1 t2)
| afi_cons2 : forall x t1 t2,
appears_free_in x t2 ->
appears_free_in x (tcons t1 t2)
| afi_lcase1 : forall x t1 t2 y1 y2 t3,
appears_free_in x t1 ->
appears_free_in x (tlcase t1 t2 y1 y2 t3)
| afi_lcase2 : forall x t1 t2 y1 y2 t3,
appears_free_in x t2 ->
appears_free_in x (tlcase t1 t2 y1 y2 t3)
| afi_lcase3 : forall x t1 t2 y1 y2 t3,
y1 <> x ->
y2 <> x ->
appears_free_in x t3 ->
appears_free_in x (tlcase t1 t2 y1 y2 t3)









.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
Gamma |- t \in S  ->
(forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
Gamma' |- t \in S.

Proof with eauto 30. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.context_invariance".
intros. generalize dependent Gamma'.
induction H;
intros Gamma' Heqv...
-
apply T_Var... rewrite <- Heqv...
-
apply T_Abs... apply IHhas_type. intros y Hafi.
unfold update, t_update.
destruct (eqb_stringP x y)...
-
eapply T_Case...
+ apply IHhas_type2. intros y Hafi.
unfold update, t_update.
destruct (eqb_stringP x1 y)...
+ apply IHhas_type3. intros y Hafi.
unfold update, t_update.
destruct (eqb_stringP x2 y)...
-
eapply T_Lcase... apply IHhas_type3. intros y Hafi.
unfold update, t_update.
destruct (eqb_stringP x1 y)...
destruct (eqb_stringP x2 y)...



Admitted.

Lemma free_in_context : forall x t T Gamma,
appears_free_in x t ->
Gamma |- t \in T ->
exists T', Gamma x = Some T'.
Proof with eauto. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.free_in_context".
intros x t T Gamma Hafi Htyp.
induction Htyp; inversion Hafi; subst...
-
destruct IHHtyp as [T' Hctx]... exists T'.
unfold update, t_update in Hctx.
rewrite false_eqb_string in Hctx...

-
destruct IHHtyp2 as [T' Hctx]... exists T'.
unfold update, t_update in Hctx.
rewrite false_eqb_string in Hctx...
-
destruct IHHtyp3 as [T' Hctx]... exists T'.
unfold update, t_update in Hctx.
rewrite false_eqb_string in Hctx...
-
clear Htyp1 IHHtyp1 Htyp2 IHHtyp2.
destruct IHHtyp3 as [T' Hctx]... exists T'.
unfold update, t_update in Hctx.
rewrite false_eqb_string in Hctx...
rewrite false_eqb_string in Hctx...



Admitted.


Definition manual_grade_for_context_invariance : option (nat*string) := None.







Lemma substitution_preserves_typing : forall Gamma x U v t S,
(update Gamma x U) |- t \in S  ->
empty |- v \in U   ->
Gamma |- ([x:=v]t) \in S.
Proof with eauto. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.substitution_preserves_typing".

intros Gamma x U v t S Htypt Htypv.
generalize dependent Gamma. generalize dependent S.

induction t;
intros S Gamma Htypt; simpl; inversion Htypt; subst...
-
simpl. rename s into y.

unfold update, t_update in H1.
destruct (eqb_stringP x y).
+

subst.
inversion H1; subst. clear H1.
eapply context_invariance...
intros x Hcontra.
destruct (free_in_context _ _ S empty Hcontra)
as [T' HT']...
inversion HT'.
+

apply T_Var...
-
rename s into y. rename t into T11.

apply T_Abs...
destruct (eqb_stringP x y) as [Hxy|Hxy].
+

eapply context_invariance...
subst.
intros x Hafi. unfold update, t_update.
destruct (eqb_string y x)...
+

apply IHt. eapply context_invariance...
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y z) as [Hyz|Hyz]...
subst.
rewrite false_eqb_string...
-
rename s into x1. rename s0 into x2.
eapply T_Case...
+
destruct (eqb_stringP x x1) as [Hxx1|Hxx1].
*
eapply context_invariance...
subst.
intros z Hafi. unfold update, t_update.
destruct (eqb_string x1 z)...
*
apply IHt2. eapply context_invariance...
intros z Hafi.  unfold update, t_update.
destruct (eqb_stringP x1 z) as [Hx1z|Hx1z]...
subst. rewrite false_eqb_string...
+
destruct (eqb_stringP x x2) as [Hxx2|Hxx2].
*
eapply context_invariance...
subst.
intros z Hafi. unfold update, t_update.
destruct (eqb_string x2 z)...
*
apply IHt3. eapply context_invariance...
intros z Hafi.  unfold update, t_update.
destruct (eqb_stringP x2 z)...
subst. rewrite false_eqb_string...
-
rename s into y1. rename s0 into y2.
eapply T_Lcase...
destruct (eqb_stringP x y1).
+
simpl.
eapply context_invariance...
subst.
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y1 z)...
+
destruct (eqb_stringP x y2).
*
eapply context_invariance...
subst.
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y2 z)...
*
apply IHt3. eapply context_invariance...
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y1 z)...
subst. rewrite false_eqb_string...
destruct (eqb_stringP y2 z)...
subst. rewrite false_eqb_string...



Admitted.


Definition manual_grade_for_substitution_preserves_typing : option (nat*string) := None.







Theorem preservation : forall t t' T,
empty |- t \in T  ->
t --> t'  ->
empty |- t' \in T.
Proof with eauto. hammer_hook "MoreStlc" "MoreStlc.STLCExtended.preservation".
intros t t' T HT.

remember empty as Gamma. generalize dependent HeqGamma.
generalize dependent t'.

induction HT;
intros t' HeqGamma HE; subst; inversion HE; subst...
-

inversion HE; subst...
+

apply substitution_preserves_typing with T1...
inversion HT1...

-
inversion HT1; subst.
eapply substitution_preserves_typing...
-
inversion HT1; subst.
eapply substitution_preserves_typing...
-
+
inversion HT1; subst.
apply substitution_preserves_typing with (List T1)...
apply substitution_preserves_typing with T1...









Admitted.


Definition manual_grade_for_preservation : option (nat*string) := None.


End STLCExtended.


