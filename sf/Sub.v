From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.







































































Definition manual_grade_for_arrow_sub_wrong : option (nat*string) := None.




















Definition manual_grade_for_subtype_order : option (nat*string) := None.





Definition manual_grade_for_subtype_instances_tf_2 : option (nat*string) := None.





Definition manual_grade_for_subtype_concepts_tf : option (nat*string) := None.





Definition manual_grade_for_proper_subtypes : option (nat*string) := None.





Definition manual_grade_for_small_large_1 : option (nat*string) := None.





Definition manual_grade_for_small_large_2 : option (nat*string) := None.







Definition manual_grade_for_small_large_4 : option (nat*string) := None.





Definition manual_grade_for_smallest_1 : option (nat*string) := None.





Definition manual_grade_for_smallest_2 : option (nat*string) := None.







Definition manual_grade_for_pair_permutation : option (nat*string) := None.















Inductive ty : Type :=
| Top   : ty
| Bool  : ty
| Base  : string -> ty
| Arrow : ty -> ty -> ty
| Unit  : ty
.

Inductive tm : Type :=
| var : string -> tm
| app : tm -> tm -> tm
| abs : string -> ty -> tm -> tm
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm
| unit : tm
.






Fixpoint subst (x:string) (s:tm)  (t:tm) : tm :=
match t with
| var y =>
if eqb_string x y then s else t
| abs y T t1 =>
abs y T (if eqb_string x y then t1 else (subst x s t1))
| app t1 t2 =>
app (subst x s t1) (subst x s t2)
| tru =>
tru
| fls =>
fls
| test t1 t2 t3 =>
test (subst x s t1) (subst x s t2) (subst x s t3)
| unit =>
unit
end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).






Inductive value : tm -> Prop :=
| v_abs : forall x T t,
value (abs x T t)
| v_true :
value tru
| v_false :
value fls
| v_unit :
value unit
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T t12 v2,
value v2 ->
(app (abs x T t12) v2) --> [x:=v2]t12
| ST_App1 : forall t1 t1' t2,
t1 --> t1' ->
(app t1 t2) --> (app t1' t2)
| ST_App2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
(app v1 t2) --> (app v1  t2')
| ST_TestTrue : forall t1 t2,
(test tru t1 t2) --> t1
| ST_TestFalse : forall t1 t2,
(test fls t1 t2) --> t2
| ST_Test : forall t1 t1' t2 t3,
t1 --> t1' ->
(test t1 t2 t3) --> (test t1' t2 t3)
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.








Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
| S_Refl : forall T,
T <: T
| S_Trans : forall S U T,
S <: U ->
U <: T ->
S <: T
| S_Top : forall S,
S <: Top
| S_Arrow : forall S1 S2 T1 T2,
T1 <: S1 ->
S2 <: T2 ->
(Arrow S1 S2) <: (Arrow T1 T2)
where "T '<:' U" := (subtype T U).



Hint Constructors subtype.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := (Base "A").
Notation B := (Base "B").
Notation C := (Base "C").

Notation String := (Base "String").
Notation Float := (Base "Float").
Notation Integer := (Base "Integer").

Example subtyping_example_0 :
(Arrow C Bool) <: (Arrow C Top).

Proof. hammer_hook "Sub" "Sub.Examples.subtyping_example_0". auto. Qed.


Definition Person : ty
. Admitted.
Definition Student : ty
. Admitted.
Definition Employee : ty
. Admitted.



Example sub_student_person :
Student <: Person.
Proof. hammer_hook "Sub" "Sub.Examples.sub_student_person".
Admitted.

Example sub_employee_person :
Employee <: Person.
Proof. hammer_hook "Sub" "Sub.Examples.sub_employee_person".
Admitted.





Example subtyping_example_1 :
(Arrow Top Student) <: (Arrow (Arrow C C) Person).

Proof with eauto. hammer_hook "Sub" "Sub.Examples.subtyping_example_1".
Admitted.



Example subtyping_example_2 :
(Arrow Top Person) <: (Arrow Person Top).

Proof with eauto. hammer_hook "Sub" "Sub.Examples.subtyping_example_2".
Admitted.


End Examples.






Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=

| T_Var : forall Gamma x T,
Gamma x = Some T ->
Gamma |- var x \in T
| T_Abs : forall Gamma x T11 T12 t12,
(x |-> T11 ; Gamma) |- t12 \in T12 ->
Gamma |- abs x T11 t12 \in Arrow T11 T12
| T_App : forall T1 T2 Gamma t1 t2,
Gamma |- t1 \in Arrow T1 T2 ->
Gamma |- t2 \in T1 ->
Gamma |- app t1 t2 \in T2
| T_True : forall Gamma,
Gamma |- tru \in Bool
| T_False : forall Gamma,
Gamma |- fls \in Bool
| T_Test : forall t1 t2 t3 T Gamma,
Gamma |- t1 \in Bool ->
Gamma |- t2 \in T ->
Gamma |- t3 \in T ->
Gamma |- test t1 t2 t3 \in T
| T_Unit : forall Gamma,
Gamma |- unit \in Unit

| T_Sub : forall Gamma t S T,
Gamma |- t \in S ->
S <: T ->
Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.



Hint Extern 2 (has_type _ (app _ _) _) =>
eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

Module Examples2.
Import Examples.















End Examples2.














Lemma sub_inversion_Bool : forall U,
U <: Bool ->
U = Bool.
Proof with auto. hammer_hook "Sub" "Sub.sub_inversion_Bool".
intros U Hs.
remember Bool as V.
Admitted.



Lemma sub_inversion_arrow : forall U V1 V2,
U <: Arrow V1 V2 ->
exists U1 U2,
U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto. hammer_hook "Sub" "Sub.sub_inversion_arrow".
intros U V1 V2 Hs.
remember (Arrow V1 V2) as V.
generalize dependent V2. generalize dependent V1.
Admitted.








Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
Gamma |- s \in Arrow T1 T2 ->
value s ->
exists x S1 s2,
s = abs x S1 s2.
Proof with eauto. hammer_hook "Sub" "Sub.canonical_forms_of_arrow_types".
Admitted.




Lemma canonical_forms_of_Bool : forall Gamma s,
Gamma |- s \in Bool ->
value s ->
s = tru \/ s = fls.
Proof with eauto. hammer_hook "Sub" "Sub.canonical_forms_of_Bool".
intros Gamma s Hty Hv.
remember Bool as T.
induction Hty; try solve_by_invert...
-
subst. apply sub_inversion_Bool in H. subst...
Qed.








Theorem progress : forall t T,
empty |- t \in T ->
value t \/ exists t', t --> t'.
Proof with eauto. hammer_hook "Sub" "Sub.progress".
intros t T Ht.
remember empty as Gamma.
revert HeqGamma.
induction Ht;
intros HeqGamma; subst...
-
inversion H.
-
right.
destruct IHHt1; subst...
+
destruct IHHt2; subst...
*
destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
as [x [S1 [t12 Heqt1]]]...
subst. exists ([x:=t2]t12)...
*
inversion H0 as [t2' Hstp]. exists (app t1 t2')...
+
inversion H as [t1' Hstp]. exists (app t1' t2)...
-
right.
destruct IHHt1.
+  eauto.
+ assert (t1 = tru \/ t1 = fls)
by (eapply canonical_forms_of_Bool; eauto).
inversion H0; subst...
+ inversion H. rename x into t1'. eauto.
Qed.








Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
Gamma |- (abs x S1 t2) \in T ->
exists S2,
Arrow S1 S2 <: T
/\ (x |-> S1 ; Gamma) |- t2 \in S2.
Proof with eauto. hammer_hook "Sub" "Sub.typing_inversion_abs".
intros Gamma x S1 t2 T H.
remember (abs x S1 t2) as t.
induction H;
inversion Heqt; subst; intros; try solve_by_invert.
-
exists T12...
-
destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.



Lemma typing_inversion_var : forall Gamma x T,
Gamma |- (var x) \in T ->
exists S,
Gamma x = Some S /\ S <: T.
Proof with eauto. hammer_hook "Sub" "Sub.typing_inversion_var".
intros Gamma x T Hty.
remember (var x) as t.
induction Hty; intros;
inversion Heqt; subst; try solve_by_invert.
-
exists T...
-
destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
Gamma |- (app t1 t2) \in T2 ->
exists T1,
Gamma |- t1 \in (Arrow T1 T2) /\
Gamma |- t2 \in T1.
Proof with eauto. hammer_hook "Sub" "Sub.typing_inversion_app".
intros Gamma t1 t2 T2 Hty.
remember (app t1 t2) as t.
induction Hty; intros;
inversion Heqt; subst; try solve_by_invert.
-
exists T1...
-
destruct IHHty as [U1 [Hty1 Hty2]]...
Qed.

Lemma typing_inversion_true : forall Gamma T,
Gamma |- tru \in T ->
Bool <: T.
Proof with eauto. hammer_hook "Sub" "Sub.typing_inversion_true".
intros Gamma T Htyp. remember tru as tu.
induction Htyp;
inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false : forall Gamma T,
Gamma |- fls \in T ->
Bool <: T.
Proof with eauto. hammer_hook "Sub" "Sub.typing_inversion_false".
intros Gamma T Htyp. remember fls as tu.
induction Htyp;
inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
Gamma |- (test t1 t2 t3) \in T ->
Gamma |- t1 \in Bool
/\ Gamma |- t2 \in T
/\ Gamma |- t3 \in T.
Proof with eauto. hammer_hook "Sub" "Sub.typing_inversion_if".
intros Gamma t1 t2 t3 T Hty.
remember (test t1 t2 t3) as t.
induction Hty; intros;
inversion Heqt; subst; try solve_by_invert.
-
auto.
-
destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.

Lemma typing_inversion_unit : forall Gamma T,
Gamma |- unit \in T ->
Unit <: T.
Proof with eauto. hammer_hook "Sub" "Sub.typing_inversion_unit".
intros Gamma T Htyp. remember unit as tu.
induction Htyp;
inversion Heqtu; subst; intros...
Qed.



Lemma abs_arrow : forall x S1 s2 T1 T2,
empty |- (abs x S1 s2) \in (Arrow T1 T2) ->
T1 <: S1
/\ (x |-> S1 ; empty) |- s2 \in T2.
Proof with eauto. hammer_hook "Sub" "Sub.abs_arrow".
intros x S1 s2 T1 T2 Hty.
apply typing_inversion_abs in Hty.
inversion Hty as [S2 [Hsub Hty1]].
apply sub_inversion_arrow in Hsub.
inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
inversion Heq; subst...  Qed.






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
| afi_test1 : forall x t1 t2 t3,
appears_free_in x t1 ->
appears_free_in x (test t1 t2 t3)
| afi_test2 : forall x t1 t2 t3,
appears_free_in x t2 ->
appears_free_in x (test t1 t2 t3)
| afi_test3 : forall x t1 t2 t3,
appears_free_in x t3 ->
appears_free_in x (test t1 t2 t3)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
Gamma |- t \in S  ->
(forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
Gamma' |- t \in S.
Proof with eauto. hammer_hook "Sub" "Sub.context_invariance".
intros. generalize dependent Gamma'.
induction H;
intros Gamma' Heqv...
-
apply T_Var... rewrite <- Heqv...
-
apply T_Abs... apply IHhas_type. intros x0 Hafi.
unfold update, t_update. destruct (eqb_stringP x x0)...
-
apply T_Test...
Qed.

Lemma free_in_context : forall x t T Gamma,
appears_free_in x t ->
Gamma |- t \in T ->
exists T', Gamma x = Some T'.
Proof with eauto. hammer_hook "Sub" "Sub.free_in_context".
intros x t T Gamma Hafi Htyp.
induction Htyp;
subst; inversion Hafi; subst...
-
destruct (IHHtyp H4) as [T Hctx]. exists T.
unfold update, t_update in Hctx.
rewrite <- eqb_string_false_iff in H2.
rewrite H2 in Hctx... Qed.






Lemma substitution_preserves_typing : forall Gamma x U v t S,
(x |-> U ; Gamma) |- t \in S  ->
empty |- v \in U   ->
Gamma |- [x:=v]t \in S.
Proof with eauto. hammer_hook "Sub" "Sub.substitution_preserves_typing".
intros Gamma x U v t S Htypt Htypv.
generalize dependent S. generalize dependent Gamma.
induction t; intros; simpl.
-
rename s into y.
destruct (typing_inversion_var _ _ _ Htypt)
as [T [Hctx Hsub]].
unfold update, t_update in Hctx.
destruct (eqb_stringP x y) as [Hxy|Hxy]; eauto;
subst.
inversion Hctx; subst. clear Hctx.
apply context_invariance with empty...
intros x Hcontra.
destruct (free_in_context _ _ S empty Hcontra)
as [T' HT']...
inversion HT'.
-
destruct (typing_inversion_app _ _ _ _ Htypt)
as [T1 [Htypt1 Htypt2]].
eapply T_App...
-
rename s into y. rename t into T1.
destruct (typing_inversion_abs _ _ _ _ _ Htypt)
as [T2 [Hsub Htypt2]].
apply T_Sub with (Arrow T1 T2)... apply T_Abs...
destruct (eqb_stringP x y) as [Hxy|Hxy].
+
eapply context_invariance...
subst.
intros x Hafi. unfold update, t_update.
destruct (eqb_string y x)...
+
apply IHt. eapply context_invariance...
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y z)...
subst.
rewrite <- eqb_string_false_iff in Hxy. rewrite Hxy...
-
assert (Bool <: S)
by apply (typing_inversion_true _ _  Htypt)...
-
assert (Bool <: S)
by apply (typing_inversion_false _ _  Htypt)...
-
assert  ((x |-> U ; Gamma) |- t1 \in Bool
/\  (x |-> U ; Gamma) |- t2 \in S
/\  (x |-> U ; Gamma) |- t3 \in S)
by apply (typing_inversion_if _ _ _ _ _ Htypt).
inversion H as [H1 [H2 H3]].
apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
auto.
-
assert (Unit <: S)
by apply (typing_inversion_unit _ _  Htypt)...
Qed.








Theorem preservation : forall t t' T,
empty |- t \in T  ->
t --> t'  ->
empty |- t' \in T.
Proof with eauto. hammer_hook "Sub" "Sub.preservation".
intros t t' T HT.
remember empty as Gamma. generalize dependent HeqGamma.
generalize dependent t'.
induction HT;
intros t' HeqGamma HE; subst; inversion HE; subst...
-
inversion HE; subst...
+
destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
apply substitution_preserves_typing with T...
Qed.












Definition manual_grade_for_variations : option (nat*string) := None.










Definition manual_grade_for_products : option (nat*string) := None.



