From Hammer Require Import Hammer.





Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.

Hint Constructors multi.











Inductive tm : Type :=
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm
| zro : tm
| scc : tm -> tm
| prd : tm -> tm
| iszro : tm -> tm.



Inductive bvalue : tm -> Prop :=
| bv_tru : bvalue tru
| bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
| nv_zro : nvalue zro
| nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold update.








Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_TestTru : forall t1 t2,
(test tru t1 t2) --> t1
| ST_TestFls : forall t1 t2,
(test fls t1 t2) --> t2
| ST_Test : forall t1 t1' t2 t3,
t1 --> t1' ->
(test t1 t2 t3) --> (test t1' t2 t3)
| ST_Scc : forall t1 t1',
t1 --> t1' ->
(scc t1) --> (scc t1')
| ST_PrdZro :
(prd zro) --> zro
| ST_PrdScc : forall t1,
nvalue t1 ->
(prd (scc t1)) --> t1
| ST_Prd : forall t1 t1',
t1 --> t1' ->
(prd t1) --> (prd t1')
| ST_IszroZro :
(iszro zro) --> tru
| ST_IszroScc : forall t1,
nvalue t1 ->
(iszro (scc t1)) --> fls
| ST_Iszro : forall t1 t1',
t1 --> t1' ->
(iszro t1) --> (iszro t1')

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.








Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
step_normal_form t /\ ~ value t.

Hint Unfold stuck.


Example some_term_is_stuck :
exists t, stuck t.
Proof. hammer_hook "Types" "Types.some_term_is_stuck".
Admitted.





Lemma value_is_nf : forall t,
value t -> step_normal_form t.
Proof. hammer_hook "Types" "Types.value_is_nf".
Admitted.





Theorem step_deterministic:
deterministic step.
Proof with eauto. hammer_hook "Types" "Types.step_deterministic".
Admitted.







Inductive ty : Type :=
| Bool : ty
| Nat : ty.



Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
| T_Tru :
|- tru \in Bool
| T_Fls :
|- fls \in Bool
| T_Test : forall t1 t2 t3 T,
|- t1 \in Bool ->
|- t2 \in T ->
|- t3 \in T ->
|- test t1 t2 t3 \in T
| T_Zro :
|- zro \in Nat
| T_Scc : forall t1,
|- t1 \in Nat ->
|- scc t1 \in Nat
| T_Prd : forall t1,
|- t1 \in Nat ->
|- prd t1 \in Nat
| T_Iszro : forall t1,
|- t1 \in Nat ->
|- iszro t1 \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
|- test fls zro (scc zro) \in Nat.
Proof. hammer_hook "Types" "Types.has_type_1".
apply T_Test.
- apply T_Fls.
- apply T_Zro.
- apply T_Scc.
+ apply T_Zro.
Qed.





Example has_type_not :
~ ( |- test fls zro tru \in Bool ).
Proof. hammer_hook "Types" "Types.has_type_not".
intros Contra. solve_by_inverts 2.  Qed.


Example scc_hastype_nat__hastype_nat : forall t,
|- scc t \in Nat ->
|- t \in Nat.
Proof. hammer_hook "Types" "Types.scc_hastype_nat__hastype_nat".
Admitted.







Lemma bool_canonical : forall t,
|- t \in Bool -> value t -> bvalue t.
Proof. hammer_hook "Types" "Types.bool_canonical".
intros t HT [Hb | Hn].
- assumption.
- induction Hn; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
|- t \in Nat -> value t -> nvalue t.
Proof. hammer_hook "Types" "Types.nat_canonical".
intros t HT [Hb | Hn].
- inversion Hb; subst; inversion HT.
- assumption.
Qed.







Theorem progress : forall t T,
|- t \in T ->
value t \/ exists t', t --> t'.


Proof with auto. hammer_hook "Types" "Types.progress".
intros t T HT.
induction HT...

-
right. inversion IHHT1; clear IHHT1.
+
apply (bool_canonical t1 HT1) in H.
inversion H; subst; clear H.
exists t2...
exists t3...
+
inversion H as [t1' H1].
exists (test t1' t2 t3)...
Admitted.








Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.










Theorem preservation : forall t t' T,
|- t \in T ->
t --> t' ->
|- t' \in T.



Proof with auto. hammer_hook "Types" "Types.preservation".
intros t t' T HT HE.
generalize dependent t'.
induction HT;

intros t' HE;

try solve_by_invert.
-  inversion HE; subst; clear HE.
+  assumption.
+  assumption.
+  apply T_Test; try assumption.
apply IHHT1; assumption.
Admitted.








Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.




Theorem preservation' : forall t t' T,
|- t \in T ->
t --> t' ->
|- t' \in T.
Proof with eauto. hammer_hook "Types" "Types.preservation'".
Admitted.









Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
|- t \in T ->
t -->* t' ->
~(stuck t').
Proof. hammer_hook "Types" "Types.soundness".
intros t t' T HT P. induction P; intros [R S].
destruct (progress x T HT); auto.
apply IHP.  apply (preservation x y T HT H).
unfold stuck. split; auto.   Qed.






Definition manual_grade_for_subject_expansion : option (nat*string) := None.




Definition manual_grade_for_variation1 : option (nat*string) := None.




Definition manual_grade_for_variation2 : option (nat*string) := None.















Definition manual_grade_for_remove_predzro : option (nat*string) := None.




Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.





