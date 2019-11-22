From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Module STLCProp.
Import STLC.








Lemma canonical_forms_bool : forall t,
empty |- t \in Bool ->
value t ->
(t = tru) \/ (t = fls).
Proof. hammer_hook "StlcProp" "StlcProp.STLCProp.canonical_forms_bool".
intros t HT HVal.
inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
empty |- t \in (Arrow T1 T2) ->
value t ->
exists x u, t = abs x T1 u.
Proof. hammer_hook "StlcProp" "StlcProp.STLCProp.canonical_forms_fun".
intros t T1 T2 HT HVal.
inversion HVal; intros; subst; try inversion HT; subst; auto.
exists x0, t0.  auto.
Qed.






Theorem progress : forall t T,
empty |- t \in T ->
value t \/ exists t', t --> t'.


Proof with eauto. hammer_hook "StlcProp" "StlcProp.STLCProp.progress".
intros t T Ht.
remember (@empty ty) as Gamma.
induction Ht; subst Gamma...
-

inversion H.

-

right. destruct IHHt1...
+
destruct IHHt2...
*
assert (exists x0 t0, t1 = abs x0 T11 t0).
eapply canonical_forms_fun; eauto.
destruct H1 as [x0 [t0 Heq]]. subst.
exists ([x0:=t2]t0)...

*
inversion H0 as [t2' Hstp]. exists (app t1 t2')...

+
inversion H as [t1' Hstp]. exists (app t1' t2)...

-
right. destruct IHHt1...

+
destruct (canonical_forms_bool t1); subst; eauto.

+
inversion H as [t1' Hstp]. exists (test t1' t2 t3)...
Qed.



Theorem progress' : forall t T,
empty |- t \in T ->
value t \/ exists t', t --> t'.
Proof. hammer_hook "StlcProp" "StlcProp.STLCProp.progress'".
intros t.
induction t; intros T Ht; auto.
Admitted.












Inductive appears_free_in : string -> tm -> Prop :=
| afi_var : forall x,
appears_free_in x (var x)
| afi_app1 : forall x t1 t2,
appears_free_in x t1 ->
appears_free_in x (app t1 t2)
| afi_app2 : forall x t1 t2,
appears_free_in x t2 ->
appears_free_in x (app t1 t2)
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
appears_free_in x (test t1 t2 t3).

Hint Constructors appears_free_in.



Definition closed (t:tm) :=
forall x, ~ appears_free_in x t.








Definition manual_grade_for_afi : option (nat*string) := None.







Lemma free_in_context : forall x t T Gamma,
appears_free_in x t ->
Gamma |- t \in T ->
exists T', Gamma x = Some T'.



Proof. hammer_hook "StlcProp" "StlcProp.STLCProp.free_in_context".
intros x t T Gamma H H0. generalize dependent Gamma.
generalize dependent T.
induction H;
intros; try solve [inversion H0; eauto].
-
inversion H1; subst.
apply IHappears_free_in in H7.
rewrite update_neq in H7; assumption.
Qed.




Corollary typable_empty__closed : forall t T,
empty |- t \in T  ->
closed t.
Proof. hammer_hook "StlcProp" "StlcProp.STLCProp.typable_empty__closed".
Admitted.




Lemma context_invariance : forall Gamma Gamma' t T,
Gamma |- t \in T  ->
(forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
Gamma' |- t \in T.



Proof with eauto. hammer_hook "StlcProp" "StlcProp.STLCProp.context_invariance".
intros.
generalize dependent Gamma'.
induction H; intros; auto.
-
apply T_Var. rewrite <- H0...
-
apply T_Abs.
apply IHhas_type. intros x1 Hafi.

unfold update. unfold t_update. destruct (eqb_string x0 x1) eqn: Hx0x1...
rewrite eqb_string_false_iff in Hx0x1. auto.
-
apply T_App with T11...
Qed.







Lemma substitution_preserves_typing : forall Gamma x U t v T,
(x |-> U ; Gamma) |- t \in T ->
empty |- v \in U   ->
Gamma |- [x:=v]t \in T.



Proof with eauto. hammer_hook "StlcProp" "StlcProp.STLCProp.substitution_preserves_typing".
intros Gamma x U t v T Ht Ht'.
generalize dependent Gamma. generalize dependent T.
induction t; intros T Gamma H;

inversion H; subst; simpl...
-
rename s into y. destruct (eqb_stringP x y) as [Hxy|Hxy].
+
subst.
rewrite update_eq in H2.
inversion H2; subst.
eapply context_invariance. eassumption.
apply typable_empty__closed in Ht'. unfold closed in Ht'.
intros.  apply (Ht' x0) in H0. inversion H0.
+
apply T_Var. rewrite update_neq in H2...
-
rename s into y. rename t into T. apply T_Abs.
destruct (eqb_stringP x y) as [Hxy | Hxy].
+
subst. rewrite update_shadow in H5. apply H5.
+
apply IHt. eapply context_invariance...
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y z) as [Hyz | Hyz]; subst; trivial.
rewrite <- eqb_string_false_iff in Hxy.
rewrite Hxy...
Qed.






Theorem preservation : forall t t' T,
empty |- t \in T  ->
t --> t'  ->
empty |- t' \in T.



Proof with eauto. hammer_hook "StlcProp" "StlcProp.STLCProp.preservation".
remember (@empty ty) as Gamma.
intros t t' T HT. generalize dependent t'.
induction HT;
intros t' HE; subst Gamma; subst;
try solve [inversion HE; subst; auto].
-
inversion HE; subst...

+
apply substitution_preserves_typing with T11...
inversion HT1...
Qed.






Definition manual_grade_for_subject_expansion_stlc : option (nat*string) := None.







Definition stuck (t:tm) : Prop :=
(normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
empty |- t \in T ->
t -->* t' ->
~(stuck t').
Proof. hammer_hook "StlcProp" "StlcProp.STLCProp.soundness".
intros t t' T Hhas_type Hmulti. unfold stuck.
intros [Hnf Hnot_val]. unfold normal_form in Hnf.
induction Hmulti.
Admitted.







Theorem unique_types : forall Gamma e T T',
Gamma |- e \in T ->
Gamma |- e \in T' ->
T = T'.
Proof. hammer_hook "StlcProp" "StlcProp.STLCProp.unique_types".
Admitted.









Definition manual_grade_for_progress_preservation_statement : option (nat*string) := None.





Definition manual_grade_for_stlc_variation1 : option (nat*string) := None.





Definition manual_grade_for_stlc_variation2 : option (nat*string) := None.





Definition manual_grade_for_stlc_variation3 : option (nat*string) := None.










End STLCProp.






Module STLCArith.
Import STLC.



Inductive ty : Type :=
| Arrow : ty -> ty -> ty
| Nat  : ty.



Inductive tm : Type :=
| var : string -> tm
| app : tm -> tm -> tm
| abs : string -> ty -> tm -> tm
| const  : nat -> tm
| scc : tm -> tm
| prd : tm -> tm
| mlt : tm -> tm -> tm
| test0 : tm -> tm -> tm -> tm.






Definition manual_grade_for_stlc_arith : option (nat*string) := None.


End STLCArith.


