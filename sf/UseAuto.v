From Hammer Require Import Hammer.






From Coq Require Import Arith.Arith.

From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require Import LibTactics.

From PLF Require Imp.

From Coq Require Import Lists.List.
Import ListNotations.
















Lemma solving_by_reflexivity :
2 + 3 = 5.
Proof. hammer_hook "UseAuto" "UseAuto.solving_by_reflexivity". auto. Qed.



Lemma solving_by_apply : forall (P Q : nat->Prop),
(forall n, Q n -> P n) ->
(forall n, Q n) ->
P 2.
Proof. hammer_hook "UseAuto" "UseAuto.solving_by_apply". auto. Qed.





Lemma solving_by_eapply : forall (P Q : nat->Prop),
(forall n m, Q m -> P n) ->
Q 1 ->
P 2.
Proof. hammer_hook "UseAuto" "UseAuto.solving_by_eapply". auto. eauto. Qed.









Lemma solving_conj_goal : forall (P : nat->Prop) (F : Prop),
(forall n, P n) ->
F ->
F /\ P 2.
Proof. hammer_hook "UseAuto" "UseAuto.solving_conj_goal". auto. Qed.



Lemma solving_conj_hyp : forall (F F' : Prop),
F /\ F' ->
F.
Proof. hammer_hook "UseAuto" "UseAuto.solving_conj_hyp". auto. eauto. jauto.  Qed.



Lemma solving_conj_hyp' : forall (F F' : Prop),
F /\ F' ->
F.
Proof. hammer_hook "UseAuto" "UseAuto.solving_conj_hyp'". intros. jauto_set. eauto. Qed.



Lemma solving_conj_more : forall (P Q R : nat->Prop) (F : Prop),
(F /\ (forall n m, (Q m /\ R n) -> P n)) ->
(F -> R 2) ->
Q 1 ->
P 2 /\ F.
Proof. hammer_hook "UseAuto" "UseAuto.solving_conj_more". jauto.  Qed.



Lemma solving_conj_hyp_forall : forall (P Q : nat->Prop),
(forall n, P n /\ Q n) ->
P 2.
Proof. hammer_hook "UseAuto" "UseAuto.solving_conj_hyp_forall".
auto. eauto. iauto. jauto.

intros. destruct (H 2). auto.
Qed.



Lemma solved_by_jauto : forall (P Q : nat->Prop) (F : Prop),
(forall n, P n) /\ (forall n, Q n) ->
P 2.
Proof. hammer_hook "UseAuto" "UseAuto.solved_by_jauto". jauto.  Qed.






Lemma solving_disj_goal : forall (F F' : Prop),
F ->
F \/ F'.
Proof. hammer_hook "UseAuto" "UseAuto.solving_disj_goal". auto. Qed.



Lemma solving_disj_hyp : forall (F F' : Prop),
F \/ F' ->
F' \/ F.
Proof. hammer_hook "UseAuto" "UseAuto.solving_disj_hyp". auto. eauto. jauto. iauto. Qed.



Lemma solving_tauto : forall (F1 F2 F3 : Prop),
((~F1 /\ F3) \/ (F2 /\ ~F3)) ->
(F2 -> F1) ->
(F2 -> F3) ->
~F2.
Proof. hammer_hook "UseAuto" "UseAuto.solving_tauto". iauto. Qed.








Lemma solving_exists_goal : forall (f : nat->Prop),
f 2 ->
exists x, f x.
Proof. hammer_hook "UseAuto" "UseAuto.solving_exists_goal".
auto.
eauto.
Qed.



Lemma solving_exists_hyp : forall (f g : nat->Prop),
(forall x, f x -> g x) ->
(exists a, f a) ->
(exists a, g a).
Proof. hammer_hook "UseAuto" "UseAuto.solving_exists_hyp".
auto. eauto. iauto.
jauto.

Qed.






Lemma negation_study_1 : forall (P : nat->Prop),
P 0 ->
(forall x, ~ P x) ->
False.
Proof. hammer_hook "UseAuto" "UseAuto.negation_study_1".
intros P H0 HX.
eauto.
unfold not in *. eauto.
Qed.



Lemma negation_study_2 : forall (P : nat->Prop),
P 0 ->
(forall x, ~ P x) ->
False.
Proof. hammer_hook "UseAuto" "UseAuto.negation_study_2". jauto.  Qed.








Lemma equality_by_auto : forall (f g : nat->Prop),
(forall x, f x = g x) ->
g 2 = f 2.
Proof. hammer_hook "UseAuto" "UseAuto.equality_by_auto". auto. Qed.











Lemma search_depth_0 :
True /\ True /\ True /\ True /\ True /\ True.
Proof. hammer_hook "UseAuto" "UseAuto.search_depth_0".
auto.
Abort.





Lemma search_depth_1 : forall (P : nat->Prop),
P 0 ->
(P 0 -> P 1) ->
(P 1 -> P 2) ->
(P 2).
Proof. hammer_hook "UseAuto" "UseAuto.search_depth_1".
auto 0.
auto 1.
auto 2.
auto 3.

Qed.



Lemma search_depth_3 : forall (P : nat->Prop),
(P 0) ->
(forall k, P (k-1) -> P k) ->
(P 4).
Proof. hammer_hook "UseAuto" "UseAuto.search_depth_3". auto. Qed.



Lemma search_depth_4 : forall (P : nat->Prop),
(P 0) ->
(forall k, P (k-1) -> P k) ->
(P 5).
Proof. hammer_hook "UseAuto" "UseAuto.search_depth_4". auto. auto 6. Qed.



Lemma search_depth_5 : forall (P : nat->Prop),
(P 0) ->
(forall k, P (k-1) -> P k) ->
(P 4 /\ P 4).
Proof. hammer_hook "UseAuto" "UseAuto.search_depth_5". auto. auto 6. Qed.






Lemma working_of_auto_1 : forall (P : nat->Prop),
(P 0) ->
(forall k, P (k-1) -> P k) ->
(forall k, P (k+1) -> P k) ->
(P 2).

Proof. hammer_hook "UseAuto" "UseAuto.working_of_auto_1". intros P H1 H2 H3.  eauto. Qed.



Lemma working_of_auto_2 : forall (P : nat->Prop),
(P 0) ->
(forall k, P (k+1) -> P k) ->
(forall k, P (k-1) -> P k) ->
(P 2).
Proof. hammer_hook "UseAuto" "UseAuto.working_of_auto_2". intros P H1 H3 H2.  eauto. Qed.








Lemma nat_le_refl : forall (x:nat), x <= x.
Proof. hammer_hook "UseAuto" "UseAuto.nat_le_refl". apply le_n. Qed.

Hint Resolve nat_le_refl.








Ltac auto_star ::= try solve [ jauto ].





Ltac auto_tilde ::= auto.













Module DeterministicImp.
Import Imp.



Theorem ceval_deterministic: forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseAuto" "UseAuto.DeterministicImp.ceval_deterministic".
intros c st st1 st2 E1 E2.
generalize dependent st2.
(induction E1); intros st2 E2; inversion E2; subst.
-  reflexivity.
-  reflexivity.
-
assert (st' = st'0) as EQ1.
{  apply IHE1_1; assumption. }
subst st'0.
apply IHE1_2. assumption.

-
apply IHE1. assumption.
-
rewrite H in H5. inversion H5.

-
rewrite H in H5. inversion H5.
-
apply IHE1. assumption.

-
reflexivity.
-
rewrite H in H2. inversion H2.

-
rewrite H in H4. inversion H4.
-
assert (st' = st'0) as EQ1.
{  apply IHE1_1; assumption. }
subst st'0.
apply IHE1_2. assumption.
Qed.



Theorem ceval_deterministic': forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseAuto" "UseAuto.DeterministicImp.ceval_deterministic'".
admit.
Admitted.



Theorem ceval_deterministic'': forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseAuto" "UseAuto.DeterministicImp.ceval_deterministic''".
introv E1 E2. gen st2.
induction E1; intros; inverts E2; tryfalse.
- auto.
- auto.
- assert (st' = st'0). auto. subst. auto.
- auto.
- auto.
- auto.
- assert (st' = st'0). auto. subst. auto.
Qed.



Theorem ceval_deterministic''': forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseAuto" "UseAuto.DeterministicImp.ceval_deterministic'''".

introv E1 E2. gen st2.
induction E1; intros; inverts E2; tryfalse.
- auto.
- auto.

- dup 4.


+ assert (st' = st'0). apply IHE1_1. apply H1.
skip.


+ forwards: IHE1_1. apply H1.
skip.


+ forwards: IHE1_1. eauto.
skip.


+ forwards*: IHE1_1.
skip.

Abort.



Theorem ceval_deterministic'''': forall c st st1 st2,
st =[ c ]=> st1  ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseAuto" "UseAuto.DeterministicImp.ceval_deterministic''''".
introv E1 E2. gen st2.
induction E1; intros; inverts* E2; tryfalse.
- forwards*: IHE1_1. subst*.
- forwards*: IHE1_1. subst*.
Qed.

End DeterministicImp.






Set Warnings "-notation-overridden,-parsing".
From PLF Require Import StlcProp.
Module PreservationProgressStlc.
Import STLC.
Import STLCProp.



Theorem preservation : forall t t' T,
has_type empty t T  ->
t --> t'  ->
has_type empty t' T.
Proof with eauto. hammer_hook "UseAuto" "UseAuto.PreservationProgressStlc.preservation".
remember (@empty ty) as Gamma.
intros t t' T HT. generalize dependent t'.
(induction HT); intros t' HE; subst Gamma.
-
inversion HE.
-
inversion HE.
-
inversion HE; subst...

+
apply substitution_preserves_typing with T11...
inversion HT1...
-
inversion HE.
-
inversion HE.
-
inversion HE; subst...
Qed.



Theorem preservation' : forall t t' T,
has_type empty t T  ->
t --> t'  ->
has_type empty t' T.
Proof. hammer_hook "UseAuto" "UseAuto.PreservationProgressStlc.preservation'".
admit.
Admitted.






Theorem progress : forall t T,
has_type empty t T ->
value t \/ exists t', t --> t'.
Proof with eauto. hammer_hook "UseAuto" "UseAuto.PreservationProgressStlc.progress".
intros t T Ht.
remember (@empty ty) as Gamma.
(induction Ht); subst Gamma...
-
inversion H.
-
right. destruct IHHt1...
+
destruct IHHt2...
*
inversion H; subst; try solve_by_invert.
exists ([x0:=t2]t)...
*
destruct H0 as [t2' Hstp]. exists (app t1 t2')...
+
destruct H as [t1' Hstp]. exists (app t1' t2)...
-
right. destruct IHHt1...
destruct t1; try solve_by_invert...
inversion H. exists (test x0 t2 t3)...
Qed.



Theorem progress' : forall t T,
has_type empty t T ->
value t \/ exists t', t --> t'.
Proof. hammer_hook "UseAuto" "UseAuto.PreservationProgressStlc.progress'".
admit.
Admitted.

End PreservationProgressStlc.




From PLF Require Import Smallstep.
Require Import Program.
Module Semantics.



Theorem multistep__eval : forall t v,
normal_form_of t v -> exists n, v = C n /\ t ==> n.
Proof. hammer_hook "UseAuto" "UseAuto.Semantics.multistep__eval".
intros t v Hnorm.
unfold normal_form_of in Hnorm.
inversion Hnorm as [Hs Hnf]; clear Hnorm.
rewrite nf_same_as_value in Hnf. inversion Hnf. clear Hnf.
exists n. split. reflexivity.
induction Hs; subst.
-
apply E_Const.
-
eapply step__eval. eassumption. apply IHHs. reflexivity.
Qed.





Theorem multistep_eval_ind : forall t v,
t -->* v -> forall n, C n = v -> t ==> n.
Proof. hammer_hook "UseAuto" "UseAuto.Semantics.multistep_eval_ind".
admit.
Admitted.



Theorem multistep__eval' : forall t v,
normal_form_of t v -> exists n, v = C n /\ t ==> n.
Proof. hammer_hook "UseAuto" "UseAuto.Semantics.multistep__eval'".
admit.
Admitted.





Theorem multistep__eval'' : forall t v,
normal_form_of t v -> exists n, v = C n /\ t ==> n.
Proof. hammer_hook "UseAuto" "UseAuto.Semantics.multistep__eval''".
admit.
Admitted.

End Semantics.




From Coq Require Import omega.Omega.
From PLF Require Import References.
Import STLCRef.
Require Import Program.
Module PreservationProgressReferences.
Hint Resolve store_weakening extends_refl.



Theorem preservation : forall ST t t' T st st',
has_type empty ST t T ->
store_well_typed ST st ->
t / st --> t' / st' ->
exists ST',
(extends ST' ST /\
has_type empty ST' t' T /\
store_well_typed ST' st').
Proof. hammer_hook "UseAuto" "UseAuto.PreservationProgressReferences.preservation".


remember (@empty ty) as Gamma. introv Ht. gen t'.
(induction Ht); introv HST Hstep;

subst Gamma; inverts Hstep; eauto.


-


exists ST. inverts Ht1. splits*. applys* substitution_preserves_typing.

-


forwards: IHHt1. eauto. eauto. eauto.

jauto_set_hyps; intros.

jauto_set_goal; intros.

eauto. eauto. eauto.

-


forwards*: IHHt2.


- forwards*: IHHt.
- forwards*: IHHt.
- forwards*: IHHt1.
- forwards*: IHHt2.
- forwards*: IHHt1.

-
+


exists (ST ++ T1::nil). inverts keep HST. splits.

apply extends_app.

applys_eq T_Loc 1.

rewrite app_length. simpl. omega.

unfold store_Tlookup. rewrite <- H. rewrite* app_nth2.

rewrite minus_diag. simpl. reflexivity.
apply* store_well_typed_app.

- forwards*: IHHt.

-
+


exists ST. splits*.

lets [_ Hsty]: HST.

applys_eq* Hsty 1.

inverts* Ht.

- forwards*: IHHt.

-
+


exists ST. splits*. applys* assign_pres_store_typing. inverts* Ht1.

- forwards*: IHHt1.
- forwards*: IHHt2.
Qed.



Lemma nth_eq_last' : forall (A : Type) (l : list A) (x d : A) (n : nat),
n = length l -> nth n (l ++ x::nil) d = x.
Proof. hammer_hook "UseAuto" "UseAuto.PreservationProgressReferences.nth_eq_last'". intros. subst. apply nth_eq_last. Qed.



Lemma preservation_ref : forall (st:store) (ST : store_ty) T1,
length ST = length st ->
Ref T1 = Ref (store_Tlookup (length st) (ST ++ T1::nil)).
Proof. hammer_hook "UseAuto" "UseAuto.PreservationProgressReferences.preservation_ref".
intros. dup.


unfold store_Tlookup. rewrite* nth_eq_last'.


fequal. symmetry. apply* nth_eq_last'.
Qed.



Theorem preservation' : forall ST t t' T st st',
has_type empty ST t T ->
store_well_typed ST st ->
t / st --> t' / st' ->
exists ST',
(extends ST' ST /\
has_type empty ST' t' T /\
store_well_typed ST' st').
Proof. hammer_hook "UseAuto" "UseAuto.PreservationProgressReferences.preservation'".
remember (@empty ty) as Gamma. introv Ht. gen t'.
induction Ht; introv HST Hstep; subst Gamma; inverts Hstep; eauto.
- exists ST. inverts Ht1. splits*. applys* substitution_preserves_typing.
- forwards*: IHHt1.
- forwards*: IHHt2.
- forwards*: IHHt.
- forwards*: IHHt.
- forwards*: IHHt1.
- forwards*: IHHt2.
- forwards*: IHHt1.
- exists (ST ++ T1::nil). inverts keep HST. splits.
apply extends_app.
applys_eq T_Loc 1.
rewrite app_length. simpl. omega.
unfold store_Tlookup. rewrite* nth_eq_last'.
apply* store_well_typed_app.
- forwards*: IHHt.
- exists ST. splits*. lets [_ Hsty]: HST.
applys_eq* Hsty 1. inverts* Ht.
- forwards*: IHHt.
- exists ST. splits*. applys* assign_pres_store_typing. inverts* Ht1.
- forwards*: IHHt1.
- forwards*: IHHt2.
Qed.






Theorem progress : forall ST t T st,
has_type empty ST t T ->
store_well_typed ST st ->
(value t \/ exists t' st', t / st --> t' / st').
Proof. hammer_hook "UseAuto" "UseAuto.PreservationProgressReferences.progress".
introv Ht HST. remember (@empty ty) as Gamma.
induction Ht; subst Gamma; tryfalse; try solve [left*].
- right. destruct* IHHt1 as [K|].
inverts K; inverts Ht1.
destruct* IHHt2.
- right. destruct* IHHt as [K|].
inverts K; try solve [inverts Ht]. eauto.
- right. destruct* IHHt as [K|].
inverts K; try solve [inverts Ht]. eauto.
- right. destruct* IHHt1 as [K|].
inverts K; try solve [inverts Ht1].
destruct* IHHt2 as [M|].
inverts M; try solve [inverts Ht2]. eauto.
- right. destruct* IHHt1 as [K|].
inverts K; try solve [inverts Ht1]. destruct* n.
- right. destruct* IHHt.
- right. destruct* IHHt as [K|].
inverts K; inverts Ht as M.
inverts HST as N. rewrite* N in M.
- right. destruct* IHHt1 as [K|].
destruct* IHHt2.
inverts K; inverts Ht1 as M.
inverts HST as N. rewrite* N in M.
Qed.

End PreservationProgressReferences.




From PLF Require Sub.
Module SubtypingInversion.
Import Sub.



Lemma abs_arrow : forall x S1 s2 T1 T2,
has_type empty (abs x S1 s2) (Arrow T1 T2) ->
subtype T1 S1
/\ has_type (update empty x S1) s2 T2.
Proof with eauto. hammer_hook "UseAuto" "UseAuto.SubtypingInversion.abs_arrow".
intros x S1 s2 T1 T2 Hty.
apply typing_inversion_abs in Hty.
destruct Hty as [S2 [Hsub Hty]].
apply sub_inversion_arrow in Hsub.
destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
inversion Heq; subst...
Qed.



Lemma abs_arrow' : forall x S1 s2 T1 T2,
has_type empty (abs x S1 s2) (Arrow T1 T2) ->
subtype T1 S1
/\ has_type (update empty x S1) s2 T2.
Proof. hammer_hook "UseAuto" "UseAuto.SubtypingInversion.abs_arrow'".
admit.
Admitted.

End SubtypingInversion.









Lemma order_matters_1 : forall (P : nat->Prop),
(forall n m, P m -> m <> 0 -> P n) ->
P 2 ->
P 1.
Proof. hammer_hook "UseAuto" "UseAuto.order_matters_1".
eauto.

Qed.

Lemma order_matters_2 : forall (P : nat->Prop),
(forall n m, m <> 0 -> P m -> P n) ->
P 5 ->
P 1.
Proof. hammer_hook "UseAuto" "UseAuto.order_matters_2".
eauto.


intros P H K.
eapply H.


eauto.

Abort.










Axiom P : nat -> Prop.

Definition myFact := forall x, x <= 3 -> P x.



Lemma demo_hint_unfold_goal_1 :
(forall x, P x) ->
myFact.
Proof. hammer_hook "UseAuto" "UseAuto.demo_hint_unfold_goal_1".
auto.
unfold myFact. auto.
Qed.



Hint Unfold myFact.



Lemma demo_hint_unfold_goal_2 :
(forall x, P x) ->
myFact.
Proof. hammer_hook "UseAuto" "UseAuto.demo_hint_unfold_goal_2". auto. Qed.



Lemma demo_hint_unfold_context_1 :
(True -> myFact) ->
P 3.
Proof. hammer_hook "UseAuto" "UseAuto.demo_hint_unfold_context_1".
intros.
auto.
unfold myFact in *. auto.
Qed.



Lemma demo_hint_unfold_context_2 :
myFact ->
P 3.
Proof. hammer_hook "UseAuto" "UseAuto.demo_hint_unfold_context_2". auto. Qed.








Parameter le_not_gt : forall x,
(x <= 3) ->
~ (x > 3).



Parameter gt_not_le : forall x,
(x > 3) ->
~ (x <= 3).



Parameter le_gt_false : forall x,
(x <= 3) ->
(x > 3) ->
False.



Section DemoAbsurd1.



Hint Resolve le_not_gt.

Lemma demo_auto_absurd_1 :
(exists x, x <= 3 /\ x > 3) ->
False.
Proof. hammer_hook "UseAuto" "UseAuto.demo_auto_absurd_1".
intros. jauto_set.
eauto.
eapply le_not_gt. eauto. eauto.
Qed.



Hint Resolve le_gt_false.

Lemma demo_auto_absurd_2 :
(exists x, x <= 3 /\ x > 3) ->
False.
Proof. hammer_hook "UseAuto" "UseAuto.demo_auto_absurd_2".
dup.


intros. jauto_set.  eauto.


jauto.
Qed.





End DemoAbsurd1.



Lemma demo_false : forall x,
(x <= 3) ->
(x > 3) ->
4 = 5.
Proof. hammer_hook "UseAuto" "UseAuto.demo_false".
intros. dup 4.


- false. eapply le_gt_false.
+ auto.

+ skip.


- false. eapply le_gt_false.
+ eauto.
+ eauto.


- false le_gt_false. eauto. eauto.


- false le_not_gt. eauto. eauto.

Abort.








Parameter typ : Type.

Parameter subtype : typ -> typ -> Prop.

Parameter subtype_refl : forall T,
subtype T T.

Parameter subtype_trans : forall S T U,
subtype S T -> subtype T U -> subtype S U.



Hint Resolve subtype_refl.



Section HintsTransitivity.

Hint Resolve subtype_trans.



Lemma transitivity_bad_hint_1 : forall S T,
subtype S T.
Proof. hammer_hook "UseAuto" "UseAuto.transitivity_bad_hint_1".
intros.  eauto.
Abort.



End HintsTransitivity.





Hint Extern 1 (subtype ?S ?U) =>
match goal with
| H: subtype S ?T |- _ => apply (@subtype_trans S T U)
| H: subtype ?T U |- _ => apply (@subtype_trans S T U)
end.





Lemma transitivity_workaround_1 : forall T1 T2 T3 T4,
subtype T1 T2 ->
subtype T2 T3 ->
subtype T3 T4 ->
subtype T1 T4.
Proof. hammer_hook "UseAuto" "UseAuto.transitivity_workaround_1".
intros.  eauto.
Qed.



Lemma transitivity_workaround_2 : forall S T,
subtype S T.
Proof. hammer_hook "UseAuto" "UseAuto.transitivity_workaround_2".
intros.  eauto.
Abort.











Require Import Omega.



Lemma omega_demo_1 : forall (x y : nat),
(y <= 4) ->
(x + x + 1 <= y) ->
(x <> 0) ->
(x = 1).
Proof. hammer_hook "UseAuto" "UseAuto.omega_demo_1". intros. omega. Qed.



Lemma omega_demo_2 : forall (x y z : nat),
(x + y = z + z) ->
(x - y <= 4) ->
(x - z <= 2).
Proof. hammer_hook "UseAuto" "UseAuto.omega_demo_2". intros. omega. Qed.



Lemma omega_demo_3 : forall (x y : nat),
(x + 5 <= y) ->
(y - x < 3) ->
False.
Proof. hammer_hook "UseAuto" "UseAuto.omega_demo_3". intros. omega. Qed.



Lemma omega_demo_4 : forall (x y : nat) (P : Prop),
(x + 5 <= y) ->
(y - x < 3) ->
P.
Proof. hammer_hook "UseAuto" "UseAuto.omega_demo_4".
intros.


false. omega.
Qed.






Require Import ZArith.
Module RingDemo.
Open Scope Z_scope.


Lemma ring_demo : forall (x y z : Z),
x * (y + z) - z * 3 * x
= x * y - 2 * x * z.
Proof. hammer_hook "UseAuto" "UseAuto.RingDemo.ring_demo". intros. ring. Qed.

End RingDemo.






Lemma congruence_demo_1 :
forall (f : nat->nat->nat) (g h : nat->nat) (x y z : nat),
f (g x) (g y) = z ->
2 = g x ->
g y = h z ->
f 2 (h z) = z.
Proof. hammer_hook "UseAuto" "UseAuto.congruence_demo_1". intros. congruence. Qed.



Lemma congruence_demo_2 :
forall (f : nat->nat->nat) (g h : nat->nat) (x y z : nat),
(forall a, g a = h a) ->
f (g x) (g y) = z ->
g x = 2 ->
f 2 (h y) = z.
Proof. hammer_hook "UseAuto" "UseAuto.congruence_demo_2". congruence. Qed.



Lemma congruence_demo_4 : forall (f g : nat->nat),
(forall a, f a = g a) ->
f (g (g 2)) = g (f (f 2)).
Proof. hammer_hook "UseAuto" "UseAuto.congruence_demo_4". congruence. Qed.



Lemma congruence_demo_3 :
forall (f g h : nat->nat) (x : nat),
(forall a, f a = h a) ->
g x = f x ->
g x <> h x ->
False.
Proof. hammer_hook "UseAuto" "UseAuto.congruence_demo_3". congruence. Qed.









