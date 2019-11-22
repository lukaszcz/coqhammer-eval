From Hammer Require Import Hammer.





From PLF Require Import Imp.
From PLF Require Import Hoare.




Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
| H_Skip : forall P,
hoare_proof P (SKIP) P
| H_Asgn : forall Q V a,
hoare_proof (assn_sub V a Q) (V ::= a) Q
| H_Seq  : forall P c Q d R,
hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;;d) R
| H_If : forall P Q b c1 c2,
hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
hoare_proof P (TEST b THEN c1 ELSE c2 FI) Q
| H_While : forall P b c,
hoare_proof (fun st => P st /\ bassn b st) c P ->
hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~ (bassn b st))
| H_Consequence  : forall (P Q P' Q' : Assertion) c,
hoare_proof P' c Q' ->
(forall st, P st -> P' st) ->
(forall st, Q' st -> Q st) ->
hoare_proof P c Q.



Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
hoare_proof P' c Q ->
(forall st, P st -> P' st) ->
hoare_proof P c Q.
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.H_Consequence_pre".
intros. eapply H_Consequence.
apply X.  apply H.  intros. apply H0. Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
hoare_proof P c Q' ->
(forall st, Q' st -> Q st) ->
hoare_proof P c Q.
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.H_Consequence_post".
intros. eapply H_Consequence.
apply X. intros. apply H0.  apply H. Qed.



Example sample_proof :
hoare_proof
((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
(X ::= X + 1;; X ::= X + 2)
(fun st:state => st X = 3).
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.sample_proof".
eapply H_Seq; apply H_Asgn.
Qed.








Theorem hoare_proof_sound : forall P c Q,
hoare_proof P c Q -> {{P}} c {{Q}}.
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.hoare_proof_sound".
Admitted.




Theorem H_Post_True_deriv:
forall c P, hoare_proof P c (fun _ => True).
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.H_Post_True_deriv".
intro c.
induction c; intro P.
-
eapply H_Consequence.
apply H_Skip.
intros. apply H.

intros. apply I.
-
eapply H_Consequence_pre.
apply H_Asgn.
intros. apply I.
-
eapply H_Consequence_pre.
eapply H_Seq.
apply (IHc1 (fun _ => True)).
apply IHc2.
intros. apply I.
-
apply H_Consequence_pre with (fun _ => True).
apply H_If.
apply IHc1.
apply IHc2.
intros. apply I.
-
eapply H_Consequence.
eapply H_While.
eapply IHc.
intros; apply I.
intros; apply I.
Qed.



Lemma False_and_P_imp: forall P Q,
False /\ P -> Q.
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.False_and_P_imp".
intros P Q [CONTRA HP].
destruct CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
eapply H_Consequence_pre;
[eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
forall c Q, hoare_proof (fun _ => False) c Q.
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.H_Pre_False_deriv".
intros c.
induction c; intro Q.
-  pre_false_helper H_Skip.
-  pre_false_helper H_Asgn.
-  pre_false_helper H_Seq. apply IHc1. apply IHc2.
-
apply H_If; eapply H_Consequence_pre.
apply IHc1. intro. eapply False_and_P_imp.
apply IHc2. intro. eapply False_and_P_imp.
-
eapply H_Consequence_post.
eapply H_While.
eapply H_Consequence_pre.
apply IHc.
intro. eapply False_and_P_imp.
intro. simpl. eapply False_and_P_imp.
Qed.



Definition wp (c:com) (Q:Assertion) : Assertion :=
fun s => forall s', s =[ c ]=> s' -> Q s'.



Lemma wp_is_precondition: forall c Q,
{{wp c Q}} c {{Q}}.
Admitted.




Lemma wp_is_weakest: forall c Q P',
{{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
Admitted.



Lemma bassn_eval_false : forall b st, ~ bassn b st -> beval st b = false.
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.bassn_eval_false".
intros b st H. unfold bassn in H. destruct (beval st b).
exfalso. apply H. reflexivity.
reflexivity.
Qed.




Theorem hoare_proof_complete: forall P c Q,
{{P}} c {{Q}} -> hoare_proof P c Q.
Proof. hammer_hook "HoareAsLogic" "HoareAsLogic.hoare_proof_complete".
intros P c. generalize dependent P.
induction c; intros P Q HT.
-
eapply H_Consequence.
eapply H_Skip.
intros.  eassumption.
intro st. apply HT.  apply E_Skip.
-
eapply H_Consequence.
eapply H_Asgn.
intro st. apply HT. econstructor. reflexivity.
intros; assumption.
-
apply H_Seq with (wp c2 Q).
eapply IHc1.
intros st st' E1 H. unfold wp. intros st'' E2.
eapply HT. econstructor; eassumption. assumption.
eapply IHc2. intros st st' E1 H. apply H; assumption.
Admitted.





