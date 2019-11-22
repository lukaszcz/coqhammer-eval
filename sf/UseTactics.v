From Hammer Require Import Hammer.







Set Warnings "-notation-overridden,-parsing".

From Coq Require Import Arith.Arith.

From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import LibTactics.

From PLF Require Stlc.
From PLF Require Equiv.
From PLF Require Imp.
From PLF Require References.
From PLF Require Smallstep.
From PLF Require Hoare.
From PLF Require Sub.















Module IntrovExamples.
Import Stlc.
Import Imp.
Import STLC.



Theorem ceval_deterministic: forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseTactics" "UseTactics.IntrovExamples.ceval_deterministic".
introv E1 E2.
Abort.



Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
(exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. hammer_hook "UseTactics" "UseTactics.IntrovExamples.dist_exists_or".
introv.
Abort.



Theorem ceval_deterministic': forall c st st1,
(st =[ c ]=> st1) ->
forall st2,
(st =[ c ]=> st2) ->
st1 = st2.
Proof. hammer_hook "UseTactics" "UseTactics.IntrovExamples.ceval_deterministic'".
introv E1 E2.
Abort.



Theorem exists_impl: forall X (P : X -> Prop) (Q : Prop) (R : Prop),
(forall x, P x -> Q) ->
((exists x, P x) -> Q).
Proof. hammer_hook "UseTactics" "UseTactics.IntrovExamples.exists_impl".
introv [x H2]. eauto.

Qed.



End IntrovExamples.




Module InvertsExamples.
Import Stlc.
Import Equiv.
Import Imp.
Import STLC.





Theorem skip_left: forall c,
cequiv (SKIP;; c) c.
Proof. hammer_hook "UseTactics" "UseTactics.InvertsExamples.skip_left".
introv. split; intros H.
dup.

- inversion H. subst. inversion H2. subst. assumption.

- inverts H. inverts H2. assumption.
Abort.



Theorem ceval_deterministic: forall c st st1 st2,
st =[ c ]=> st1  ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseTactics" "UseTactics.InvertsExamples.ceval_deterministic".
introv E1 E2. generalize dependent st2.
induction E1; intros st2 E2.
admit. admit.
dup.

- inversion E2. subst. admit.

- inverts E2. admit.
Abort.



Theorem ceval_deterministic': forall c st st1 st2,
st =[ c ]=> st1  ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseTactics" "UseTactics.InvertsExamples.ceval_deterministic'".
introv E1 E2. generalize dependent st2.
(induction E1); intros st2 E2;
inverts E2 as.
-  reflexivity.
-

subst n.
reflexivity.
-

intros st3 Red1 Red2.
assert (st' = st3) as EQ1.
{  apply IHE1_1; assumption. }
subst st3.
apply IHE1_2. assumption.

-

intros.
apply IHE1. assumption.
-
intros.
rewrite H in H5. inversion H5.

Abort.



Theorem skip_left': forall c,
cequiv (SKIP;; c) c.
Proof. hammer_hook "UseTactics" "UseTactics.InvertsExamples.skip_left'".
introv. split; intros H.
inverts H as U V.
inverts U. assumption.
Abort.



Example typing_nonexample_1 :
~ exists T,
has_type empty
(abs x Bool
(abs y Bool
(app (var x) (var y))))
T.
Proof. hammer_hook "UseTactics" "UseTactics.InvertsExamples.typing_nonexample_1".
dup 3.


- intros C. destruct C.
inversion H. subst. clear H.
inversion H5. subst. clear H5.
inversion H4. subst. clear H4.
inversion H2. subst. clear H2.
inversion H1.


- intros C. destruct C.
inverts H as H1.
inverts H1 as H2.
inverts H2 as H3 H4.
inverts H3 as H5.
inverts H5.


- intros C. destruct C.
inverts H as H.
inverts H as H.
inverts H as H1 H2.
inverts H1 as H1.
inverts H1.
Qed.

End InvertsExamples.












Module NaryExamples.
Import References.
Import Smallstep.
Import STLCRef.






Lemma demo_splits : forall n m,
n > 0 /\ n < m /\ m < n+10 /\ m <> 3.
Proof. hammer_hook "UseTactics" "UseTactics.NaryExamples.demo_splits".
intros. splits.
Abort.






Lemma demo_branch : forall n m,
n < m \/ n = m \/ m < n.
Proof. hammer_hook "UseTactics" "UseTactics.NaryExamples.demo_branch".
intros.
destruct (lt_eq_lt_dec n m) as [[H1|H2]|H3].
- branch 1. apply H1.
- branch 2. apply H2.
- branch 3. apply H3.
Qed.

End NaryExamples.








Module EqualityExamples.






Theorem mult_0_plus : forall n m : nat,
(0 + n) * m = n * m.
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.mult_0_plus".
dup.

intros n m.
assert (H: 0 + n = n). reflexivity. rewrite -> H.
reflexivity.


intros n m.
asserts_rewrite (0 + n = n).
reflexivity.
reflexivity.
Qed.





Theorem mult_0_plus' : forall n m : nat,
(0 + n) * m = n * m.
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.mult_0_plus'".
intros n m.
cuts_rewrite (0 + n = n).
reflexivity.
reflexivity.
Qed.



Theorem mult_0_plus'' : forall u v w x y z: nat,
(u + v) * (S (w * x + y)) = z.
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.mult_0_plus''".
intros. asserts_rewrite (forall a b, a*(S b) = a*b+a).


Abort.






Lemma demo_substs : forall x y (f:nat->nat),
x = f x ->
y = x ->
y = f x.
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.demo_substs".
intros. substs.
assumption.
Qed.






Lemma demo_fequals : forall (a b c d e : nat) (f : nat->nat->nat->nat->nat),
a = 1 ->
b = e ->
e = 2 ->
f a b c d = f 1 2 c 4.
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.demo_fequals".
intros. fequals.

Abort.






Axiom big_expression_using : nat->nat.

Lemma demo_applys_eq_1 : forall (P:nat->nat->Prop) x y z,
P x (big_expression_using z) ->
P x (big_expression_using y).
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.demo_applys_eq_1".
introv H. dup.


assert (Eq: big_expression_using y = big_expression_using z).
admit.
rewrite Eq. apply H.


applys_eq H 1.
admit.
Abort.



Lemma demo_applys_eq_2 : forall (P:nat->nat->Prop) x y z,
P (big_expression_using z) x ->
P (big_expression_using y) x.
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.demo_applys_eq_2".
introv H. applys_eq H 2.
Abort.



Lemma demo_applys_eq_3 : forall (P:nat->nat->Prop) x1 x2 y1 y2,
P (big_expression_using x2) (big_expression_using y2) ->
P (big_expression_using x1) (big_expression_using y1).
Proof. hammer_hook "UseTactics" "UseTactics.EqualityExamples.demo_applys_eq_3".
introv H. applys_eq H 1 2.

Abort.

End EqualityExamples.









Module UnfoldsExample.
Import Hoare.



Lemma bexp_eval_true : forall b st,
beval st b = true ->
(bassn b) st.
Proof. hammer_hook "UseTactics" "UseTactics.UnfoldsExample.bexp_eval_true".
intros b st Hbe. dup.


unfold bassn. assumption.


unfolds. assumption.
Qed.





End UnfoldsExample.






Lemma demo_false : forall n,
S n = 1 ->
n = 0.
Proof. hammer_hook "UseTactics" "UseTactics.demo_false".
intros. destruct n. reflexivity. false.
Qed.



Lemma demo_false_arg :
(forall n, n < 0 -> False) ->
3 < 0 ->
4 < 0.
Proof. hammer_hook "UseTactics" "UseTactics.demo_false_arg".
intros H L. false H. apply L.
Qed.



Lemma demo_tryfalse : forall n,
S n = 1 ->
n = 0.
Proof. hammer_hook "UseTactics" "UseTactics.demo_tryfalse".
intros. destruct n; tryfalse. reflexivity.
Qed.






Module GenExample.
Import Stlc.
Import STLC.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
has_type (update Gamma x U) t S ->
has_type empty v U ->
has_type Gamma ([x:=v]t) S.
Proof. hammer_hook "UseTactics" "UseTactics.GenExample.substitution_preserves_typing".
dup.


intros Gamma x U v t S Htypt Htypv.
generalize dependent S. generalize dependent Gamma.
induction t; intros; simpl.
admit. admit. admit. admit. admit. admit.


introv Htypt Htypv. gen S Gamma.
induction t; intros; simpl.
admit. admit. admit. admit. admit. admit.
Abort.

End GenExample.






Module SkipExample.
Import Stlc.
Import STLC.



Theorem demo_admits : True.
Proof. hammer_hook "UseTactics" "UseTactics.SkipExample.demo_admits".
admits H: (forall n m : nat, (0 + n) * m = n * m).
Abort.



Theorem mult_plus_0 : forall n m : nat,
(n + 0) * m = n * m.
Proof. hammer_hook "UseTactics" "UseTactics.SkipExample.mult_plus_0".
dup 3.


intros n m.
assert (H: n + 0 = n). admit. rewrite -> H. clear H.
reflexivity.


intros n m.
admit_rewrite (n + 0 = n).
reflexivity.


intros n m.
admit_rewrite (forall a, a + 0 = a).
reflexivity.
Admitted.



Theorem ceval_deterministic: forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseTactics" "UseTactics.SkipExample.ceval_deterministic".

admit_goal.

introv E1 E2. gen st2.
(induction E1); introv E2; inverts E2 as.
-  reflexivity.
-
subst n.
reflexivity.
-
intros st3 Red1 Red2.
assert (st' = st3) as EQ1.
{

eapply IH. eapply E1_1. eapply Red1. }
subst st3.

eapply IH. eapply E1_2. eapply Red2.

Abort.

End SkipExample.




Module SortExamples.
Import Imp.



Theorem ceval_deterministic: forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "UseTactics" "UseTactics.SortExamples.ceval_deterministic".
intros c st st1 st2 E1 E2.
generalize dependent st2.
(induction E1); intros st2 E2; inverts E2.
admit. admit.
sort.
Abort.

End SortExamples.













Module ExamplesLets.
Import Sub.



Import Sub.

Axiom typing_inversion_var : forall (G:context) (x:string) (T:ty),
has_type G (var x) T ->
exists S, G x = Some S /\ subtype S T.



Lemma demo_lets_1 : forall (G:context) (x:string) (T:ty),
has_type G (var x) T ->
True.
Proof. hammer_hook "UseTactics" "UseTactics.ExamplesLets.demo_lets_1".
intros G x T H. dup.


lets K: typing_inversion_var H.
destruct K as (S & Eq & Sub).
admit.


lets (S & Eq & Sub): typing_inversion_var H.
admit.
Abort.



Lemma demo_lets_2 : forall (G:context) (x:string) (T:ty), True.
Proof. hammer_hook "UseTactics" "UseTactics.ExamplesLets.demo_lets_2".
intros G x T.
lets (S & Eq & Sub): typing_inversion_var G x T ___.
Abort.



Lemma demo_lets_3 : forall (x:string), True.
Proof. hammer_hook "UseTactics" "UseTactics.ExamplesLets.demo_lets_3".
intros x.
lets (S & Eq & Sub): typing_inversion_var x ___.
Abort.



Lemma demo_lets_4 : True.
Proof. hammer_hook "UseTactics" "UseTactics.ExamplesLets.demo_lets_4".
lets (S & Eq & Sub): typing_inversion_var ___.
Abort.



Lemma demo_lets_5 : True.
Proof. hammer_hook "UseTactics" "UseTactics.ExamplesLets.demo_lets_5".
lets H: typing_inversion_var.
Abort.



Lemma demo_lets_underscore :
(forall n m, n <= m -> n < m+1) ->
True.
Proof. hammer_hook "UseTactics" "UseTactics.ExamplesLets.demo_lets_underscore".
intros H.


lets K: H 3.
clear K.


lets K: H __ 3.
clear K.
Abort.



End ExamplesLets.









Module ExamplesInstantiations.
Import Sub.



Lemma substitution_preserves_typing : forall Gamma x U v t S,
has_type (update Gamma x U) t S ->
has_type empty v U ->
has_type Gamma ([x:=v]t) S.
Proof with eauto. hammer_hook "UseTactics" "UseTactics.ExamplesInstantiations.substitution_preserves_typing".
intros Gamma x U v t S Htypt Htypv.
generalize dependent S. generalize dependent Gamma.
(induction t); intros; simpl.
-
rename s into y.



lets (T&Hctx&Hsub): typing_inversion_var Htypt.
unfold update, t_update in Hctx.
destruct (eqb_stringP x y)...
+
subst.
inversion Hctx; subst. clear Hctx.
apply context_invariance with empty...
intros x Hcontra.




lets [T' HT']: free_in_context S (@empty ty) Hcontra...
inversion HT'.
-



admit.

-
rename s into y. rename t into T1.



lets (T2&Hsub&Htypt2): typing_inversion_abs Htypt.



applys T_Sub (Arrow T1 T2)...
apply T_Abs...
destruct (eqb_stringP x y).
+
eapply context_invariance...
subst.
intros x Hafi. unfold update, t_update.
destruct (eqb_stringP y x)...
+
apply IHt. eapply context_invariance...
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y z)...
subst. rewrite false_eqb_string...
-
lets: typing_inversion_true Htypt...
-
lets: typing_inversion_false Htypt...
-
lets (Htyp1&Htyp2&Htyp3): typing_inversion_if Htypt...
-


lets: typing_inversion_unit Htypt...

Admitted.

End ExamplesInstantiations.







