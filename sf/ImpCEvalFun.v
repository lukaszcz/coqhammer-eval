From Hammer Require Import Hammer.








From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
From LF Require Import Imp Maps.



Open Scope imp_scope.
Fixpoint ceval_step1 (st : state) (c : com) : state :=
match c with
| SKIP =>
st
| l ::= a1 =>
(l !-> aeval st a1 ; st)
| c1 ;; c2 =>
let st' := ceval_step1 st c1 in
ceval_step1 st' c2
| TEST b THEN c1 ELSE c2 FI =>
if (beval st b)
then ceval_step1 st c1
else ceval_step1 st c2
| WHILE b1 DO c1 END =>
st
end.
Close Scope imp_scope.








Open Scope imp_scope.
Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
match i with
| O => empty_st
| S i' =>
match c with
| SKIP =>
st
| l ::= a1 =>
(l !-> aeval st a1 ; st)
| c1 ;; c2 =>
let st' := ceval_step2 st c1 i' in
ceval_step2 st' c2 i'
| TEST b THEN c1 ELSE c2 FI =>
if (beval st b)
then ceval_step2 st c1 i'
else ceval_step2 st c2 i'
| WHILE b1 DO c1 END =>
if (beval st b1)
then let st' := ceval_step2 st c1 i' in
ceval_step2 st' c i'
else st
end
end.
Close Scope imp_scope.



Open Scope imp_scope.
Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
: option state :=
match i with
| O => None
| S i' =>
match c with
| SKIP =>
Some st
| l ::= a1 =>
Some (l !-> aeval st a1 ; st)
| c1 ;; c2 =>
match (ceval_step3 st c1 i') with
| Some st' => ceval_step3 st' c2 i'
| None => None
end
| TEST b THEN c1 ELSE c2 FI =>
if (beval st b)
then ceval_step3 st c1 i'
else ceval_step3 st c2 i'
| WHILE b1 DO c1 END =>
if (beval st b1)
then match (ceval_step3 st c1 i') with
| Some st' => ceval_step3 st' c i'
| None => None
end
else Some st
end
end.
Close Scope imp_scope.



Notation "'LETOPT' x <== e1 'IN' e2"
:= (match e1 with
| Some x => e2
| None => None
end)
(right associativity, at level 60).

Open Scope imp_scope.
Fixpoint ceval_step (st : state) (c : com) (i : nat)
: option state :=
match i with
| O => None
| S i' =>
match c with
| SKIP =>
Some st
| l ::= a1 =>
Some (l !-> aeval st a1 ; st)
| c1 ;; c2 =>
LETOPT st' <== ceval_step st c1 i' IN
ceval_step st' c2 i'
| TEST b THEN c1 ELSE c2 FI =>
if (beval st b)
then ceval_step st c1 i'
else ceval_step st c2 i'
| WHILE b1 DO c1 END =>
if (beval st b1)
then LETOPT st' <== ceval_step st c1 i' IN
ceval_step st' c i'
else Some st
end
end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
match ceval_step st c 500 with
| None    => None
| Some st => Some (st X, st Y, st Z)
end.





Definition pup_to_n : com
. Admitted.












Theorem ceval_step__ceval: forall c st st',
(exists i, ceval_step st c i = Some st') ->
st =[ c ]=> st'.
Proof. hammer_hook "ImpCEvalFun" "ImpCEvalFun.ceval_step__ceval".
intros c st st' H.
inversion H as [i E].
clear H.
generalize dependent st'.
generalize dependent st.
generalize dependent c.
induction i as [| i' ].

-
intros c st st' H. discriminate H.

-
intros c st st' H.
destruct c;
simpl in H; inversion H; subst; clear H.
+  apply E_Skip.
+  apply E_Ass. reflexivity.

+
destruct (ceval_step st c1 i') eqn:Heqr1.
*
apply E_Seq with s.
apply IHi'. rewrite Heqr1. reflexivity.
apply IHi'. simpl in H1. assumption.
*
discriminate H1.

+
destruct (beval st b) eqn:Heqr.
*
apply E_IfTrue. rewrite Heqr. reflexivity.
apply IHi'. assumption.
*
apply E_IfFalse. rewrite Heqr. reflexivity.
apply IHi'. assumption.

+  destruct (beval st b) eqn :Heqr.
*
destruct (ceval_step st c i') eqn:Heqr1.
{
apply E_WhileTrue with s. rewrite Heqr.
reflexivity.
apply IHi'. rewrite Heqr1. reflexivity.
apply IHi'. simpl in H1. assumption. }
{  discriminate H1. }
*
injection H1. intros H2. rewrite <- H2.
apply E_WhileFalse. apply Heqr. Qed.






Definition manual_grade_for_ceval_step__ceval_inf : option (nat*string) := None.


Theorem ceval_step_more: forall i1 i2 st st' c,
i1 <= i2 ->
ceval_step st c i1 = Some st' ->
ceval_step st c i2 = Some st'.
Proof. hammer_hook "ImpCEvalFun" "ImpCEvalFun.ceval_step_more".
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
-
simpl in Hceval. discriminate Hceval.
-
destruct i2 as [|i2']. inversion Hle.
assert (Hle': i1' <= i2') by omega.
destruct c.
+
simpl in Hceval. inversion Hceval.
reflexivity.
+
simpl in Hceval. inversion Hceval.
reflexivity.
+
simpl in Hceval. simpl.
destruct (ceval_step st c1 i1') eqn:Heqst1'o.
*
apply (IHi1' i2') in Heqst1'o; try assumption.
rewrite Heqst1'o. simpl. simpl in Hceval.
apply (IHi1' i2') in Hceval; try assumption.
*
discriminate Hceval.

+
simpl in Hceval. simpl.
destruct (beval st b); apply (IHi1' i2') in Hceval;
assumption.

+
simpl in Hceval. simpl.
destruct (beval st b); try assumption.
destruct (ceval_step st c i1') eqn: Heqst1'o.
*
apply (IHi1' i2') in Heqst1'o; try assumption.
rewrite -> Heqst1'o. simpl. simpl in Hceval.
apply (IHi1' i2') in Hceval; try assumption.
*
simpl in Hceval. discriminate Hceval.  Qed.



Theorem ceval__ceval_step: forall c st st',
st =[ c ]=> st' ->
exists i, ceval_step st c i = Some st'.
Proof. hammer_hook "ImpCEvalFun" "ImpCEvalFun.ceval__ceval_step".
intros c st st' Hce.
induction Hce.
Admitted.


Theorem ceval_and_ceval_step_coincide: forall c st st',
st =[ c ]=> st'
<-> exists i, ceval_step st c i = Some st'.
Proof. hammer_hook "ImpCEvalFun" "ImpCEvalFun.ceval_and_ceval_step_coincide".
intros c st st'.
split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.






Theorem ceval_deterministic' : forall c st st1 st2,
st =[ c ]=> st1 ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "ImpCEvalFun" "ImpCEvalFun.ceval_deterministic'".
intros c st st1 st2 He1 He2.
apply ceval__ceval_step in He1.
apply ceval__ceval_step in He2.
inversion He1 as [i1 E1].
inversion He2 as [i2 E2].
apply ceval_step_more with (i2 := i1 + i2) in E1.
apply ceval_step_more with (i2 := i1 + i2) in E2.
rewrite E1 in E2. inversion E2. reflexivity.
omega. omega.  Qed.


