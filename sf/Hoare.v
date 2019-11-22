From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From PLF Require Import Imp.












Definition Assertion := state -> Prop.



Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
fun st => st Z * st Z <= st X /\
~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

End ExAssertions.








Definition assert_implies (P Q : Assertion) : Prop :=
forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
(at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.





Notation "P <<->> Q" :=
(P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.










Definition hoare_triple
(P : Assertion) (c : com) (Q : Assertion) : Prop :=
forall st st',
st =[ c ]=> st'  ->
P st  ->
Q st'.



Notation "{{ P }}  c  {{ Q }}" :=
(hoare_triple P c Q) (at level 90, c at next level)
: hoare_spec_scope.









Theorem hoare_post_true : forall (P Q : Assertion) c,
(forall st, Q st) ->
{{P}} c {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_post_true".
intros P Q c H. unfold hoare_triple.
intros st st' Heval HP.
apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
(forall st, ~ (P st)) ->
{{P}} c {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_pre_false".
intros P Q c H. unfold hoare_triple.
intros st st' Heval HP.
unfold not in H. apply H in HP.
inversion HP.  Qed.























Definition assn_sub X a P : Assertion :=
fun (st : state) =>
P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
(at level 10, X at next level).











Theorem hoare_asgn : forall Q X a,
{{Q [X |-> a]}} X ::= a {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_asgn".
unfold hoare_triple.
intros Q X a st st' HE HQ.
inversion HE. subst.
unfold assn_sub in HQ. assumption.  Qed.



Example assn_sub_example :
{{(fun st => st X < 5) [X |-> X + 1]}}
X ::= X + 1
{{fun st => st X < 5}}.
Proof. hammer_hook "Hoare" "Hoare.assn_sub_example".

apply hoare_asgn.  Qed.








Definition manual_grade_for_hoare_asgn_examples : option (nat*string) := None.







Definition manual_grade_for_hoare_asgn_wrong : option (nat*string) := None.




Theorem hoare_asgn_fwd :
forall m a P,
{{fun st => P st /\ st X = m}}
X ::= a
{{fun st => P (X !-> m ; st)
/\ st X = aeval (X !-> m ; st) a }}.
Proof. hammer_hook "Hoare" "Hoare.hoare_asgn_fwd".
Admitted.




Theorem hoare_asgn_fwd_exists :
forall a P,
{{fun st => P st}}
X ::= a
{{fun st => exists m, P (X !-> m ; st) /\
st X = aeval (X !-> m ; st) a }}.
Proof. hammer_hook "Hoare" "Hoare.hoare_asgn_fwd_exists".
intros a P.
Admitted.











Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
{{P'}} c {{Q}} ->
P ->> P' ->
{{P}} c {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_consequence_pre".
intros P P' Q c Hhoare Himp.
intros st st' Hc HP. apply (Hhoare st st').
assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
{{P}} c {{Q'}} ->
Q' ->> Q ->
{{P}} c {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_consequence_post".
intros P Q Q' c Hhoare Himp.
intros st st' Hc HP.
apply Himp.
apply (Hhoare st st').
assumption. assumption. Qed.



Example hoare_asgn_example1 :
{{fun st => True}} X ::= 1 {{fun st => st X = 1}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_asgn_example1".

apply hoare_consequence_pre
with (P' := (fun st => st X = 1) [X |-> 1]).
apply hoare_asgn.
intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.



Example assn_sub_example2 :
{{(fun st => st X < 4)}}
X ::= X + 1
{{fun st => st X < 5}}.
Proof. hammer_hook "Hoare" "Hoare.assn_sub_example2".

apply hoare_consequence_pre
with (P' := (fun st => st X < 5) [X |-> X + 1]).
apply hoare_asgn.
intros st H. unfold assn_sub, t_update. simpl. omega.
Qed.



Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
{{P'}} c {{Q'}} ->
P ->> P' ->
Q' ->> Q ->
{{P}} c {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_consequence".
intros P P' Q Q' c Hht HPP' HQ'Q.
apply hoare_consequence_pre with (P' := P').
apply hoare_consequence_post with (Q' := Q').
assumption. assumption. assumption.  Qed.






Example hoare_asgn_example1' :
{{fun st => True}}
X ::= 1
{{fun st => st X = 1}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_asgn_example1'".
eapply hoare_consequence_pre.
apply hoare_asgn.
intros st H.  reflexivity.  Qed.





Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
(forall x y : nat, P x y) ->
(forall x y : nat, P x y -> Q x) ->
Q 42.
Proof. hammer_hook "Hoare" "Hoare.silly1".
intros P Q HP HQ. eapply HQ. apply HP.


Abort.



Lemma silly2 :
forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
(exists y, P 42 y) ->
(forall x y : nat, P x y -> Q x) ->
Q 42.
Proof. hammer_hook "Hoare" "Hoare.silly2".
intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].


Abort.

Lemma silly2_fixed :
forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
(exists y, P 42 y) ->
(forall x y : nat, P x y -> Q x) ->
Q 42.
Proof. hammer_hook "Hoare" "Hoare.silly2_fixed".
intros P Q HP HQ. destruct HP as [y HP'].
eapply HQ. apply HP'.
Qed.



Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
(exists y, P 42 y) ->
(forall x y : nat, P x y -> Q x) ->
Q 42.
Proof. hammer_hook "Hoare" "Hoare.silly2_eassumption".
intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.






Definition manual_grade_for_hoare_asgn_examples_2 : option (nat*string) := None.







Theorem hoare_skip : forall P,
{{P}} SKIP {{P}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_skip".
intros P st st' H HP. inversion H. subst.
assumption.  Qed.






Theorem hoare_seq : forall P Q R c1 c2,
{{Q}} c2 {{R}} ->
{{P}} c1 {{Q}} ->
{{P}} c1;;c2 {{R}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_seq".
intros P Q R c1 c2 H1 H2 st st' H12 Pre.
inversion H12; subst.
apply (H1 st'0 st'); try assumption.
apply (H2 st st'0); assumption. Qed.







Example hoare_asgn_example3 : forall a n,
{{fun st => aeval st a = n}}
X ::= a;; SKIP
{{fun st => st X = n}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_asgn_example3".
intros a n. eapply hoare_seq.
-
apply hoare_skip.
-
eapply hoare_consequence_pre. apply hoare_asgn.
intros st H. subst. reflexivity.
Qed.





Example hoare_asgn_example4 :
{{fun st => True}}
X ::= 1;; Y ::= 2
{{fun st => st X = 1 /\ st Y = 2}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_asgn_example4".
Admitted.




Definition swap_program : com
. Admitted.

Theorem swap_exercise :
{{fun st => st X <= st Y}}
swap_program
{{fun st => st Y <= st X}}.
Proof. hammer_hook "Hoare" "Hoare.swap_exercise".
Admitted.







Definition manual_grade_for_hoarestate1 : option (nat*string) := None.













Definition bassn b : Assertion :=
fun st => (beval st b = true).



Lemma bexp_eval_true : forall b st,
beval st b = true -> (bassn b) st.
Proof. hammer_hook "Hoare" "Hoare.bexp_eval_true".
intros b st Hbe.
unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
beval st b = false -> ~ ((bassn b) st).
Proof. hammer_hook "Hoare" "Hoare.bexp_eval_false".
intros b st Hbe contra.
unfold bassn in contra.
rewrite -> contra in Hbe. inversion Hbe.  Qed.



Theorem hoare_if : forall P Q b c1 c2,
{{fun st => P st /\ bassn b st}} c1 {{Q}} ->
{{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
{{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_if".
intros P Q b c1 c2 HTrue HFalse st st' HE HP.
inversion HE; subst.
-
apply (HTrue st st').
assumption.
split. assumption.
apply bexp_eval_true. assumption.
-
apply (HFalse st st').
assumption.
split. assumption.
apply bexp_eval_false. assumption. Qed.






Example if_example :
{{fun st => True}}
TEST X = 0
THEN Y ::= 2
ELSE Y ::= X + 1
FI
{{fun st => st X <= st Y}}.
Proof. hammer_hook "Hoare" "Hoare.if_example".

apply hoare_if.
-
eapply hoare_consequence_pre. apply hoare_asgn.
unfold bassn, assn_sub, t_update, assert_implies.
simpl. intros st [_ H].
apply eqb_eq in H.
rewrite H. omega.
-
eapply hoare_consequence_pre. apply hoare_asgn.
unfold assn_sub, t_update, assert_implies.
simpl; intros st _. omega.
Qed.



Theorem if_minus_plus :
{{fun st => True}}
TEST X <= Y
THEN Z ::= Y - X
ELSE Y ::= X + Z
FI
{{fun st => st Y = st X + st Z}}.
Proof. hammer_hook "Hoare" "Hoare.if_minus_plus".
Admitted.









Module If1.

Inductive com : Type :=
| CSkip : com
| CAss : string -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
CSkip : imp_scope.
Notation "c1 ;; c2" :=
(CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "X '::=' a" :=
(CAss X a) (at level 60) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
(CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
(CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'IF1' b 'THEN' c 'FI'" :=
(CIf1 b c) (at level 80, right associativity) : imp_scope.



Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Open Scope imp_scope.
Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
st =[ SKIP ]=> st
| E_Ass  : forall st a1 n x,
aeval st a1 = n ->
st =[ x ::= a1 ]=> (x !-> n ; st)
| E_Seq : forall c1 c2 st st' st'',
st  =[ c1 ]=> st'  ->
st' =[ c2 ]=> st'' ->
st  =[ c1 ;; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
beval st b = true ->
st =[ c1 ]=> st' ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
| E_IfFalse : forall st st' b c1 c2,
beval st b = false ->
st =[ c2 ]=> st' ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
| E_WhileFalse : forall b st c,
beval st b = false ->
st =[ WHILE b DO c END ]=> st
| E_WhileTrue : forall st st' st'' b c,
beval st b = true ->
st  =[ c ]=> st' ->
st' =[ WHILE b DO c END ]=> st'' ->
st  =[ WHILE b DO c END ]=> st''


where "st '=[' c ']=>' st'" := (ceval c st st').
Close Scope imp_scope.



Definition hoare_triple
(P : Assertion) (c : com) (Q : Assertion) : Prop :=
forall st st',
st =[ c ]=> st' ->
P st  ->
Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
(at level 90, c at next level)
: hoare_spec_scope.









Lemma hoare_if1_good :
{{ fun st => st X + st Y = st Z }}
(IF1 ~(Y = 0) THEN
X ::= X + Y
FI)%imp
{{ fun st => st X = st Z }}.
Proof. hammer_hook "Hoare" "Hoare.If1.hoare_if1_good".  Admitted.

End If1.


Definition manual_grade_for_if1_hoare : option (nat*string) := None.



















Theorem hoare_while : forall P b c,
{{fun st => P st /\ bassn b st}} c {{P}} ->
{{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof. hammer_hook "Hoare" "Hoare.hoare_while".
intros P b c Hhoare st st' He HP.

remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
induction He;
try (inversion Heqwcom); subst; clear Heqwcom.
-
split. assumption. apply bexp_eval_false. assumption.
-
apply IHHe2. reflexivity.
apply (Hhoare st st'). assumption.
split. assumption. apply bexp_eval_true. assumption.
Qed.



Example while_example :
{{fun st => st X <= 3}}
WHILE X <= 2
DO X ::= X + 1 END
{{fun st => st X = 3}}.
Proof. hammer_hook "Hoare" "Hoare.while_example".
eapply hoare_consequence_post.
apply hoare_while.
eapply hoare_consequence_pre.
apply hoare_asgn.
unfold bassn, assn_sub, assert_implies, t_update. simpl.
intros st [H1 H2]. apply leb_complete in H2. omega.
unfold bassn, assert_implies. intros st [Hle Hb].
simpl in Hb. destruct ((st X) <=? 2) eqn : Heqle.
exfalso. apply Hb; reflexivity.
apply leb_iff_conv in Heqle. omega.
Qed.


Theorem always_loop_hoare : forall P Q,
{{P}} WHILE true DO SKIP END {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.always_loop_hoare".

intros P Q.
apply hoare_consequence_pre with (P' := fun st : state => True).
eapply hoare_consequence_post.
apply hoare_while.
-
apply hoare_post_true. intros st. apply I.
-
simpl. intros st [Hinv Hguard].
exfalso. apply Hguard. reflexivity.
-
intros st H. constructor.  Qed.










Module RepeatExercise.

Inductive com : Type :=
| CSkip : com
| CAsgn : string -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CRepeat : com -> bexp -> com.



Notation "'SKIP'" :=
CSkip.
Notation "c1 ;; c2" :=
(CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
(CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
(CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
(CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
(CRepeat e1 b2) (at level 80, right associativity).



Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : state -> com -> state -> Prop :=
| E_Skip : forall st,
st =[ SKIP ]=> st
| E_Ass  : forall st a1 n x,
aeval st a1 = n ->
st =[ x ::= a1 ]=> (x !-> n ; st)
| E_Seq : forall c1 c2 st st' st'',
st  =[ c1 ]=> st'  ->
st' =[ c2 ]=> st'' ->
st  =[ c1 ;; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
beval st b = true ->
st =[ c1 ]=> st' ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
| E_IfFalse : forall st st' b c1 c2,
beval st b = false ->
st =[ c2 ]=> st' ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
| E_WhileFalse : forall b st c,
beval st b = false ->
st =[ WHILE b DO c END ]=> st
| E_WhileTrue : forall st st' st'' b c,
beval st b = true ->
st  =[ c ]=> st' ->
st' =[ WHILE b DO c END ]=> st'' ->
st  =[ WHILE b DO c END ]=> st''


where "st '=[' c ']=>' st'" := (ceval st c st').



Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion)
: Prop :=
forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
(hoare_triple P c Q) (at level 90, c at next level).



Definition ex1_repeat :=
REPEAT
X ::= 1;;
Y ::= Y + 1
UNTIL X = 1 END.

Theorem ex1_repeat_works :
empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof. hammer_hook "Hoare" "Hoare.RepeatExercise.ex1_repeat_works".
Admitted.







End RepeatExercise.


Definition manual_grade_for_hoare_repeat : option (nat*string) := None.












Module Himp.

Inductive com : Type :=
| CSkip : com
| CAsgn : string -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CHavoc : string -> com.

Notation "'SKIP'" :=
CSkip.
Notation "X '::=' a" :=
(CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
(CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
(CWhile b c) (at level 80, right associativity).
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
(CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
st =[ SKIP ]=> st
| E_Ass  : forall st a1 n x,
aeval st a1 = n ->
st =[ x ::= a1 ]=> (x !-> n ; st)
| E_Seq : forall c1 c2 st st' st'',
st  =[ c1 ]=> st'  ->
st' =[ c2 ]=> st'' ->
st  =[ c1 ;; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
beval st b = true ->
st =[ c1 ]=> st' ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
| E_IfFalse : forall st st' b c1 c2,
beval st b = false ->
st =[ c2 ]=> st' ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
| E_WhileFalse : forall b st c,
beval st b = false ->
st =[ WHILE b DO c END ]=> st
| E_WhileTrue : forall st st' st'' b c,
beval st b = true ->
st  =[ c ]=> st' ->
st' =[ WHILE b DO c END ]=> st'' ->
st  =[ WHILE b DO c END ]=> st''
| E_Havoc : forall st X n,
st =[ HAVOC X ]=> (X !-> n ; st)

where "st '=[' c ']=>' st'" := (ceval c st st').



Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
(at level 90, c at next level)
: hoare_spec_scope.



Definition havoc_pre (X : string) (Q : Assertion) : Assertion
. Admitted.

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
{{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof. hammer_hook "Hoare" "Hoare.Himp.hoare_havoc".
Admitted.

End Himp.




Module HoareAssertAssume.



Inductive com : Type :=
| CSkip : com
| CAss : string -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CAssert : bexp -> com
| CAssume : bexp -> com.

Notation "'SKIP'" :=
CSkip.
Notation "x '::=' a" :=
(CAss x a) (at level 60).
Notation "c1 ;; c2" :=
(CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
(CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
(CIf c1 c2 c3) (at level 80, right associativity).
Notation "'ASSERT' b" :=
(CAssert b) (at level 60).
Notation "'ASSUME' b" :=
(CAssume b) (at level 60).



Inductive result : Type :=
| RNormal : state -> result
| RError : result.



Inductive ceval : com -> state -> result -> Prop :=

| E_Skip : forall st,
st =[ SKIP ]=> RNormal st
| E_Ass  : forall st a1 n x,
aeval st a1 = n ->
st =[ x ::= a1 ]=> RNormal (x !-> n ; st)
| E_SeqNormal : forall c1 c2 st st' r,
st  =[ c1 ]=> RNormal st' ->
st' =[ c2 ]=> r ->
st  =[ c1 ;; c2 ]=> r
| E_SeqError : forall c1 c2 st,
st =[ c1 ]=> RError ->
st =[ c1 ;; c2 ]=> RError
| E_IfTrue : forall st r b c1 c2,
beval st b = true ->
st =[ c1 ]=> r ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> r
| E_IfFalse : forall st r b c1 c2,
beval st b = false ->
st =[ c2 ]=> r ->
st =[ TEST b THEN c1 ELSE c2 FI ]=> r
| E_WhileFalse : forall b st c,
beval st b = false ->
st =[ WHILE b DO c END ]=> RNormal st
| E_WhileTrueNormal : forall st st' r b c,
beval st b = true ->
st  =[ c ]=> RNormal st' ->
st' =[ WHILE b DO c END ]=> r ->
st  =[ WHILE b DO c END ]=> r
| E_WhileTrueError : forall st b c,
beval st b = true ->
st =[ c ]=> RError ->
st =[ WHILE b DO c END ]=> RError

| E_AssertTrue : forall st b,
beval st b = true ->
st =[ ASSERT b ]=> RNormal st
| E_AssertFalse : forall st b,
beval st b = false ->
st =[ ASSERT b ]=> RError
| E_Assume : forall st b,
beval st b = true ->
st =[ ASSUME b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).



Definition hoare_triple
(P : Assertion) (c : com) (Q : Assertion) : Prop :=
forall st r,
st =[ c ]=> r  -> P st  ->
(exists st', r = RNormal st' /\ Q st').

Notation "{{ P }}  c  {{ Q }}" :=
(hoare_triple P c Q) (at level 90, c at next level)
: hoare_spec_scope.



Theorem assert_assume_differ : exists P b Q,
({{P}} ASSUME b {{Q}})
/\ ~ ({{P}} ASSERT b {{Q}}).
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.assert_assume_differ".
Admitted.

Theorem assert_implies_assume : forall P b Q,
({{P}} ASSERT b {{Q}})
-> ({{P}} ASSUME b {{Q}}).
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.assert_implies_assume".
Admitted.



Theorem hoare_asgn : forall Q X a,
{{Q [X |-> a]}} X ::= a {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.hoare_asgn".
unfold hoare_triple.
intros Q X a st st' HE HQ.
inversion HE. subst.
exists (X !-> aeval st a ; st). split; try reflexivity.
assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
{{P'}} c {{Q}} ->
P ->> P' ->
{{P}} c {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.hoare_consequence_pre".
intros P P' Q c Hhoare Himp.
intros st st' Hc HP. apply (Hhoare st st').
assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
{{P}} c {{Q'}} ->
Q' ->> Q ->
{{P}} c {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.hoare_consequence_post".
intros P Q Q' c Hhoare Himp.
intros st r Hc HP.
unfold hoare_triple in Hhoare.
assert (exists st', r = RNormal st' /\ Q' st').
{ apply (Hhoare st); assumption. }
destruct H as [st' [Hr HQ']].
exists st'. split; try assumption.
apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
{{Q}} c2 {{R}} ->
{{P}} c1 {{Q}} ->
{{P}} c1;;c2 {{R}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.hoare_seq".
intros P Q R c1 c2 H1 H2 st r H12 Pre.
inversion H12; subst.
- eapply H1.
+ apply H6.
+ apply H2 in H3. apply H3 in Pre.
destruct Pre as [st'0 [Heq HQ]].
inversion Heq; subst. assumption.
-
apply H2 in H5. apply H5 in Pre.
destruct Pre as [st' [C _]].
inversion C.
Qed.






Theorem hoare_skip : forall P,
{{P}} SKIP {{P}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.hoare_skip".
intros P st st' H HP. inversion H. subst.
eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
{{fun st => P st /\ bassn b st}} c1 {{Q}} ->
{{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
{{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.hoare_if".
intros P Q b c1 c2 HTrue HFalse st st' HE HP.
inversion HE; subst.
-
apply (HTrue st st').
assumption.
split. assumption.
apply bexp_eval_true. assumption.
-
apply (HFalse st st').
assumption.
split. assumption.
apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P b c,
{{fun st => P st /\ bassn b st}} c {{P}} ->
{{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.hoare_while".
intros P b c Hhoare st st' He HP.
remember (WHILE b DO c END) as wcom eqn:Heqwcom.
induction He;
try (inversion Heqwcom); subst; clear Heqwcom.
-
eexists. split. reflexivity. split.
assumption. apply bexp_eval_false. assumption.
-
clear IHHe1.
apply IHHe2. reflexivity.
clear IHHe2 He2 r.
unfold hoare_triple in Hhoare.
apply Hhoare in He1.
+ destruct He1 as [st1 [Heq Hst1]].
inversion Heq; subst.
assumption.
+ split; assumption.
-
exfalso. clear IHHe.
unfold hoare_triple in Hhoare.
apply Hhoare in He.
+ destruct He as [st' [C _]]. inversion C.
+ split; assumption.
Qed.

Example assert_assume_example:
{{fun st => True}}
ASSUME (X = 1);;
X ::= X + 1;;
ASSERT (X = 2)
{{fun st => True}}.
Proof. hammer_hook "Hoare" "Hoare.HoareAssertAssume.assert_assume_example".
Admitted.

End HoareAssertAssume.



