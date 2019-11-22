From Hammer Require Import Hammer.







Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From PLF Require Import Maps.









Module AExp.



Inductive aexp : Type :=
| ANum (n : nat)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).












Fixpoint aeval (a : aexp) : nat :=
match a with
| ANum n => n
| APlus  a1 a2 => (aeval a1) + (aeval a2)
| AMinus a1 a2 => (aeval a1) - (aeval a2)
| AMult  a1 a2 => (aeval a1) * (aeval a2)
end.

Example test_aeval1:
aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. hammer_hook "Imp" "Imp.AExp.test_aeval1". reflexivity. Qed.



Fixpoint beval (b : bexp) : bool :=
match b with
| BTrue       => true
| BFalse      => false
| BEq a1 a2   => (aeval a1) =? (aeval a2)
| BLe a1 a2   => (aeval a1) <=? (aeval a2)
| BNot b1     => negb (beval b1)
| BAnd b1 b2  => andb (beval b1) (beval b2)
end.






Fixpoint optimize_0plus (a:aexp) : aexp :=
match a with
| ANum n => ANum n
| APlus (ANum 0) e2 => optimize_0plus e2
| APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
| AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
| AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
end.



Example test_optimize_0plus:
optimize_0plus (APlus (ANum 2)
(APlus (ANum 0)
(APlus (ANum 0) (ANum 1))))
= APlus (ANum 2) (ANum 1).
Proof. hammer_hook "Imp" "Imp.AExp.test_optimize_0plus". reflexivity. Qed.



Theorem optimize_0plus_sound: forall a,
aeval (optimize_0plus a) = aeval a.
Proof. hammer_hook "Imp" "Imp.AExp.optimize_0plus_sound".
intros a. induction a.
-  reflexivity.
-  destruct a1 eqn:Ea1.
+  destruct n eqn:En.
*   simpl. apply IHa2.
*  simpl. rewrite IHa2. reflexivity.
+
simpl. simpl in IHa1. rewrite IHa1.
rewrite IHa2. reflexivity.
+
simpl. simpl in IHa1. rewrite IHa1.
rewrite IHa2. reflexivity.
+
simpl. simpl in IHa1. rewrite IHa1.
rewrite IHa2. reflexivity.
-
simpl. rewrite IHa1. rewrite IHa2. reflexivity.
-
simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.
















Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. hammer_hook "Imp" "Imp.AExp.silly1". try reflexivity.  Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof. hammer_hook "Imp" "Imp.AExp.silly2".
intros P HP.
try reflexivity.
apply HP.
Qed.










Lemma foo : forall n, 0 <=? n = true.
Proof. hammer_hook "Imp" "Imp.AExp.foo".
intros.
destruct n.

-  simpl. reflexivity.
-  simpl. reflexivity.
Qed.



Lemma foo' : forall n, 0 <=? n = true.
Proof. hammer_hook "Imp" "Imp.AExp.foo'".
intros.

destruct n;

simpl;

reflexivity.
Qed.



Theorem optimize_0plus_sound': forall a,
aeval (optimize_0plus a) = aeval a.
Proof. hammer_hook "Imp" "Imp.AExp.optimize_0plus_sound'".
intros a.
induction a;

try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).

-  reflexivity.
-
destruct a1 eqn:Ea1;

try (simpl; simpl in IHa1; rewrite IHa1;
rewrite IHa2; reflexivity).

+  destruct n eqn:En;
simpl; rewrite IHa2; reflexivity.   Qed.





Theorem optimize_0plus_sound'': forall a,
aeval (optimize_0plus a) = aeval a.
Proof. hammer_hook "Imp" "Imp.AExp.optimize_0plus_sound''".
intros a.
induction a;

try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);

try reflexivity.

-
destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
rewrite IHa2; reflexivity).
+  destruct n;
simpl; rewrite IHa2; reflexivity. Qed.











Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof. hammer_hook "Imp" "Imp.AExp.In10".
repeat (try (left; reflexivity); right).
Qed.



Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof. hammer_hook "Imp" "Imp.AExp.In10'".
repeat (left; reflexivity).
repeat (right; try (left; reflexivity)).
Qed.





Fixpoint optimize_0plus_b (b : bexp) : bexp
. Admitted.

Theorem optimize_0plus_b_sound : forall b,
beval (optimize_0plus_b b) = beval b.
Proof. hammer_hook "Imp" "Imp.AExp.optimize_0plus_b_sound".
Admitted.











Tactic Notation "simpl_and_try" tactic(c) :=
simpl;
try c.








Example silly_presburger_example : forall m n o p,
m + n <= n + o /\ o + 3 = p + 3 ->
m <= p.
Proof. hammer_hook "Imp" "Imp.AExp.silly_presburger_example".
intros. omega.
Qed.













Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum n :
aevalR (ANum n) n
| E_APlus (e1 e2: aexp) (n1 n2: nat) :
aevalR e1 n1 ->
aevalR e2 n2 ->
aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus (e1 e2: aexp) (n1 n2: nat) :
aevalR e1 n1 ->
aevalR e2 n2 ->
aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult (e1 e2: aexp) (n1 n2: nat) :
aevalR e1 n1 ->
aevalR e2 n2 ->
aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.



Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum n :
aevalR (ANum n) n
| E_APlus (e1 e2: aexp) (n1 n2: nat)
(H1 : aevalR e1 n1)
(H2 : aevalR e2 n2) :
aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus (e1 e2: aexp) (n1 n2: nat)
(H1 : aevalR e1 n1)
(H2 : aevalR e2 n2) :
aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult (e1 e2: aexp) (n1 n2: nat)
(H1 : aevalR e1 n1)
(H2 : aevalR e2 n2) :
aevalR (AMult e1 e2) (n1 * n2).



End TooHardToRead.



Notation "e '\\' n"
:= (aevalR e n)
(at level 50, left associativity)
: type_scope.

End aevalR_first_try.



Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum (n : nat) :
(ANum n) \\ n
| E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
(e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
| E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
(e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
| E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
(e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

where "e '\\' n" := (aevalR e n) : type_scope.
















Definition manual_grade_for_beval_rules : option (nat*string) := None.







Theorem aeval_iff_aevalR : forall a n,
(a \\ n) <-> aeval a = n.
Proof. hammer_hook "Imp" "Imp.AExp.aeval_iff_aevalR".
split.
-
intros H.
induction H; simpl.
+
reflexivity.
+
rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
+
rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
+
rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
-
generalize dependent n.
induction a;
simpl; intros; subst.
+
apply E_ANum.
+
apply E_APlus.
apply IHa1. reflexivity.
apply IHa2. reflexivity.
+
apply E_AMinus.
apply IHa1. reflexivity.
apply IHa2. reflexivity.
+
apply E_AMult.
apply IHa1. reflexivity.
apply IHa2. reflexivity.
Qed.



Theorem aeval_iff_aevalR' : forall a n,
(a \\ n) <-> aeval a = n.
Proof. hammer_hook "Imp" "Imp.AExp.aeval_iff_aevalR'".

split.
-
intros H; induction H; subst; reflexivity.
-
generalize dependent n.
induction a; simpl; intros; subst; constructor;
try apply IHa1; try apply IHa2; reflexivity.
Qed.



Inductive bevalR: bexp -> bool -> Prop :=

.

Lemma beval_iff_bevalR : forall b bv,
bevalR b bv <-> beval b = bv.
Proof. hammer_hook "Imp" "Imp.AExp.beval_iff_bevalR".
Admitted.


End AExp.






Module aevalR_division.



Inductive aexp : Type :=
| ANum (n : nat)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp)
| ADiv (a1 a2 : aexp).



Reserved Notation "e '\\' n"
(at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum (n : nat) :
(ANum n) \\ n
| E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
(a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
| E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
(a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
| E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
(a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
| E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
(a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
(mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.



Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aexp : Type :=
| AAny
| ANum (n : nat)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).



Inductive aevalR : aexp -> nat -> Prop :=
| E_Any (n : nat) :
AAny \\ n
| E_ANum (n : nat) :
(ANum n) \\ n
| E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
(a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
| E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
(a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
| E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
(a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.



















Definition state := total_map nat.






Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).



Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".





Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).








Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.



Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.



Set Printing Coercions.

Print example_bexp.


Unset Printing Coercions.






Fixpoint aeval (st : state) (a : aexp) : nat :=
match a with
| ANum n => n
| AId x => st x
| APlus a1 a2 => (aeval st a1) + (aeval st a2)
| AMinus a1 a2  => (aeval st a1) - (aeval st a2)
| AMult a1 a2 => (aeval st a1) * (aeval st a2)
end.

Fixpoint beval (st : state) (b : bexp) : bool :=
match b with
| BTrue       => true
| BFalse      => false
| BEq a1 a2   => (aeval st a1) =? (aeval st a2)
| BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
| BNot b1     => negb (beval st b1)
| BAnd b1 b2  => andb (beval st b1) (beval st b2)
end.



Definition empty_st := (_ !-> 0).


Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
aeval (X !-> 5) (3 + (X * 2))%imp
= 13.
Proof. hammer_hook "Imp" "Imp.aexp1". reflexivity. Qed.

Example bexp1 :
beval (X !-> 5) (true && ~(X <= 4))%imp
= true.
Proof. hammer_hook "Imp" "Imp.bexp1". reflexivity. Qed.













Inductive com : Type :=
| CSkip
| CAss (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).



Bind Scope imp_scope with com.
Notation "'SKIP'" :=
CSkip : imp_scope.
Notation "x '::=' a" :=
(CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
(CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
(CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
(CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.



Definition fact_in_coq : com :=
(Z ::= X;;
Y ::= 1;;
WHILE ~(Z = 0) DO
Y ::= Y * Z;;
Z ::= Z - 1
END)%imp.






Unset Printing Notations.
Print fact_in_coq.

Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.

Unset Printing Coercions.








Locate "&&".


Locate ";;".


Locate "WHILE".






Locate aexp.







Definition plus2 : com :=
X ::= X + 2.

Definition XtimesYinZ : com :=
Z ::= X * Y.

Definition subtract_slowly_body : com :=
Z ::= Z - 1 ;;
X ::= X - 1.




Definition subtract_slowly : com :=
(WHILE ~(X = 0) DO
subtract_slowly_body
END)%imp.

Definition subtract_3_from_5_slowly : com :=
X ::= 3 ;;
Z ::= 5 ;;
subtract_slowly.




Definition loop : com :=
WHILE true DO
SKIP
END.












Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
: state :=
match c with
| SKIP =>
st
| x ::= a1 =>
(x !-> (aeval st a1) ; st)
| c1 ;; c2 =>
let st' := ceval_fun_no_while st c1 in
ceval_fun_no_while st' c2
| TEST b THEN c1 ELSE c2 FI =>
if (beval st b)
then ceval_fun_no_while st c1
else ceval_fun_no_while st c2
| WHILE b DO c END =>
st
end.
Close Scope imp_scope.



















Reserved Notation "st '=[' c ']=>' st'"
(at level 40).

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

where "st =[ c ]=> st'" := (ceval c st st').



Example ceval_example1:
empty_st =[
X ::= 2;;
TEST X <= 1
THEN Y ::= 3
ELSE Z ::= 4
FI
]=> (Z !-> 4 ; X !-> 2).
Proof. hammer_hook "Imp" "Imp.ceval_example1".

apply E_Seq with (X !-> 2).
-
apply E_Ass. reflexivity.
-
apply E_IfFalse.
reflexivity.
apply E_Ass. reflexivity.
Qed.


Example ceval_example2:
empty_st =[
X ::= 0;; Y ::= 1;; Z ::= 2
]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof. hammer_hook "Imp" "Imp.ceval_example2".
Admitted.




Definition pup_to_n : com
. Admitted.

Theorem pup_to_2_ceval :
(X !-> 2) =[
pup_to_n
]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof. hammer_hook "Imp" "Imp.pup_to_2_ceval".
Admitted.







Theorem ceval_deterministic: forall c st st1 st2,
st =[ c ]=> st1  ->
st =[ c ]=> st2 ->
st1 = st2.
Proof. hammer_hook "Imp" "Imp.ceval_deterministic".
intros c st st1 st2 E1 E2.
generalize dependent st2.
induction E1;
intros st2 E2; inversion E2; subst.
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
rewrite H in H5. discriminate H5.
-
rewrite H in H5. discriminate H5.
-
apply IHE1. assumption.
-
reflexivity.
-
rewrite H in H2. discriminate H2.
-
rewrite H in H4. discriminate H4.
-
assert (st' = st'0) as EQ1.
{  apply IHE1_1; assumption. }
subst st'0.
apply IHE1_2. assumption.  Qed.






Theorem plus2_spec : forall st n st',
st X = n ->
st =[ plus2 ]=> st' ->
st' X = n + 2.
Proof. hammer_hook "Imp" "Imp.plus2_spec".
intros st n st' HX Heval.



inversion Heval. subst. clear Heval. simpl.
apply t_update_eq.  Qed.






Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.



Theorem loop_never_stops : forall st st',
~(st =[ loop ]=> st').
Proof. hammer_hook "Imp" "Imp.loop_never_stops".
intros st st' contra. unfold loop in contra.
remember (WHILE true DO SKIP END)%imp as loopdef
eqn:Heqloopdef.



Admitted.




Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
match c with
| SKIP =>
true
| _ ::= _ =>
true
| c1 ;; c2 =>
andb (no_whiles c1) (no_whiles c2)
| TEST _ THEN ct ELSE cf FI =>
andb (no_whiles ct) (no_whiles cf)
| WHILE _ DO _ END  =>
false
end.
Close Scope imp_scope.



Inductive no_whilesR: com -> Prop :=

.

Theorem no_whiles_eqv:
forall c, no_whiles c = true <-> no_whilesR c.
Proof. hammer_hook "Imp" "Imp.no_whiles_eqv".
Admitted.







Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.







Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.



Fixpoint s_execute (st : state) (stack : list nat)
(prog : list sinstr)
: list nat
. Admitted.

Example s_execute1 :
s_execute empty_st []
[SPush 5; SPush 3; SPush 1; SMinus]
= [2; 5].
Admitted.

Example s_execute2 :
s_execute (X !-> 3) [3;4]
[SPush 4; SLoad X; SMult; SPlus]
= [15; 4].
Admitted.



Fixpoint s_compile (e : aexp) : list sinstr
. Admitted.



Example s_compile1 :
s_compile (X - (2 * Y))%imp
= [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Admitted.




Theorem s_compile_correct : forall (st : state) (e : aexp),
s_execute st [] (s_compile e) = [ aeval st e ].
Proof. hammer_hook "Imp" "Imp.s_compile_correct".
Admitted.






Module BreakImp.


Inductive com : Type :=
| CSkip
| CBreak
| CAss (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
CSkip.
Notation "'BREAK'" :=
CBreak.
Notation "x '::=' a" :=
(CAss x a) (at level 60).
Notation "c1 ;; c2" :=
(CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
(CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
(CIf c1 c2 c3) (at level 80, right associativity).



Inductive result : Type :=
| SContinue
| SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
(at level 40, st' at next level).





Inductive ceval : com -> state -> result -> state -> Prop :=
| E_Skip : forall st,
st =[ CSkip ]=> st / SContinue


where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').



Theorem break_ignore : forall c st st' s,
st =[ BREAK;; c ]=> st' / s ->
st = st'.
Proof. hammer_hook "Imp" "Imp.BreakImp.break_ignore".
Admitted.

Theorem while_continue : forall b c st st' s,
st =[ WHILE b DO c END ]=> st' / s ->
s = SContinue.
Proof. hammer_hook "Imp" "Imp.BreakImp.while_continue".
Admitted.

Theorem while_stops_on_break : forall b c st st',
beval st b = true ->
st =[ c ]=> st' / SBreak ->
st =[ WHILE b DO c END ]=> st' / SContinue.
Proof. hammer_hook "Imp" "Imp.BreakImp.while_stops_on_break".
Admitted.



Theorem while_break_true : forall b c st st',
st =[ WHILE b DO c END ]=> st' / SContinue ->
beval st' b = true ->
exists st'', st'' =[ c ]=> st' / SBreak.
Proof. hammer_hook "Imp" "Imp.BreakImp.while_break_true".
Admitted.



Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
st =[ c ]=> st1 / s1 ->
st =[ c ]=> st2 / s2 ->
st1 = st2 /\ s1 = s2.
Proof. hammer_hook "Imp" "Imp.BreakImp.ceval_deterministic".
Admitted.


End BreakImp.







