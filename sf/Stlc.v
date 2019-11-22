From Hammer Require Import Hammer.





Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

















Module STLC.




Inductive ty : Type :=
| Bool  : ty
| Arrow : ty -> ty -> ty.




Inductive tm : Type :=
| var : string -> tm
| app : tm -> tm -> tm
| abs : string -> ty -> tm -> tm
| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm.





Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition z := "z".

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.



Notation idB :=
(abs x Bool (var x)).



Notation idBB :=
(abs x (Arrow Bool Bool) (var x)).



Notation idBBBB :=
(abs x (Arrow (Arrow Bool Bool)
(Arrow Bool Bool))
(var x)).



Notation k := (abs x Bool (abs y Bool (var x))).



Notation notB := (abs x Bool (test (var x) fls tru)).

















Inductive value : tm -> Prop :=
| v_abs : forall x T t,
value (abs x T t)
| v_tru :
value tru
| v_fls :
value fls.

Hint Constructors value.
















Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
match t with
| var x' =>
if eqb_string x x' then s else t
| abs x' T t1 =>
abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
| app t1 t2 =>
app ([x:=s] t1) ([x:=s] t2)
| tru =>
tru
| fls =>
fls
| test t1 t2 t3 =>
test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
end

where "'[' x ':=' s ']' t" := (subst x s t).









Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
| s_var1 :
substi s x (var x) s

.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
[x:=s]t = t' <-> substi s x t t'.
Proof. hammer_hook "Stlc" "Stlc.STLC.substi_correct".
Admitted.











Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T t12 v2,
value v2 ->
(app (abs x T t12) v2) --> [x:=v2]t12
| ST_App1 : forall t1 t1' t2,
t1 --> t1' ->
app t1 t2 --> app t1' t2
| ST_App2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
app v1 t2 --> app v1  t2'
| ST_TestTru : forall t1 t2,
(test tru t1 t2) --> t1
| ST_TestFls : forall t1 t2,
(test fls t1 t2) --> t2
| ST_Test : forall t1 t1' t2 t3,
t1 --> t1' ->
(test t1 t2 t3) --> (test t1' t2 t3)

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).






Lemma step_example1 :
(app idBB idB) -->* idB.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example1".
eapply multi_step.
apply ST_AppAbs.
apply v_abs.
simpl.
apply multi_refl.  Qed.



Lemma step_example2 :
(app idBB (app idBB idB)) -->* idB.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example2".
eapply multi_step.
apply ST_App2. auto.
apply ST_AppAbs. auto.
eapply multi_step.
apply ST_AppAbs. simpl. auto.
simpl. apply multi_refl.  Qed.



Lemma step_example3 :
app (app idBB notB) tru -->* fls.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example3".
eapply multi_step.
apply ST_App1. apply ST_AppAbs. auto. simpl.
eapply multi_step.
apply ST_AppAbs. auto. simpl.
eapply multi_step.
apply ST_TestTru. apply multi_refl.  Qed.



Lemma step_example4 :
app idBB (app notB tru) -->* fls.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example4".
eapply multi_step.
apply ST_App2. auto.
apply ST_AppAbs. auto. simpl.
eapply multi_step.
apply ST_App2. auto.
apply ST_TestTru.
eapply multi_step.
apply ST_AppAbs. auto. simpl.
apply multi_refl.  Qed.



Lemma step_example1' :
app idBB idB -->* idB.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example1'". normalize.  Qed.

Lemma step_example2' :
app idBB (app idBB idB) -->* idB.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example2'". normalize. Qed.

Lemma step_example3' :
app (app idBB notB) tru -->* fls.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example3'". normalize.  Qed.

Lemma step_example4' :
app idBB (app notB tru) -->* fls.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example4'". normalize.  Qed.



Lemma step_example5 :
app (app idBBBB idBB) idB
-->* idB.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example5".
Admitted.

Lemma step_example5_with_normalize :
app (app idBBBB idBB) idB
-->* idB.
Proof. hammer_hook "Stlc" "Stlc.STLC.step_example5_with_normalize".
Admitted.














Definition context := partial_map ty.






Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Gamma x T,
Gamma x = Some T ->
Gamma |- var x \in T
| T_Abs : forall Gamma x T11 T12 t12,
(x |-> T11 ; Gamma) |- t12 \in T12 ->
Gamma |- abs x T11 t12 \in Arrow T11 T12
| T_App : forall T11 T12 Gamma t1 t2,
Gamma |- t1 \in Arrow T11 T12 ->
Gamma |- t2 \in T11 ->
Gamma |- app t1 t2 \in T12
| T_Tru : forall Gamma,
Gamma |- tru \in Bool
| T_Fls : forall Gamma,
Gamma |- fls \in Bool
| T_Test : forall t1 t2 t3 T Gamma,
Gamma |- t1 \in Bool ->
Gamma |- t2 \in T ->
Gamma |- t3 \in T ->
Gamma |- test t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.




Example typing_example_1 :
empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof. hammer_hook "Stlc" "Stlc.STLC.typing_example_1".
apply T_Abs. apply T_Var. reflexivity.  Qed.



Example typing_example_1' :
empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof. hammer_hook "Stlc" "Stlc.STLC.typing_example_1'". auto.  Qed.



Example typing_example_2 :
empty |-
(abs x Bool
(abs y (Arrow Bool Bool)
(app (var y) (app (var y) (var x))))) \in
(Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof with auto using update_eq. hammer_hook "Stlc" "Stlc.STLC.typing_example_2".
apply T_Abs.
apply T_Abs.
eapply T_App. apply T_Var...
eapply T_App. apply T_Var...
apply T_Var...
Qed.



Example typing_example_2_full :
empty |-
(abs x Bool
(abs y (Arrow Bool Bool)
(app (var y) (app (var y) (var x))))) \in
(Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof. hammer_hook "Stlc" "Stlc.STLC.typing_example_2_full".
Admitted.




Example typing_example_3 :
exists T,
empty |-
(abs x (Arrow Bool Bool)
(abs y (Arrow Bool Bool)
(abs z Bool
(app (var y) (app (var x) (var z)))))) \in
T.
Proof with auto. hammer_hook "Stlc" "Stlc.STLC.typing_example_3".
Admitted.




Example typing_nonexample_1 :
~ exists T,
empty |-
(abs x Bool
(abs y Bool
(app (var x) (var y)))) \in
T.
Proof. hammer_hook "Stlc" "Stlc.STLC.typing_nonexample_1".
intros Hc. inversion Hc.

inversion H. subst. clear H.
inversion H5. subst. clear H5.
inversion H4. subst. clear H4.
inversion H2. subst. clear H2.
inversion H5. subst. clear H5.
inversion H1.  Qed.



Example typing_nonexample_3 :
~ (exists S T,
empty |-
(abs x S
(app (var x) (var x))) \in
T).
Proof. hammer_hook "Stlc" "Stlc.STLC.typing_nonexample_3".
Admitted.


End STLC.


