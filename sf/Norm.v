From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Constructors multi.










Definition manual_grade_for_norm_fail : option (nat*string) := None.





Definition manual_grade_for_norm : option (nat*string) := None.










Inductive ty : Type :=
| Bool : ty
| Arrow : ty -> ty -> ty
| Prod  : ty -> ty -> ty
.

Inductive tm : Type :=

| var : string -> tm
| app : tm -> tm -> tm
| abs : string -> ty -> tm -> tm

| pair : tm -> tm -> tm
| fst : tm -> tm
| snd : tm -> tm

| tru : tm
| fls : tm
| test : tm -> tm -> tm -> tm.





Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
match t with
| var y => if eqb_string x y then s else t
| abs y T t1 =>
abs y T (if eqb_string x y then t1 else (subst x s t1))
| app t1 t2 => app (subst x s t1) (subst x s t2)
| pair t1 t2 => pair (subst x s t1) (subst x s t2)
| fst t1 => fst (subst x s t1)
| snd t1 => snd (subst x s t1)
| tru => tru
| fls => fls
| test t0 t1 t2 =>
test (subst x s t0) (subst x s t1) (subst x s t2)
end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).




Inductive value : tm -> Prop :=
| v_abs : forall x T11 t12,
value (abs x T11 t12)
| v_pair : forall v1 v2,
value v1 ->
value v2 ->
value (pair v1 v2)
| v_tru : value tru
| v_fls : value fls
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T11 t12 v2,
value v2 ->
(app (abs x T11 t12) v2) --> [x:=v2]t12
| ST_App1 : forall t1 t1' t2,
t1 --> t1' ->
(app t1 t2) --> (app t1' t2)
| ST_App2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
(app v1 t2) --> (app v1 t2')

| ST_Pair1 : forall t1 t1' t2,
t1 --> t1' ->
(pair t1 t2) --> (pair t1' t2)
| ST_Pair2 : forall v1 t2 t2',
value v1 ->
t2 --> t2' ->
(pair v1 t2) --> (pair v1 t2')
| ST_Fst : forall t1 t1',
t1 --> t1' ->
(fst t1) --> (fst t1')
| ST_FstPair : forall v1 v2,
value v1 ->
value v2 ->
(fst (pair v1 v2)) --> v1
| ST_Snd : forall t1 t1',
t1 --> t1' ->
(snd t1) --> (snd t1')
| ST_SndPair : forall v1 v2,
value v1 ->
value v2 ->
(snd (pair v1 v2)) --> v2

| ST_TestTrue : forall t1 t2,
(test tru t1 t2) --> t1
| ST_TestFalse : forall t1 t2,
(test fls t1 t2) --> t2
| ST_Test : forall t0 t0' t1 t2,
t0 --> t0' ->
(test t0 t1 t2) --> (test t0' t1 t2)

where "t1 '-->' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof with eauto. hammer_hook "Norm" "Norm.value__normal".
intros t H; induction H; intros [t' ST]; inversion ST...
Qed.




Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=

| T_Var : forall Gamma x T,
Gamma x = Some T ->
has_type Gamma (var x) T
| T_Abs : forall Gamma x T11 T12 t12,
has_type (update Gamma x T11) t12 T12 ->
has_type Gamma (abs x T11 t12) (Arrow T11 T12)
| T_App : forall T1 T2 Gamma t1 t2,
has_type Gamma t1 (Arrow T1 T2) ->
has_type Gamma t2 T1 ->
has_type Gamma (app t1 t2) T2

| T_Pair : forall Gamma t1 t2 T1 T2,
has_type Gamma t1 T1 ->
has_type Gamma t2 T2 ->
has_type Gamma (pair t1 t2) (Prod T1 T2)
| T_Fst : forall Gamma t T1 T2,
has_type Gamma t (Prod T1 T2) ->
has_type Gamma (fst t) T1
| T_Snd : forall Gamma t T1 T2,
has_type Gamma t (Prod T1 T2) ->
has_type Gamma (snd t) T2

| T_True : forall Gamma,
has_type Gamma tru Bool
| T_False : forall Gamma,
has_type Gamma fls Bool
| T_Test : forall Gamma t0 t1 t2 T,
has_type Gamma t0 Bool ->
has_type Gamma t1 T ->
has_type Gamma t2 T ->
has_type Gamma (test t0 t1 t2) T
.

Hint Constructors has_type.

Hint Extern 2 (has_type _ (app _ _) _) => eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.




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

| afi_pair1 : forall x t1 t2,
appears_free_in x t1 ->
appears_free_in x (pair t1 t2)
| afi_pair2 : forall x t1 t2,
appears_free_in x t2 ->
appears_free_in x (pair t1 t2)
| afi_fst : forall x t,
appears_free_in x t ->
appears_free_in x (fst t)
| afi_snd : forall x t,
appears_free_in x t ->
appears_free_in x (snd t)

| afi_test0 : forall x t0 t1 t2,
appears_free_in x t0 ->
appears_free_in x (test t0 t1 t2)
| afi_test1 : forall x t0 t1 t2,
appears_free_in x t1 ->
appears_free_in x (test t0 t1 t2)
| afi_test2 : forall x t0 t1 t2,
appears_free_in x t2 ->
appears_free_in x (test t0 t1 t2)
.

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t S,
has_type Gamma t S  ->
(forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
has_type Gamma' t S.
Proof with eauto. hammer_hook "Norm" "Norm.context_invariance".
intros. generalize dependent Gamma'.
induction H;
intros Gamma' Heqv...
-
apply T_Var... rewrite <- Heqv...
-
apply T_Abs... apply IHhas_type. intros y Hafi.
unfold update, t_update. destruct (eqb_stringP x y)...
-
apply T_Pair...
-
eapply T_Test...
Qed.

Lemma free_in_context : forall x t T Gamma,
appears_free_in x t ->
has_type Gamma t T ->
exists T', Gamma x = Some T'.
Proof with eauto. hammer_hook "Norm" "Norm.free_in_context".
intros x t T Gamma Hafi Htyp.
induction Htyp; inversion Hafi; subst...
-
destruct IHHtyp as [T' Hctx]... exists T'.
unfold update, t_update in Hctx.
rewrite false_eqb_string in Hctx...
Qed.

Corollary typable_empty__closed : forall t T,
has_type empty t T  ->
closed t.
Proof. hammer_hook "Norm" "Norm.typable_empty__closed".
intros. unfold closed. intros x H1.
destruct (free_in_context _ _ _ _ H1 H) as [T' C].
inversion C.  Qed.




Lemma substitution_preserves_typing : forall Gamma x U v t S,
has_type (update Gamma x U) t S  ->
has_type empty v U   ->
has_type Gamma ([x:=v]t) S.
Proof with eauto. hammer_hook "Norm" "Norm.substitution_preserves_typing".

intros Gamma x U v t S Htypt Htypv.
generalize dependent Gamma. generalize dependent S.

induction t;
intros S Gamma Htypt; simpl; inversion Htypt; subst...
-
simpl. rename s into y.

unfold update, t_update in H1.
destruct (eqb_stringP x y).
+

subst.
inversion H1; subst. clear H1.
eapply context_invariance...
intros x Hcontra.
destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
inversion HT'.
+

apply T_Var...
-
rename s into y. rename t into T11.

apply T_Abs...
destruct (eqb_stringP x y).
+

eapply context_invariance...
subst.
intros x Hafi. unfold update, t_update.
destruct (eqb_string y x)...
+

apply IHt. eapply context_invariance...
intros z Hafi. unfold update, t_update.
destruct (eqb_stringP y z)...
subst. rewrite false_eqb_string...
Qed.

Theorem preservation : forall t t' T,
has_type empty t T  ->
t --> t'  ->
has_type empty t' T.
Proof with eauto. hammer_hook "Norm" "Norm.preservation".
intros t t' T HT.

remember (@empty ty) as Gamma. generalize dependent HeqGamma.
generalize dependent t'.

induction HT;
intros t' HeqGamma HE; subst; inversion HE; subst...
-

inversion HE; subst...
+

apply substitution_preserves_typing with T1...
inversion HT1...
-
inversion HT...
-
inversion HT...
Qed.




Lemma step_deterministic :
deterministic step.
Proof with eauto. hammer_hook "Norm" "Norm.step_deterministic".
unfold deterministic.
intros t t' t'' E1 E2.
generalize dependent t''.
induction E1; intros t'' E2; inversion E2; subst; clear E2...

- inversion H3.
- exfalso; apply value__normal in H...

- inversion E1.
-  f_equal...
- exfalso; apply value__normal in H1...

- exfalso; apply value__normal in H3...
- exfalso; apply value__normal in H...
- f_equal...

- f_equal...
- exfalso; apply value__normal in H1...

- exfalso; apply value__normal in H...
- f_equal...

- f_equal...
- exfalso.
inversion E1; subst.
+ apply value__normal in H0...
+ apply value__normal in H1...

- exfalso.
inversion H2; subst.
+ apply value__normal in H...
+ apply value__normal in H0...

- f_equal...
- exfalso.
inversion E1; subst.
+ apply value__normal in H0...
+ apply value__normal in H1...

- exfalso.
inversion H2; subst.
+ apply value__normal in H...
+ apply value__normal in H0...
-
inversion H3.
-
inversion H3.

- inversion E1.
- inversion E1.
- f_equal...
Qed.






Definition halts  (t:tm) : Prop :=  exists t', t -->* t' /\  value t'.



Lemma value_halts : forall v, value v -> halts v.
Proof. hammer_hook "Norm" "Norm.value_halts".
intros v H. unfold halts.
exists v. split.
apply multi_refl.
assumption.
Qed.





Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
has_type empty t T /\ halts t /\
(match T with
| Bool  => True
| Arrow T1 T2 => (forall s, R T1 s -> R T2 (app t s))


| Prod T1 T2 => False
end).



Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof. hammer_hook "Norm" "Norm.R_halts".
intros. destruct T; unfold R in H; inversion H; inversion H1;  assumption.
Qed.

Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
Proof. hammer_hook "Norm" "Norm.R_typable_empty".
intros. destruct T; unfold R in H; inversion H; inversion H1; assumption.
Qed.








Lemma step_preserves_halting : forall t t', (t --> t') -> (halts t <-> halts t').
Proof. hammer_hook "Norm" "Norm.step_preserves_halting".
intros t t' ST.  unfold halts.
split.
-
intros [t'' [STM V]].
inversion STM; subst.
exfalso.  apply value__normal in V. unfold normal_form in V. apply V. exists t'. auto.
rewrite (step_deterministic _ _ _ ST H). exists t''. split; assumption.
-
intros [t'0 [STM V]].
exists t'0. split; eauto.
Qed.



Lemma step_preserves_R : forall T t t', (t --> t') -> R T t -> R T t'.
Proof. hammer_hook "Norm" "Norm.step_preserves_R".
induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
destruct Rt as [typable_empty_t [halts_t RRt]].

split. eapply preservation; eauto.
split. apply (step_preserves_halting _ _ E); eauto.
auto.

split. eapply preservation; eauto.
split. apply (step_preserves_halting _ _ E); eauto.
intros.
eapply IHT2.
apply  ST_App1. apply E.
apply RRt; auto.
Admitted.



Lemma multistep_preserves_R : forall T t t',
(t -->* t') -> R T t -> R T t'.
Proof. hammer_hook "Norm" "Norm.multistep_preserves_R".
intros T t t' STM; induction STM; intros.
assumption.
apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.



Lemma step_preserves_R' : forall T t t',
has_type empty t T -> (t --> t') -> R T t' -> R T t.
Proof. hammer_hook "Norm" "Norm.step_preserves_R'".
Admitted.

Lemma multistep_preserves_R' : forall T t t',
has_type empty t T -> (t -->* t') -> R T t' -> R T t.
Proof. hammer_hook "Norm" "Norm.multistep_preserves_R'".
intros T t t' HT STM.
induction STM; intros.
assumption.
eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
eapply preservation;  eauto. auto.
Qed.











Definition env := list (string * tm).

Fixpoint msubst (ss:env) (t:tm) {struct ss} : tm :=
match ss with
| nil => t
| ((x,s)::ss') => msubst ss' ([x:=s]t)
end.



Definition tass := list (string * ty).

Fixpoint mupdate (Gamma : context) (xts : tass) :=
match xts with
| nil => Gamma
| ((x,v)::xts') => update (mupdate Gamma xts') x v
end.



Fixpoint lookup {X:Set} (k : string) (l : list (string * X)) {struct l}
: option X :=
match l with
| nil => None
| (j,x) :: l' =>
if eqb_string j k then Some x else lookup k l'
end.

Fixpoint drop {X:Set} (n:string) (nxs:list (string * X)) {struct nxs}
: list (string * X) :=
match nxs with
| nil => nil
| ((n',x)::nxs') =>
if eqb_string n' n then drop n nxs'
else (n',x)::(drop n nxs')
end.



Inductive instantiation :  tass -> env -> Prop :=
| V_nil :
instantiation nil nil
| V_cons : forall x T v c e,
value v -> R T v ->
instantiation c e ->
instantiation ((x,T)::c) ((x,v)::e).








Lemma vacuous_substitution : forall  t x,
~ appears_free_in x t  ->
forall t', [x:=t']t = t.
Proof with eauto. hammer_hook "Norm" "Norm.vacuous_substitution".
Admitted.

Lemma subst_closed: forall t,
closed t  ->
forall x t', [x:=t']t = t.
Proof. hammer_hook "Norm" "Norm.subst_closed".
intros. apply vacuous_substitution. apply H.  Qed.

Lemma subst_not_afi : forall t x v,
closed v ->  ~ appears_free_in x ([x:=v]t).
Proof with eauto. hammer_hook "Norm" "Norm.subst_not_afi".
unfold closed, not.
induction t; intros x v P A; simpl in A.
-
destruct (eqb_stringP x s)...
inversion A; subst. auto.
-
inversion A; subst...
-
destruct (eqb_stringP x s)...
+ inversion A; subst...
+ inversion A; subst...
-
inversion A; subst...
-
inversion A; subst...
-
inversion A; subst...
-
inversion A.
-
inversion A.
-
inversion A; subst...
Qed.

Lemma duplicate_subst : forall t' x t v,
closed v -> [x:=t]([x:=v]t') = [x:=v]t'.
Proof. hammer_hook "Norm" "Norm.duplicate_subst".
intros. eapply vacuous_substitution. apply subst_not_afi.  auto.
Qed.

Lemma swap_subst : forall t x x1 v v1,
x <> x1 ->
closed v -> closed v1 ->
[x1:=v1]([x:=v]t) = [x:=v]([x1:=v1]t).
Proof with eauto. hammer_hook "Norm" "Norm.swap_subst".
induction t; intros; simpl.
-
destruct (eqb_stringP x s); destruct (eqb_stringP x1 s).
+ subst. exfalso...
+ subst. simpl. rewrite <- eqb_string_refl. apply subst_closed...
+ subst. simpl. rewrite <- eqb_string_refl. rewrite subst_closed...
+ simpl. rewrite false_eqb_string... rewrite false_eqb_string...
Admitted.




Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof. hammer_hook "Norm" "Norm.msubst_closed".
induction ss.
reflexivity.
destruct a. simpl. rewrite subst_closed; assumption.
Qed.



Fixpoint closed_env (env:env) {struct env} :=
match env with
| nil => True
| (x,t)::env' => closed t /\ closed_env env'
end.



Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
msubst env ([x:=v]t) = [x:=v](msubst (drop x env) t).
Proof. hammer_hook "Norm" "Norm.subst_msubst".
induction env0; intros; auto.
destruct a. simpl.
inversion H0. fold closed_env in H2.
destruct (eqb_stringP s x).
- subst. rewrite duplicate_subst; auto.
- simpl. rewrite swap_subst; eauto.
Qed.

Lemma msubst_var:  forall ss x, closed_env ss ->
msubst ss (var x) =
match lookup x ss with
| Some t => t
| None => var x
end.
Proof. hammer_hook "Norm" "Norm.msubst_var".
induction ss; intros.
reflexivity.
destruct a.
simpl. destruct (eqb_string s x).
apply msubst_closed. inversion H; auto.
apply IHss. inversion H; auto.
Qed.

Lemma msubst_abs: forall ss x T t,
msubst ss (abs x T t) = abs x T (msubst (drop x ss) t).
Proof. hammer_hook "Norm" "Norm.msubst_abs".
induction ss; intros.
reflexivity.
destruct a.
simpl. destruct (eqb_string s x); simpl; auto.
Qed.

Lemma msubst_app : forall ss t1 t2, msubst ss (app t1 t2) = app (msubst ss t1) (msubst ss t2).
Proof. hammer_hook "Norm" "Norm.msubst_app".
induction ss; intros.
reflexivity.
destruct a.
simpl. rewrite <- IHss. auto.
Qed.










Lemma mupdate_lookup : forall (c : tass) (x:string),
lookup x c = (mupdate empty c) x.
Proof. hammer_hook "Norm" "Norm.mupdate_lookup".
induction c; intros.
auto.
destruct a. unfold lookup, mupdate, update, t_update. destruct (eqb_string s x); auto.
Qed.

Lemma mupdate_drop : forall (c: tass) Gamma x x',
mupdate Gamma (drop x c) x'
= if eqb_string x x' then Gamma x' else mupdate Gamma c x'.
Proof. hammer_hook "Norm" "Norm.mupdate_drop".
induction c; intros.
- destruct (eqb_stringP x x'); auto.
- destruct a. simpl.
destruct (eqb_stringP s x).
+ subst. rewrite IHc.
unfold update, t_update. destruct (eqb_stringP x x'); auto.
+ simpl. unfold update, t_update. destruct (eqb_stringP s x'); auto.
subst. rewrite false_eqb_string; congruence.
Qed.






Lemma instantiation_domains_match: forall {c} {e},
instantiation c e ->
forall {x} {T},
lookup x c = Some T -> exists t, lookup x e = Some t.
Proof. hammer_hook "Norm" "Norm.instantiation_domains_match".
intros c e V. induction V; intros x0 T0 C.
solve_by_invert.
simpl in *.
destruct (eqb_string x x0); eauto.
Qed.

Lemma instantiation_env_closed : forall c e,
instantiation c e -> closed_env e.
Proof. hammer_hook "Norm" "Norm.instantiation_env_closed".
intros c e V; induction V; intros.
econstructor.
unfold closed_env. fold closed_env.
split.  eapply typable_empty__closed. eapply R_typable_empty. eauto.
auto.
Qed.

Lemma instantiation_R : forall c e,
instantiation c e ->
forall x t T,
lookup x c = Some T ->
lookup x e = Some t -> R T t.
Proof. hammer_hook "Norm" "Norm.instantiation_R".
intros c e V. induction V; intros x' t' T' G E.
solve_by_invert.
unfold lookup in *.  destruct (eqb_string x x').
inversion G; inversion E; subst.  auto.
eauto.
Qed.

Lemma instantiation_drop : forall c env,
instantiation c env ->
forall x, instantiation (drop x c) (drop x env).
Proof. hammer_hook "Norm" "Norm.instantiation_drop".
intros c e V. induction V.
intros.  simpl.  constructor.
intros. unfold drop. destruct (eqb_string x x0); auto. constructor; eauto.
Qed.






Lemma multistep_App2 : forall v t t',
value v -> (t -->* t') -> (app v t) -->* (app v t').
Proof. hammer_hook "Norm" "Norm.multistep_App2".
intros v t t' V STM. induction STM.
apply multi_refl.
eapply multi_step.
apply ST_App2; eauto.  auto.
Qed.








Lemma msubst_preserves_typing : forall c e,
instantiation c e ->
forall Gamma t S, has_type (mupdate Gamma c) t S ->
has_type Gamma (msubst e t) S.
Proof. hammer_hook "Norm" "Norm.msubst_preserves_typing".
induction 1; intros.
simpl in H. simpl. auto.
simpl in H2.  simpl.
apply IHinstantiation.
eapply substitution_preserves_typing; eauto.
apply (R_typable_empty H0).
Qed.



Lemma msubst_R : forall c env t T,
has_type (mupdate empty c) t T ->
instantiation c env ->
R T (msubst env t).
Proof. hammer_hook "Norm" "Norm.msubst_R".
intros c env0 t T HT V.
generalize dependent env0.

remember (mupdate empty c) as Gamma.
assert (forall x, Gamma x = lookup x c).
intros. rewrite HeqGamma. rewrite mupdate_lookup. auto.
clear HeqGamma.
generalize dependent c.
induction HT; intros.

-
rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
eapply instantiation_R; eauto.
rewrite msubst_var.  rewrite P. auto. eapply instantiation_env_closed; eauto.

-
rewrite msubst_abs.

assert (WT: has_type empty (abs x T11 (msubst (drop x env0) t12)) (Arrow T11 T12)).
{ eapply T_Abs. eapply msubst_preserves_typing.
{ eapply instantiation_drop; eauto. }
eapply context_invariance.
{ apply HT. }
intros.
unfold update, t_update. rewrite mupdate_drop. destruct (eqb_stringP x x0).
+ auto.
+ rewrite H.
clear - c n. induction c.
simpl.  rewrite false_eqb_string; auto.
simpl. destruct a.  unfold update, t_update.
destruct (eqb_string s x0); auto. }
unfold R. fold R. split.
auto.
split. apply value_halts. apply v_abs.
intros.
destruct (R_halts H0) as [v [P Q]].
pose proof (multistep_preserves_R _ _ _ P H0).
apply multistep_preserves_R' with (msubst ((x,v)::env0) t12).
eapply T_App. eauto.
apply R_typable_empty; auto.
eapply multi_trans.  eapply multistep_App2; eauto.
eapply multi_R.
simpl.  rewrite subst_msubst.
eapply ST_AppAbs; eauto.
eapply typable_empty__closed.
apply (R_typable_empty H1).
eapply instantiation_env_closed; eauto.
eapply (IHHT ((x,T11)::c)).
intros. unfold update, t_update, lookup. destruct (eqb_string x x0); auto.
constructor; auto.

-
rewrite msubst_app.
destruct (IHHT1 c H env0 V) as [_ [_ P1]].
pose proof (IHHT2 c H env0 V) as P2.  fold R in P1.  auto.

Admitted.






Theorem normalization : forall t T, has_type empty t T -> halts t.
Proof. hammer_hook "Norm" "Norm.normalization".
intros.
replace t with (msubst nil t) by reflexivity.
apply (@R_halts T).
apply (msubst_R nil); eauto.
eapply V_nil.
Qed.



