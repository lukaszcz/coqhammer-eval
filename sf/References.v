From Hammer Require Import Hammer.





Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From Coq Require Import Lists.List.
Import ListNotations.











Module STLCRef.










Inductive ty : Type :=
| Nat   : ty
| Unit  : ty
| Arrow : ty -> ty -> ty
| Ref   : ty -> ty.






Inductive tm  : Type :=

| var    : string -> tm
| app    : tm -> tm -> tm
| abs    : string -> ty -> tm -> tm
| const  : nat -> tm
| scc    : tm -> tm
| prd    : tm -> tm
| mlt    : tm -> tm -> tm
| test0  : tm -> tm -> tm -> tm

| unit   : tm
| ref    : tm -> tm
| deref  : tm -> tm
| assign : tm -> tm -> tm
| loc    : nat -> tm.















Inductive value : tm -> Prop :=
| v_abs  : forall x T t,
value (abs x T t)
| v_nat : forall n,
value (const n)
| v_unit :
value unit
| v_loc : forall l,
value (loc l).

Hint Constructors value.



Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
match t with
| var x'       =>
if eqb_string x x' then s else t
| app t1 t2    =>
app (subst x s t1) (subst x s t2)
| abs x' T t1  =>
if eqb_string x x' then t else abs x' T (subst x s t1)
| const n        =>
t
| scc t1      =>
scc (subst x s t1)
| prd t1      =>
prd (subst x s t1)
| mlt t1 t2   =>
mlt (subst x s t1) (subst x s t2)
| test0 t1 t2 t3 =>
test0 (subst x s t1) (subst x s t2) (subst x s t3)
| unit         =>
t
| ref t1       =>
ref (subst x s t1)
| deref t1     =>
deref (subst x s t1)
| assign t1 t2 =>
assign (subst x s t1) (subst x s t2)
| loc _        =>
t
end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).









Definition tseq t1 t2 :=
app (abs "x" Unit t2) t1.


































Definition manual_grade_for_compact_update : option (nat*string) := None.

















Definition manual_grade_for_type_safety_violation : option (nat*string) := None.















Definition store := list tm.



Definition store_lookup (n:nat) (st:store) :=
nth n st unit.



Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
match l with
| nil    => nil
| h :: t =>
match n with
| O    => x :: t
| S n' => h :: replace n' x t
end
end.



Lemma replace_nil : forall A n (x:A),
replace n x nil = nil.
Proof. hammer_hook "References" "References.STLCRef.replace_nil".
destruct n; auto.
Qed.

Lemma length_replace : forall A n x (l:list A),
length (replace n x l) = length l.
Proof with auto. hammer_hook "References" "References.STLCRef.length_replace".
intros A n x l. generalize dependent n.
induction l; intros n.
destruct n...
destruct n...
simpl. rewrite IHl...
Qed.

Lemma lookup_replace_eq : forall l t st,
l < length st ->
store_lookup l (replace l t st) = t.
Proof with auto. hammer_hook "References" "References.STLCRef.lookup_replace_eq".
intros l t st.
unfold store_lookup.
generalize dependent l.
induction st as [|t' st']; intros l Hlen.
-
inversion Hlen.
-
destruct l; simpl...
apply IHst'. simpl in Hlen. omega.
Qed.

Lemma lookup_replace_neq : forall l1 l2 t st,
l1 <> l2 ->
store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto. hammer_hook "References" "References.STLCRef.lookup_replace_neq".
unfold store_lookup.
induction l1 as [|l1']; intros l2 t st Hneq.
-
destruct st.
+  rewrite replace_nil...
+  destruct l2... contradict Hneq...
-
destruct st as [|t2 st2].
+  destruct l2...
+
destruct l2...
simpl; apply IHl1'...
Qed.






Reserved Notation "t1 '/' st1 '-->' t2 '/' st2"
(at level 40, st1 at level 39, t2 at level 39).

Import ListNotations.

Inductive step : tm * store -> tm * store -> Prop :=
| ST_AppAbs : forall x T t12 v2 st,
value v2 ->
app (abs x T t12) v2 / st --> [x:=v2]t12 / st
| ST_App1 : forall t1 t1' t2 st st',
t1 / st --> t1' / st' ->
app t1 t2 / st --> app t1' t2 / st'
| ST_App2 : forall v1 t2 t2' st st',
value v1 ->
t2 / st --> t2' / st' ->
app v1 t2 / st --> app v1 t2'/ st'
| ST_SuccNat : forall n st,
scc (const n) / st --> const (S n) / st
| ST_Succ : forall t1 t1' st st',
t1 / st --> t1' / st' ->
scc t1 / st --> scc t1' / st'
| ST_PredNat : forall n st,
prd (const n) / st --> const (pred n) / st
| ST_Pred : forall t1 t1' st st',
t1 / st --> t1' / st' ->
prd t1 / st --> prd t1' / st'
| ST_MultNats : forall n1 n2 st,
mlt (const n1) (const n2) / st --> const (mult n1 n2) / st
| ST_Mult1 : forall t1 t2 t1' st st',
t1 / st --> t1' / st' ->
mlt t1 t2 / st --> mlt t1' t2 / st'
| ST_Mult2 : forall v1 t2 t2' st st',
value v1 ->
t2 / st --> t2' / st' ->
mlt v1 t2 / st --> mlt v1 t2' / st'
| ST_If0 : forall t1 t1' t2 t3 st st',
t1 / st --> t1' / st' ->
test0 t1 t2 t3 / st --> test0 t1' t2 t3 / st'
| ST_If0_Zero : forall t2 t3 st,
test0 (const 0) t2 t3 / st --> t2 / st
| ST_If0_Nonzero : forall n t2 t3 st,
test0 (const (S n)) t2 t3 / st --> t3 / st
| ST_RefValue : forall v1 st,
value v1 ->
ref v1 / st --> loc (length st) / (st ++ v1::nil)
| ST_Ref : forall t1 t1' st st',
t1 / st --> t1' / st' ->
ref t1 /  st --> ref t1' /  st'
| ST_DerefLoc : forall st l,
l < length st ->
deref (loc l) / st --> store_lookup l st / st
| ST_Deref : forall t1 t1' st st',
t1 / st --> t1' / st' ->
deref t1 / st --> deref t1' / st'
| ST_Assign : forall v2 l st,
value v2 ->
l < length st ->
assign (loc l) v2 / st --> unit / replace l v2 st
| ST_Assign1 : forall t1 t1' t2 st st',
t1 / st --> t1' / st' ->
assign t1 t2 / st --> assign t1' t2 / st'
| ST_Assign2 : forall v1 t2 t2' st st',
value v1 ->
t2 / st --> t2' / st' ->
assign v1 t2 / st --> assign v1 t2' / st'

where "t1 '/' st1 '-->' t2 '/' st2" := (step (t1,st1) (t2,st2)).



Hint Constructors step.

Definition multistep := (multi step).
Notation "t1 '/' st '-->*' t2 '/' st'" :=
(multistep (t1,st) (t2,st'))
(at level 40, st at level 39, t2 at level 39).






Definition context := partial_map ty.









Definition manual_grade_for_cyclic_store : option (nat*string) := None.




Definition store_ty := list ty.



Definition store_Tlookup (n:nat) (ST:store_ty) :=
nth n ST Unit.










Reserved Notation "Gamma ';' ST '|-' t '\in' T" (at level 40).

Inductive has_type : context -> store_ty -> tm -> ty -> Prop :=
| T_Var : forall Gamma ST x T,
Gamma x = Some T ->
Gamma; ST |- (var x) \in T
| T_Abs : forall Gamma ST x T11 T12 t12,
(update Gamma x T11); ST |- t12 \in T12 ->
Gamma; ST |- (abs x T11 t12) \in (Arrow T11 T12)
| T_App : forall T1 T2 Gamma ST t1 t2,
Gamma; ST |- t1 \in (Arrow T1 T2) ->
Gamma; ST |- t2 \in T1 ->
Gamma; ST |- (app t1 t2) \in T2
| T_Nat : forall Gamma ST n,
Gamma; ST |- (const n) \in Nat
| T_Succ : forall Gamma ST t1,
Gamma; ST |- t1 \in Nat ->
Gamma; ST |- (scc t1) \in Nat
| T_Pred : forall Gamma ST t1,
Gamma; ST |- t1 \in Nat ->
Gamma; ST |- (prd t1) \in Nat
| T_Mult : forall Gamma ST t1 t2,
Gamma; ST |- t1 \in Nat ->
Gamma; ST |- t2 \in Nat ->
Gamma; ST |- (mlt t1 t2) \in Nat
| T_If0 : forall Gamma ST t1 t2 t3 T,
Gamma; ST |- t1 \in Nat ->
Gamma; ST |- t2 \in T ->
Gamma; ST |- t3 \in T ->
Gamma; ST |- (test0 t1 t2 t3) \in T
| T_Unit : forall Gamma ST,
Gamma; ST |- unit \in Unit
| T_Loc : forall Gamma ST l,
l < length ST ->
Gamma; ST |- (loc l) \in (Ref (store_Tlookup l ST))
| T_Ref : forall Gamma ST t1 T1,
Gamma; ST |- t1 \in T1 ->
Gamma; ST |- (ref t1) \in (Ref T1)
| T_Deref : forall Gamma ST t1 T11,
Gamma; ST |- t1 \in (Ref T11) ->
Gamma; ST |- (deref t1) \in T11
| T_Assign : forall Gamma ST t1 t2 T11,
Gamma; ST |- t1 \in (Ref T11) ->
Gamma; ST |- t2 \in T11 ->
Gamma; ST |- (assign t1 t2) \in Unit

where "Gamma ';' ST '|-' t '\in' T" := (has_type Gamma ST t T).

Hint Constructors has_type.













Theorem preservation_wrong1 : forall ST T t st t' st',
empty; ST |- t \in T ->
t / st --> t' / st' ->
empty; ST |- t' \in T.
Abort.



Definition store_well_typed (ST:store_ty) (st:store) :=
length ST = length st /\
(forall l, l < length st ->
empty; ST |- (store_lookup l st) \in (store_Tlookup l ST)).










Definition manual_grade_for_store_not_unique : option (nat*string) := None.




Theorem preservation_wrong2 : forall ST T t st t' st',
empty; ST |- t \in T ->
t / st --> t' / st' ->
store_well_typed ST st ->
empty; ST |- t' \in T.
Abort.








Inductive extends : store_ty -> store_ty -> Prop :=
| extends_nil  : forall ST',
extends ST' nil
| extends_cons : forall x ST' ST,
extends ST' ST ->
extends (x::ST') (x::ST).

Hint Constructors extends.



Lemma extends_lookup : forall l ST ST',
l < length ST ->
extends ST' ST ->
store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto. hammer_hook "References" "References.STLCRef.extends_lookup".
intros l ST ST' Hlen H.
generalize dependent ST'. generalize dependent l.
induction ST as [|a ST2]; intros l Hlen ST' HST'.
-  inversion Hlen.
-  unfold store_Tlookup in *.
destruct ST'.
+  inversion HST'.
+
inversion HST'; subst.
destruct l as [|l'].
*  auto.
*  simpl. apply IHST2...
simpl in Hlen; omega.
Qed.



Lemma length_extends : forall l ST ST',
l < length ST ->
extends ST' ST ->
l < length ST'.
Proof with eauto. hammer_hook "References" "References.STLCRef.length_extends".
intros. generalize dependent l. induction H0; intros l Hlen.
inversion Hlen.
simpl in *.
destruct l; try omega.
apply lt_n_S. apply IHextends. omega.
Qed.



Lemma extends_app : forall ST T,
extends (ST ++ T) ST.
Proof with auto. hammer_hook "References" "References.STLCRef.extends_app".
induction ST; intros T...
simpl...
Qed.

Lemma extends_refl : forall ST,
extends ST ST.
Proof. hammer_hook "References" "References.STLCRef.extends_refl".
induction ST; auto.
Qed.






Definition preservation_theorem := forall ST t t' T st st',
empty; ST |- t \in T ->
store_well_typed ST st ->
t / st --> t' / st' ->
exists ST',
(extends ST' ST /\
empty; ST' |- t' \in T /\
store_well_typed ST' st').








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
| afi_succ : forall x t1,
appears_free_in x t1 ->
appears_free_in x (scc t1)
| afi_pred : forall x t1,
appears_free_in x t1 ->
appears_free_in x (prd t1)
| afi_mult1 : forall x t1 t2,
appears_free_in x t1 ->
appears_free_in x (mlt t1 t2)
| afi_mult2 : forall x t1 t2,
appears_free_in x t2 ->
appears_free_in x (mlt t1 t2)
| afi_if0_1 : forall x t1 t2 t3,
appears_free_in x t1 ->
appears_free_in x (test0 t1 t2 t3)
| afi_if0_2 : forall x t1 t2 t3,
appears_free_in x t2 ->
appears_free_in x (test0 t1 t2 t3)
| afi_if0_3 : forall x t1 t2 t3,
appears_free_in x t3 ->
appears_free_in x (test0 t1 t2 t3)
| afi_ref : forall x t1,
appears_free_in x t1 -> appears_free_in x (ref t1)
| afi_deref : forall x t1,
appears_free_in x t1 -> appears_free_in x (deref t1)
| afi_assign1 : forall x t1 t2,
appears_free_in x t1 -> appears_free_in x (assign t1 t2)
| afi_assign2 : forall x t1 t2,
appears_free_in x t2 -> appears_free_in x (assign t1 t2).

Hint Constructors appears_free_in.

Lemma free_in_context : forall x t T Gamma ST,
appears_free_in x t ->
Gamma; ST |- t \in T ->
exists T', Gamma x = Some T'.
Proof with eauto. hammer_hook "References" "References.STLCRef.free_in_context".
intros. generalize dependent Gamma. generalize dependent T.
induction H;
intros; (try solve [ inversion H0; subst; eauto ]).
-
inversion H1; subst.
apply IHappears_free_in in H8.
rewrite update_neq in H8; assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' ST t T,
Gamma; ST |- t \in T ->
(forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
Gamma'; ST |- t \in T.
Proof with eauto. hammer_hook "References" "References.STLCRef.context_invariance".
intros.
generalize dependent Gamma'.
induction H; intros...
-
apply T_Var. symmetry. rewrite <- H...
-
apply T_Abs. apply IHhas_type; intros.
unfold update, t_update.
destruct (eqb_stringP x x0)...
-
eapply T_App.
apply IHhas_type1...
apply IHhas_type2...
-
eapply T_Mult.
apply IHhas_type1...
apply IHhas_type2...
-
eapply T_If0.
apply IHhas_type1...
apply IHhas_type2...
apply IHhas_type3...
-
eapply T_Assign.
apply IHhas_type1...
apply IHhas_type2...
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x s S t T,
empty; ST |- s \in S ->
(update Gamma x S); ST |- t \in T ->
Gamma; ST |- ([x:=s]t) \in T.
Proof with eauto. hammer_hook "References" "References.STLCRef.substitution_preserves_typing".
intros Gamma ST x s S t T Hs Ht.
generalize dependent Gamma. generalize dependent T.
induction t; intros T Gamma H;
inversion H; subst; simpl...
-
rename s0 into y.
destruct (eqb_stringP x y).
+
subst.
rewrite update_eq in H3.
inversion H3; subst.
eapply context_invariance...
intros x Hcontra.
destruct (free_in_context _ _ _ _ _ Hcontra Hs)
as [T' HT'].
inversion HT'.
+
apply T_Var.
rewrite update_neq in H3...
-  subst.
rename s0 into y.
destruct (eqb_stringP x y).
+
subst.
apply T_Abs. eapply context_invariance...
intros. rewrite update_shadow. reflexivity.
+
apply T_Abs. apply IHt.
eapply context_invariance...
intros. unfold update, t_update.
destruct (eqb_stringP y x0)...
subst.
rewrite false_eqb_string...
Qed.






Lemma assign_pres_store_typing : forall ST st l t,
l < length st ->
store_well_typed ST st ->
empty; ST |- t \in (store_Tlookup l ST) ->
store_well_typed ST (replace l t st).
Proof with auto. hammer_hook "References" "References.STLCRef.assign_pres_store_typing".
intros ST st l t Hlen HST Ht.
inversion HST; subst.
split. rewrite length_replace...
intros l' Hl'.
destruct (l' =? l) eqn: Heqll'.
-
apply Nat.eqb_eq in Heqll'; subst.
rewrite lookup_replace_eq...
-
apply Nat.eqb_neq in Heqll'.
rewrite lookup_replace_neq...
rewrite length_replace in Hl'.
apply H0...
Qed.






Lemma store_weakening : forall Gamma ST ST' t T,
extends ST' ST ->
Gamma; ST |- t \in T ->
Gamma; ST' |- t \in T.
Proof with eauto. hammer_hook "References" "References.STLCRef.store_weakening".
intros. induction H0; eauto.
-
erewrite <- extends_lookup...
apply T_Loc.
eapply length_extends...
Qed.



Lemma store_well_typed_app : forall ST st t1 T1,
store_well_typed ST st ->
empty; ST |- t1 \in T1 ->
store_well_typed (ST ++ T1::nil) (st ++ t1::nil).
Proof with auto. hammer_hook "References" "References.STLCRef.store_well_typed_app".
intros.
unfold store_well_typed in *.
inversion H as [Hlen Hmatch]; clear H.
rewrite app_length, plus_comm. simpl.
rewrite app_length, plus_comm. simpl.
split...
-
intros l Hl.
unfold store_lookup, store_Tlookup.
apply le_lt_eq_dec in Hl; inversion Hl as [Hlt | Heq].
+
apply lt_S_n in Hlt.
rewrite !app_nth1...
* apply store_weakening with ST. apply extends_app.
apply Hmatch...
* rewrite Hlen...
+
inversion Heq.
rewrite app_nth2; try omega.
rewrite <- Hlen.
rewrite minus_diag. simpl.
apply store_weakening with ST...
{ apply extends_app. }
rewrite app_nth2; try omega.
rewrite minus_diag. simpl. trivial.
Qed.








Lemma nth_eq_last : forall A (l:list A) x d,
nth (length l) (l ++ x::nil) d = x.
Proof. hammer_hook "References" "References.STLCRef.nth_eq_last".
induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.



Theorem preservation : forall ST t t' T st st',
empty; ST |- t \in T ->
store_well_typed ST st ->
t / st --> t' / st' ->
exists ST',
(extends ST' ST /\
empty; ST' |- t' \in T /\
store_well_typed ST' st').
Proof with eauto using store_weakening, extends_refl. hammer_hook "References" "References.STLCRef.preservation".
remember (@empty ty) as Gamma.
intros ST t t' T st st' Ht.
generalize dependent t'.
induction Ht; intros t' HST Hstep;
subst; try solve_by_invert; inversion Hstep; subst;
try (eauto using store_weakening, extends_refl).

-  exists ST.
inversion Ht1; subst.
split; try split... eapply substitution_preserves_typing...
-
eapply IHHt1 in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'...
-
eapply IHHt2 in H5...
inversion H5 as [ST' [Hext [Hty Hsty]]].
exists ST'...
-
+
eapply IHHt in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'...
-
+
eapply IHHt in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'...

-
eapply IHHt1 in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'...
-
eapply IHHt2 in H5...
inversion H5 as [ST' [Hext [Hty Hsty]]].
exists ST'...
-
+
eapply IHHt1 in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'... split...

-
exists (ST ++ T1::nil).
inversion HST; subst.
split.
apply extends_app.
split.
replace (Ref T1)
with (Ref (store_Tlookup (length st) (ST ++ T1::nil))).
apply T_Loc.
rewrite <- H. rewrite app_length, plus_comm. simpl. omega.
unfold store_Tlookup. rewrite <- H. rewrite nth_eq_last.
reflexivity.
apply store_well_typed_app; assumption.
-
eapply IHHt in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'...

-
exists ST. split; try split...
inversion HST as [_ Hsty].
replace T11 with (store_Tlookup l ST).
apply Hsty...
inversion Ht; subst...
-
eapply IHHt in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'...

-
exists ST. split; try split...
eapply assign_pres_store_typing...
inversion Ht1; subst...
-
eapply IHHt1 in H0...
inversion H0 as [ST' [Hext [Hty Hsty]]].
exists ST'...
-
eapply IHHt2 in H5...
inversion H5 as [ST' [Hext [Hty Hsty]]].
exists ST'...
Qed.




Definition manual_grade_for_preservation_informal : option (nat*string) := None.







Theorem progress : forall ST t T st,
empty; ST |- t \in T ->
store_well_typed ST st ->
(value t \/ exists t' st', t / st --> t' / st').
Proof with eauto. hammer_hook "References" "References.STLCRef.progress".
intros ST t T st Ht HST. remember (@empty ty) as Gamma.
induction Ht; subst; try solve_by_invert...
-
right. destruct IHHt1 as [Ht1p | Ht1p]...
+
inversion Ht1p; subst; try solve_by_invert.
destruct IHHt2 as [Ht2p | Ht2p]...
*
inversion Ht2p as [t2' [st' Hstep]].
exists (app (abs x T t) t2'), st'...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (app t1' t2), st'...
-
right. destruct IHHt as [Ht1p | Ht1p]...
+
inversion Ht1p; subst; try solve [ inversion Ht ].
*
exists (const (S n)), st...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (scc t1'), st'...
-
right. destruct IHHt as [Ht1p | Ht1p]...
+
inversion Ht1p; subst; try solve [inversion Ht ].
*
exists (const (pred n)), st...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (prd t1'), st'...
-
right. destruct IHHt1 as [Ht1p | Ht1p]...
+
inversion Ht1p; subst; try solve [inversion Ht1].
destruct IHHt2 as [Ht2p | Ht2p]...
*
inversion Ht2p; subst; try solve [inversion Ht2].
exists (const (mult n n0)), st...
*
inversion Ht2p as [t2' [st' Hstep]].
exists (mlt (const n) t2'), st'...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (mlt t1' t2), st'...
-
right. destruct IHHt1 as [Ht1p | Ht1p]...
+
inversion Ht1p; subst; try solve [inversion Ht1].
destruct n.
*  exists t2, st...
*  exists t3, st...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (test0 t1' t2 t3), st'...
-
right. destruct IHHt as [Ht1p | Ht1p]...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (ref t1'), st'...
-
right. destruct IHHt as [Ht1p | Ht1p]...
+
inversion Ht1p; subst; try solve_by_invert.
eexists. eexists. apply ST_DerefLoc...
inversion Ht; subst. inversion HST; subst.
rewrite <- H...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (deref t1'), st'...
-
right. destruct IHHt1 as [Ht1p|Ht1p]...
+
destruct IHHt2 as [Ht2p|Ht2p]...
*
inversion Ht1p; subst; try solve_by_invert.
eexists. eexists. apply ST_Assign...
inversion HST; subst. inversion Ht1; subst.
rewrite H in H5...
*
inversion Ht2p as [t2' [st' Hstep]].
exists (assign t1 t2'), st'...
+
inversion Ht1p as [t1' [st' Hstep]].
exists (assign t1' t2), st'...
Qed.






Module ExampleVariables.

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition r := "r".
Definition s := "s".

End ExampleVariables.

Module RefsAndNontermination.
Import ExampleVariables.

Definition loop_fun :=
abs x Unit (app (deref (var r)) unit).

Definition loop :=
app
(abs r (Ref (Arrow Unit Unit))
(tseq (assign (var r) loop_fun)
(app (deref (var r)) unit)))
(ref (abs x Unit unit)).



Lemma loop_typeable : exists T, empty; nil |- loop \in T.
Proof with eauto. hammer_hook "References" "References.STLCRef.RefsAndNontermination.loop_typeable".
eexists. unfold loop. unfold loop_fun.
eapply T_App...
eapply T_Abs...
eapply T_App...
eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.
unfold update, t_update. simpl. reflexivity. auto.
eapply T_Assign.
eapply T_Var. unfold update, t_update. simpl. reflexivity.
eapply T_Abs.
eapply T_App...
eapply T_Deref. eapply T_Var. reflexivity.
Qed.



Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
| sc_one  : forall (x y : X),
R x y -> step_closure R x y
| sc_step : forall (x y z : X),
R x y ->
step_closure R y z ->
step_closure R x z.

Definition multistep1 := (step_closure step).
Notation "t1 '/' st '-->+' t2 '/' st'" :=
(multistep1 (t1,st) (t2,st'))
(at level 40, st at level 39, t2 at level 39).





Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
repeat (print_goal; eapply multi_step ;
[ (eauto 10; fail) | (instantiate; compute)];
try solve [apply multi_refl]).



Lemma loop_steps_to_loop_fun :
loop / nil -->*
app (deref (loc 0)) unit / cons ([r:=loc 0]loop_fun) nil.
Proof. hammer_hook "References" "References.STLCRef.RefsAndNontermination.loop_steps_to_loop_fun".
unfold loop.
reduce.
Qed.



Lemma loop_fun_step_self :
app (deref (loc 0)) unit / cons ([r:=loc 0]loop_fun) nil -->+
app (deref (loc 0)) unit / cons ([r:=loc 0]loop_fun) nil.
Proof with eauto. hammer_hook "References" "References.STLCRef.RefsAndNontermination.loop_fun_step_self".
unfold loop_fun; simpl.
eapply sc_step. apply ST_App1...
eapply sc_one. compute. apply ST_AppAbs...
Qed.



Definition factorial : tm
. Admitted.

Lemma factorial_type : empty; nil |- factorial \in (Arrow Nat Nat).
Proof with eauto. hammer_hook "References" "References.STLCRef.RefsAndNontermination.factorial_type".
Admitted.












End RefsAndNontermination.
End STLCRef.



