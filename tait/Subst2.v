From Hammer Require Import Hammer.

















From Tait Require Export Subst.

Unset Standard Proposition Elimination Names.



Module Joachimski.

Inductive substitution : Set :=
Dot : term -> substitution -> substitution
| Up : nat -> substitution.

Fixpoint sublift (theta : substitution) : nat -> substitution := fun n =>
match theta with
| Dot r theta =>  Dot (lift 0 n r) (sublift theta n)
| Up m => Up (m+n)
end.

Notation " th ||\ n " := (sublift th n) (at level 60, no associativity).

Lemma subliftId : forall theta, theta||\0 = theta.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.subliftId".
induction theta; simpl; auto with arith.
rewrite lift_null; f_equal; auto.
Qed.

Fixpoint sub' (k : nat) : substitution -> term := fun theta =>
match k,theta with
| S k, Dot r theta => sub' k theta
| 0, Dot r theta => r
| k, Up n => Var (k+n)
end.

Fixpoint sub (r : term) : substitution -> term := fun theta =>
match r with
| Var k => sub' k theta
| App r s => App (sub r theta) (sub s theta)
| Abs rho r => Abs rho (sub r (Dot (Var 0) (sublift theta 1)))
end.

Notation " r {[ th ]} " := (sub r th) (at level 60, no associativity).

Fixpoint comp'  (n : nat) : substitution -> substitution := fun theta =>
match n,theta with
| 0,_ => theta
| S n, Dot r theta => comp' n theta
| S n, Up m => Up (S n + m)
end.

Fixpoint comp (theta theta': substitution) {struct theta} : substitution :=
match theta with
| Dot r theta => Dot (sub r theta') (comp theta theta')
| Up n => comp' n theta'
end.

Notation " th 'o' th' " := (comp th th') (at level 61, left associativity).

Lemma Comp'Eq : forall n m, comp' m (Up n) = Up (m+n).
induction m; simpl; auto with arith.
Qed.

Lemma Sub'Eq : forall n m, sub' m (Up n) = Var (n+m).
induction m; simpl; auto with arith; tomega.
Qed.

Hint Rewrite Sub'Eq Comp'Eq : db.
Ltac ar := autorewrite with db.

Lemma SubliftTwice :
forall theta n m, (theta ||\ n) ||\ m = theta ||\ n+m.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SubliftTwice".
induction theta; simpl; intros.
rewrite lift_lift; f_equal; auto.
tomega.
Qed.



Fixpoint PushList (l : list term) : substitution -> substitution :=
fun theta =>
match l with
| nil => theta
| r :: l => Dot r (PushList l theta)
end.

Infix "++" := PushList.



Fixpoint Spare(n : nat) : substitution -> substitution :=
fun theta =>
match n with
| 0 => theta
| S m => Spare m (Dot (Var m) theta)
end.

Infix "!!" := Spare (at level 60, no associativity).






Lemma SparePushList_aux : forall n m theta, m<=n ->
(map Var (seq 0 n)) ++ theta =
Spare m (map Var (seq m (n-m)) ++ theta).
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SparePushList_aux".
induction m; intros; simp; auto.
rewrite IHm; simpl; try omega.
replace (n-m) with (S (n- (S m))); simpl; auto; omega.
Qed.

Lemma SparePushList :
forall n theta, n !! theta = map Var (seq 0 n) ++ theta.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SparePushList".
intros; rewrite (SparePushList_aux n n); simpl_arith; auto.
Qed.

Lemma SubPushList1 : forall n l theta, n < length l ->
Var n {[l++theta]} = nth n l (Var 0).
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SubPushList1".
induction n; destruct l; intros; try (inversion H; fail); auto.
simpl in *; rewrite IHn; auto with arith.
Qed.

Lemma SubPushList2 : forall n l theta, length l <= n ->
Var n {[l++theta]} = Var (n - length l) {[theta]}.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SubPushList2".
induction n; destruct l; intros; auto.
inversion H.
simpl in *; apply IHn; auto with arith.
Qed.

Lemma SubliftPushList : forall n l theta,
(l++theta) ||\ n = (map (fun r => r |\ [0,n]) l) ++ (theta ||\ n).
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SubliftPushList".
induction l; simpl; auto.
intros; rewrite IHl; auto.
Qed.

Lemma UpPushList : forall l theta, (Up (length l))o(l++theta) = theta.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.UpPushList".
induction l; simpl; auto.
Qed.




Lemma LiftSubst : forall r m n, r |\ [m,n] = r {[ m !! (Up (n+m)) ]}.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.LiftSubst".
induction r; intros.
rewrite SparePushList.
simpl lift.
break.
rewrite SubPushList2; simp; auto; ar; tomega.
rewrite SubPushList1; simp; auto; rewrite seq_nth; auto.

simpl; rewrite IHr1; rewrite IHr2; auto.

rewrite SparePushList; simpl.
rewrite IHr; do 2 f_equal.
rewrite SparePushList; simpl; f_equal.
rewrite SubliftPushList; simpl.
map_map_S; simpl_arith; auto.
Qed.


Lemma CompUp : forall theta n, theta o Up n = theta ||\ n.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.CompUp".
induction theta; simpl; intros.
rewrite IHtheta.
rewrite LiftSubst.
simp; auto.
ar; auto.
Qed.


Lemma LiftSublift : forall k n m theta,
(Var k {[theta ||\ m]}) |\ [m,n] = Var k {[theta ||\ m+n]}.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.LiftSublift".
induction k.
destruct theta; simpl; intros.
exact (lift_lift2 t 0 m n).
simp; tomega.
destruct theta; simpl in *; auto; intros; simp; tomega.
Qed.


Lemma LiftSpare : forall r m theta n,
(r {[ m !! (theta ||\ m)]}) |\ [m,n] = r {[ m !! (theta ||\ m+n)]}.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.LiftSpare".
induction r; intros.

case (le_lt_dec m n); intros; do 2 (rewrite SparePushList; auto).

do 2 (rewrite SubPushList2; simpl_list; auto).
apply LiftSublift.

do 2 (rewrite SubPushList1; simpl_list; auto).
rewrite seq_nth; simp; tomega.

simpl; rewrite IHr1; rewrite IHr2; auto.

simpl.
do 2 (rewrite SparePushList; rewrite SubliftPushList).
f_equal.
map_map_S.
do 2 rewrite SubliftTwice.
generalize (IHr (S m) theta n).
do 2 rewrite SparePushList.
simp; auto.
Qed.


Lemma LiftSpare2 : forall r theta n,
(r {[theta]}) |\ [0,n] = r {[ theta ||\ n]}.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.LiftSpare2".
intros.
rewrite <- (subliftId theta).
rewrite SubliftTwice.
exact (LiftSpare r 0 theta n).
Qed.


Lemma CompSublift : forall theta theta' n,
theta o (theta' ||\ n) = (theta o theta') ||\ n.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.CompSublift".
induction theta.
simpl; intros.
rewrite LiftSpare2.
rewrite IHtheta; auto.
simpl.
induction n; destruct theta'; simpl; auto; intros; tomega.
Qed.


Lemma SubLiftSpare : forall r m l theta,
(r |\ [m, length l]) {[ m  !! (l++theta) ]} = r {[ m !! theta ]}.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SubLiftSpare".
induction r; simpl; intros.
simp;
match goal with|-sub'?n?s=sub'?n'?s'=>change(n{[s]}=n'{[s']})end;
do 2 (rewrite SparePushList; auto).

do 3 (rewrite SubPushList2; [idtac | simpl_list; omega]); simpl_list.
do 2 (f_equal; auto); omega.

do 2 (rewrite SubPushList1; simpl_list; auto).

rewrite IHr1; rewrite IHr2; trivial.

do 2 rewrite SparePushList; do 3 rewrite SubliftPushList.
map_map_S.
set (l' := map (fun r0 => r0 |\  [0, 1]) l).
replace (length l) with (length l').
generalize (IHr (S m) l' (theta ||\1)).
do 2 rewrite SparePushList.
simpl; congruence.
unfold l'; simp; auto.
Qed.


Lemma SubLiftComp : forall theta theta' l,
(theta ||\ length l)o(l++theta') = theta o theta'.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SubLiftComp".
induction theta; simpl; intros.
change  (l++theta') with (0 !! (l++theta')).
rewrite SubLiftSpare; simpl.
rewrite IHtheta; auto.
induction l; simpl; simpl_arith; auto.
Qed.


Lemma SubSub : forall r theta theta',
r{[theta]}{[theta']} = r{[theta o theta']}.
Proof. hammer_hook "Subst2" "Subst2.Joachimski.SubSub".
induction r; simpl.
intro theta.
generalize n; clear n.
induction theta; simpl.
destruct n; auto; intros.
apply (IHtheta n theta').
intros m theta'.
generalize n m; clear n m.
induction theta'; simpl; ar; auto.
destruct n; auto; simpl; intros.
ar; auto.
simpl in *; rewrite <- IHtheta'; ar; auto.
intros; rewrite  Comp'Eq; do 2 (ar; simpl); tomega.

intros; rewrite IHr1; rewrite IHr2; trivial.

intros; rewrite IHr; simpl.
rewrite <- CompSublift ; simpl; auto.
rewrite <- SubLiftComp with (l:=[0]::nil) (theta:=theta); auto.
Qed.


Lemma CompAssoc : forall theta theta' theta'',
(theta o theta') o theta'' = theta o (theta' o theta'').
Proof. hammer_hook "Subst2" "Subst2.Joachimski.CompAssoc".
induction theta; intros.
simpl; rewrite SubSub.
rewrite IHtheta; trivial.
generalize n; clear n.
induction theta'; intros.
destruct n; simpl in *; auto.
generalize n n0; clear n n0.
induction theta''; intros.
destruct n; simpl; ar; simp; auto.
simpl in *; rewrite <- IHtheta''; ar; auto.
intros; do 2 (simpl; ar); tomega.
Qed.

End Joachimski.

Module Isom.
Import Joachimski.

Fixpoint sub_2_1 (s:substitution) : Subst.substitution := match s with
| Dot r s => let s' := sub_2_1 s in (r::s')#s'.(shift)
| Up n => nil#n
end.

Definition sub_1_2 (s:Subst.substitution) : substitution :=
fold_right Dot (Up s.(shift)) s.

Lemma substitution_isom1 : forall s, sub_2_1 (sub_1_2 s) = s.
Proof. hammer_hook "Subst2" "Subst2.Isom.substitution_isom1".
induction s as [l s]; unfold sub_1_2.
induction l; auto; simpl in*; rewrite IHl; auto.
Qed.

Lemma substitution_isom2 : forall s, sub_1_2 (sub_2_1 s) = s.
Proof. hammer_hook "Subst2" "Subst2.Isom.substitution_isom2".
unfold sub_1_2.
induction s; auto; simpl; rewrite IHs; auto.
Qed.

Lemma sublift_isom : forall th n, sub_2_1 (th ||\ n) =
(map (lift 0 n) (sub_2_1 th))#((sub_2_1 th).(shift)+n).
Proof. hammer_hook "Subst2" "Subst2.Isom.sublift_isom".
induction th; simpl; auto.
intros; rewrite IHth; simpl; auto.
Qed.

Lemma sub_isom1 : forall r s, sub r s = Subst.sub r (sub_2_1 s).
Proof. hammer_hook "Subst2" "Subst2.Isom.sub_isom1".
induction r; simpl.
induction n; destruct s; simpl; auto.
intros; rewrite IHr1; rewrite IHr2; auto.
intros; rewrite IHr; auto.
simpl.
rewrite sublift_isom; simpl.
simpl_arith.
unfold Subst.sublift.
rewrite map_ext with (f:=up 0) (g:=lift 0 1); auto.
intros; apply lift_up.
Qed.

Lemma sub_isom2 : forall r s, Subst.sub r s = sub r (sub_1_2 s).
Proof. hammer_hook "Subst2" "Subst2.Isom.sub_isom2".
intros.
pattern s at 1; rewrite <- (substitution_isom1 s).
rewrite sub_isom1; auto.
Qed.

End Isom.

Import Joachimski.
Import Isom.
Import Subst.

Lemma Sub_Sub : forall r (s:term) rs,
sub (sub r s) rs = sub r (((sub s rs)::rs)#rs.(shift)).
Proof. hammer_hook "Subst2" "Subst2.Sub_Sub".
intros.
repeat rewrite sub_isom2.
unfold Isom.sub_1_2; simpl.
set (theta := fold_right Dot (Up (shift rs)) rs);
clearbody theta; clear rs.
rewrite SubSub.
simpl; auto.
Qed.

Lemma Sub_Sub_Ad_Hoc : forall (r s:term) (rs:substitution),
sub (sub r (sublift rs)) s =
sub r ((s::rs)#rs.(shift)).
Proof. hammer_hook "Subst2" "Subst2.Sub_Sub_Ad_Hoc".
intros.
repeat rewrite sub_isom2.
assert (sub_1_2 (sublift rs) = Dot [0] (sub_1_2 rs ||\ 1)).
unfold sub_1_2, sublift; simpl.
destruct rs; simpl.
induction support; simpl; simpl_arith; auto.
rewrite lift_up.
injection IHsupport; clear IHsupport; intros.
rewrite H; auto.
rewrite H; clear H.
unfold sub_1_2; simpl.
set (theta := (fold_right Dot (Up (shift rs)) rs)); clearbody theta; clear rs.
rewrite SubSub; simpl.
replace (Dot s (Up 0)) with ((s::nil) ++ Up 0); auto.
replace 1 with (length (s::nil)); auto.
rewrite SubLiftComp.
rewrite CompUp.
rewrite subliftId; auto.
Qed.

Definition above k r := forall n, k <= n -> occurs n r = false.

Lemma above_sub : forall r (rs:substitution) l d,
above (length rs) r ->
sub r ((rs++l)#d) = sub r rs.
Proof. hammer_hook "Subst2" "Subst2.above_sub".
unfold above; induction r; simpl; intros.
destruct (le_lt_dec (length rs) n).
generalize (H n l0); destruct (eq_nat_dec n n); intuition; try discriminate.
rewrite app_nth1; auto.
apply nth_indep; auto.
rewrite IHr1.
rewrite IHr2; auto.
intros; destruct (orb_false_elim _ _ (H n H0)); auto.
intros; destruct (orb_false_elim _ _ (H n H0)); auto.
unfold sublift; simpl; rewrite map_app; simpl.
rewrite app_comm_cons.
f_equal.
apply (IHr (([0] :: map (up 0) rs) # S (shift rs))).
simp; intros; rewrite (S_pred n) with 0; intuition.
Qed.

Lemma sub_sub_swap0 : forall r k, above (S k) r ->
sub_swap0 (sub r [k]) k = r.
Proof. hammer_hook "Subst2" "Subst2.sub_sub_swap0".
unfold sub_swap0; intros.
rewrite Sub_Sub; simp.
rewrite app_nth2; simp; auto.
rewrite app_comm_cons.
replace ([0] :: map (up 0) (map Var (seq 0 k))) with (support (id (S k))).
rewrite above_sub.
apply sub_id.
unfold id; simp; auto.
rewrite <- (sublift_id k); auto.
Qed.


Lemma down_sub2 : forall r l k,
occurs 0 r = false ->
let rs := ((id l)++[k]::nil)#l in
down 0 (sub r (sublift rs)) = sub (down 0 r) rs.

Proof. hammer_hook "Subst2" "Subst2.down_sub2".
intros.
rewrite (down_sub _ _ dterm H).
unfold id; simpl.
replace ((dterm::nil)#0) with (sub1 dterm); auto.
rewrite Sub_Sub.
rewrite <- Sub_Sub_Ad_Hoc.
rewrite (down_sub (sub r (sublift rs)) 0 (sub dterm rs)); auto.
unfold rs, sublift; simpl.
rewrite map_app; simpl.
rewrite app_comm_cons.
replace ([0] :: map (up 0) (map Var (seq 0 l))) with (support (id (S l))).
rewrite <- sub_occurs2; auto with arith.
rewrite <- (sublift_id l); auto.
Qed.

