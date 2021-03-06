From Hammer Require Import Hammer.















Require Import List Setoid Compare_dec Morphisms FinFun.
Import ListNotations.
Set Implicit Arguments.


Section Permutation.

Variable A:Type.

Inductive Permutation : list A -> list A -> Prop :=
| perm_nil: Permutation [] []
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Local Hint Constructors Permutation.



Theorem Permutation_nil : forall (l : list A), Permutation [] l -> l = [].
Proof. hammer_hook "Permutation" "Permutation.Permutation_nil".
intros l HF.
remember (@nil A) as m in HF.
induction HF; discriminate || auto.
Qed.

Theorem Permutation_nil_cons : forall (l : list A) (x : A),
~ Permutation nil (x::l).
Proof. hammer_hook "Permutation" "Permutation.Permutation_nil_cons".
intros l x HF.
apply Permutation_nil in HF; discriminate.
Qed.



Theorem Permutation_refl : forall l : list A, Permutation l l.
Proof. hammer_hook "Permutation" "Permutation.Permutation_refl".
induction l; constructor. exact IHl.
Qed.

Theorem Permutation_sym : forall l l' : list A,
Permutation l l' -> Permutation l' l.
Proof. hammer_hook "Permutation" "Permutation.Permutation_sym".
intros l l' Hperm; induction Hperm; auto.
apply perm_trans with (l':=l'); assumption.
Qed.

Theorem Permutation_trans : forall l l' l'' : list A,
Permutation l l' -> Permutation l' l'' -> Permutation l l''.
Proof. hammer_hook "Permutation" "Permutation.Permutation_trans".
exact perm_trans.
Qed.

End Permutation.

Hint Resolve Permutation_refl perm_nil perm_skip.



Local Hint Resolve perm_swap perm_trans.
Local Hint Resolve Permutation_sym Permutation_trans.



Instance Permutation_Equivalence A : Equivalence (@Permutation A) | 10 := {
Equivalence_Reflexive := @Permutation_refl A ;
Equivalence_Symmetric := @Permutation_sym A ;
Equivalence_Transitive := @Permutation_trans A }.

Instance Permutation_cons A :
Proper (Logic.eq ==> @Permutation A ==> @Permutation A) (@cons A) | 10.
Proof. hammer_hook "Permutation" "Permutation.Permutation_cons".
repeat intro; subst; auto using perm_skip.
Qed.

Section Permutation_properties.

Variable A:Type.

Implicit Types a b : A.
Implicit Types l m : list A.



Theorem Permutation_in : forall (l l' : list A) (x : A),
Permutation l l' -> In x l -> In x l'.
Proof. hammer_hook "Permutation" "Permutation.Permutation_in".
intros l l' x Hperm; induction Hperm; simpl; tauto.
Qed.

Global Instance Permutation_in' :
Proper (Logic.eq ==> @Permutation A ==> iff) (@In A) | 10.
Proof. hammer_hook "Permutation" "Permutation.Permutation_in'".
repeat red; intros; subst; eauto using Permutation_in.
Qed.

Lemma Permutation_app_tail : forall (l l' tl : list A),
Permutation l l' -> Permutation (l++tl) (l'++tl).
Proof. hammer_hook "Permutation" "Permutation.Permutation_app_tail".
intros l l' tl Hperm; induction Hperm as [|x l l'|x y l|l l' l'']; simpl; auto.
eapply Permutation_trans with (l':=l'++tl); trivial.
Qed.

Lemma Permutation_app_head : forall (l tl tl' : list A),
Permutation tl tl' -> Permutation (l++tl) (l++tl').
Proof. hammer_hook "Permutation" "Permutation.Permutation_app_head".
intros l tl tl' Hperm; induction l;
[trivial | repeat rewrite <- app_comm_cons; constructor; assumption].
Qed.

Theorem Permutation_app : forall (l m l' m' : list A),
Permutation l l' -> Permutation m m' -> Permutation (l++m) (l'++m').
Proof. hammer_hook "Permutation" "Permutation.Permutation_app".
intros l m l' m' Hpermll' Hpermmm';
induction Hpermll' as [|x l l'|x y l|l l' l''];
repeat rewrite <- app_comm_cons; auto.
apply Permutation_trans with (l' := (x :: y :: l ++ m));
[idtac | repeat rewrite app_comm_cons; apply Permutation_app_head]; trivial.
apply Permutation_trans with (l' := (l' ++ m')); try assumption.
apply Permutation_app_tail; assumption.
Qed.

Global Instance Permutation_app' :
Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A) | 10.
Proof. hammer_hook "Permutation" "Permutation.Permutation_app'".
repeat intro; now apply Permutation_app.
Qed.

Lemma Permutation_add_inside : forall a (l l' tl tl' : list A),
Permutation l l' -> Permutation tl tl' ->
Permutation (l ++ a :: tl) (l' ++ a :: tl').
Proof. hammer_hook "Permutation" "Permutation.Permutation_add_inside".
intros; apply Permutation_app; auto.
Qed.

Lemma Permutation_cons_append : forall (l : list A) x,
Permutation (x :: l) (l ++ x :: nil).
Proof. hammer_hook "Permutation" "Permutation.Permutation_cons_append".   induction l; intros; auto. simpl. rewrite <- IHl; auto. Qed.
Local Hint Resolve Permutation_cons_append.

Theorem Permutation_app_comm : forall (l l' : list A),
Permutation (l ++ l') (l' ++ l).
Proof. hammer_hook "Permutation" "Permutation.Permutation_app_comm".
induction l as [|x l]; simpl; intro l'.
rewrite app_nil_r; trivial. rewrite IHl.
rewrite app_comm_cons, Permutation_cons_append.
now rewrite <- app_assoc.
Qed.
Local Hint Resolve Permutation_app_comm.

Theorem Permutation_cons_app : forall (l l1 l2:list A) a,
Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Proof. hammer_hook "Permutation" "Permutation.Permutation_cons_app".
intros l l1 l2 a H. rewrite H.
rewrite app_comm_cons, Permutation_cons_append.
now rewrite <- app_assoc.
Qed.
Local Hint Resolve Permutation_cons_app.

Lemma Permutation_Add a l l' : Add a l l' -> Permutation (a::l) l'.
Proof. hammer_hook "Permutation" "Permutation.Permutation_Add".
induction 1; simpl; trivial.
rewrite perm_swap. now apply perm_skip.
Qed.

Theorem Permutation_middle : forall (l1 l2:list A) a,
Permutation (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof. hammer_hook "Permutation" "Permutation.Permutation_middle".
auto.
Qed.
Local Hint Resolve Permutation_middle.

Theorem Permutation_rev : forall (l : list A), Permutation l (rev l).
Proof. hammer_hook "Permutation" "Permutation.Permutation_rev".
induction l as [| x l]; simpl; trivial. now rewrite IHl at 1.
Qed.

Global Instance Permutation_rev' :
Proper (@Permutation A ==> @Permutation A) (@rev A) | 10.
Proof. hammer_hook "Permutation" "Permutation.Permutation_rev'".
repeat intro; now rewrite <- 2 Permutation_rev.
Qed.

Theorem Permutation_length : forall (l l' : list A),
Permutation l l' -> length l = length l'.
Proof. hammer_hook "Permutation" "Permutation.Permutation_length".
intros l l' Hperm; induction Hperm; simpl; auto. now transitivity (length l').
Qed.

Global Instance Permutation_length' :
Proper (@Permutation A ==> Logic.eq) (@length A) | 10.
Proof. hammer_hook "Permutation" "Permutation.Permutation_length'".
exact Permutation_length.
Qed.

Theorem Permutation_ind_bis :
forall P : list A -> list A -> Prop,
P [] [] ->
(forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
(forall x y l l', Permutation l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
(forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
forall l l', Permutation l l' -> P l l'.
Proof. hammer_hook "Permutation" "Permutation.Permutation_ind_bis".
intros P Hnil Hskip Hswap Htrans.
induction 1; auto.
apply Htrans with (x::y::l); auto.
apply Hswap; auto.
induction l; auto.
apply Hskip; auto.
apply Hskip; auto.
induction l; auto.
eauto.
Qed.

Theorem Permutation_nil_app_cons : forall (l l' : list A) (x : A),
~ Permutation nil (l++x::l').
Proof. hammer_hook "Permutation" "Permutation.Permutation_nil_app_cons".
intros l l' x HF.
apply Permutation_nil in HF. destruct l; discriminate.
Qed.

Ltac InvAdd := repeat (match goal with
| H: Add ?x _ (_ :: _) |- _ => inversion H; clear H; subst
end).

Ltac finish_basic_perms H :=
try constructor; try rewrite perm_swap; try constructor; trivial;
(rewrite <- H; now apply Permutation_Add) ||
(rewrite H; symmetry; now apply Permutation_Add).

Theorem Permutation_Add_inv a l1 l2 :
Permutation l1 l2 -> forall l1' l2', Add a l1' l1 -> Add a l2' l2 ->
Permutation l1' l2'.
Proof. hammer_hook "Permutation" "Permutation.Permutation_Add_inv".
revert l1 l2. refine (Permutation_ind_bis _ _ _ _ _).
-
inversion_clear 1.
-
intros x l1 l2 PE IH. intros. InvAdd; try finish_basic_perms PE.
constructor. now apply IH.
-
intros x y l1 l2 PE IH. intros. InvAdd; try finish_basic_perms PE.
rewrite perm_swap; do 2 constructor. now apply IH.
-
intros l1 l l2 PE IH PE' IH' l1' l2' AD1 AD2.
assert (Ha : In a l). { rewrite <- PE. rewrite (Add_in AD1). simpl; auto. }
destruct (Add_inv _ _ Ha) as (l',AD).
transitivity l'; auto.
Qed.

Theorem Permutation_app_inv (l1 l2 l3 l4:list A) a :
Permutation (l1++a::l2) (l3++a::l4) -> Permutation (l1++l2) (l3 ++ l4).
Proof. hammer_hook "Permutation" "Permutation.Permutation_app_inv".
intros. eapply Permutation_Add_inv; eauto using Add_app.
Qed.

Theorem Permutation_cons_inv l l' a :
Permutation (a::l) (a::l') -> Permutation l l'.
Proof. hammer_hook "Permutation" "Permutation.Permutation_cons_inv".
intro. eapply Permutation_Add_inv; eauto using Add_head.
Qed.

Theorem Permutation_cons_app_inv l l1 l2 a :
Permutation (a :: l) (l1 ++ a :: l2) -> Permutation l (l1 ++ l2).
Proof. hammer_hook "Permutation" "Permutation.Permutation_cons_app_inv".
intro. eapply Permutation_Add_inv; eauto using Add_head, Add_app.
Qed.

Theorem Permutation_app_inv_l : forall l l1 l2,
Permutation (l ++ l1) (l ++ l2) -> Permutation l1 l2.
Proof. hammer_hook "Permutation" "Permutation.Permutation_app_inv_l".
induction l; simpl; auto.
intros.
apply IHl.
apply Permutation_cons_inv with a; auto.
Qed.

Theorem Permutation_app_inv_r l l1 l2 :
Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2.
Proof. hammer_hook "Permutation" "Permutation.Permutation_app_inv_r".
rewrite 2 (Permutation_app_comm _ l). apply Permutation_app_inv_l.
Qed.

Lemma Permutation_length_1_inv: forall a l, Permutation [a] l -> l = [a].
Proof. hammer_hook "Permutation" "Permutation.Permutation_length_1_inv".
intros a l H; remember [a] as m in H.
induction H; try (injection Heqm as -> ->);
discriminate || auto.
apply Permutation_nil in H as ->; trivial.
Qed.

Lemma Permutation_length_1: forall a b, Permutation [a] [b] -> a = b.
Proof. hammer_hook "Permutation" "Permutation.Permutation_length_1".
intros a b H.
apply Permutation_length_1_inv in H; injection H as ->; trivial.
Qed.

Lemma Permutation_length_2_inv :
forall a1 a2 l, Permutation [a1;a2] l -> l = [a1;a2] \/ l = [a2;a1].
Proof. hammer_hook "Permutation" "Permutation.Permutation_length_2_inv".
intros a1 a2 l H; remember [a1;a2] as m in H.
revert a1 a2 Heqm.
induction H; intros; try (injection Heqm as ? ?; subst);
discriminate || (try tauto).
apply Permutation_length_1_inv in H as ->; left; auto.
apply IHPermutation1 in Heqm as [H1|H1]; apply IHPermutation2 in H1 as [];
auto.
Qed.

Lemma Permutation_length_2 :
forall a1 a2 b1 b2, Permutation [a1;a2] [b1;b2] ->
a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.
Proof. hammer_hook "Permutation" "Permutation.Permutation_length_2".
intros a1 b1 a2 b2 H.
apply Permutation_length_2_inv in H as [H|H]; injection H as -> ->; auto.
Qed.

Lemma NoDup_Permutation l l' : NoDup l -> NoDup l' ->
(forall x:A, In x l <-> In x l') -> Permutation l l'.
Proof. hammer_hook "Permutation" "Permutation.NoDup_Permutation".
intros N. revert l'. induction N as [|a l Hal Hl IH].
- destruct l'; simpl; auto.
intros Hl' H. exfalso. rewrite (H a); auto.
- intros l' Hl' H.
assert (Ha : In a l') by (apply H; simpl; auto).
destruct (Add_inv _ _ Ha) as (l'' & AD).
rewrite <- (Permutation_Add AD).
apply perm_skip.
apply IH; clear IH.
* now apply (NoDup_Add AD).
* split.
+ apply incl_Add_inv with a l'; trivial. intro. apply H.
+ intro Hx.
assert (Hx' : In x (a::l)).
{ apply H. rewrite (Add_in AD). now right. }
destruct Hx'; simpl; trivial. subst.
rewrite (NoDup_Add AD) in Hl'. tauto.
Qed.

Lemma NoDup_Permutation_bis l l' : NoDup l -> NoDup l' ->
length l' <= length l -> incl l l' -> Permutation l l'.
Proof. hammer_hook "Permutation" "Permutation.NoDup_Permutation_bis".
intros. apply NoDup_Permutation; auto.
split; auto. apply NoDup_length_incl; trivial.
Qed.

Lemma Permutation_NoDup l l' : Permutation l l' -> NoDup l -> NoDup l'.
Proof. hammer_hook "Permutation" "Permutation.Permutation_NoDup".
induction 1; auto.
* inversion_clear 1; constructor; eauto using Permutation_in.
* inversion_clear 1 as [|? ? H1 H2]. inversion_clear H2; simpl in *.
constructor. simpl; intuition. constructor; intuition.
Qed.

Global Instance Permutation_NoDup' :
Proper (@Permutation A ==> iff) (@NoDup A) | 10.
Proof. hammer_hook "Permutation" "Permutation.Permutation_NoDup'".
repeat red; eauto using Permutation_NoDup.
Qed.

End Permutation_properties.

Section Permutation_map.

Variable A B : Type.
Variable f : A -> B.

Lemma Permutation_map l l' :
Permutation l l' -> Permutation (map f l) (map f l').
Proof. hammer_hook "Permutation" "Permutation.Permutation_map".
induction 1; simpl; eauto.
Qed.

Global Instance Permutation_map' :
Proper (@Permutation A ==> @Permutation B) (map f) | 10.
Proof. hammer_hook "Permutation" "Permutation.Permutation_map'".
exact Permutation_map.
Qed.

End Permutation_map.

Lemma nat_bijection_Permutation n f :
bFun n f ->
Injective f ->
let l := seq 0 n in Permutation (map f l) l.
Proof. hammer_hook "Permutation" "Permutation.nat_bijection_Permutation".
intros Hf BD.
apply NoDup_Permutation_bis; auto using Injective_map_NoDup, seq_NoDup.
* now rewrite map_length.
* intros x. rewrite in_map_iff. intros (y & <- & Hy').
rewrite in_seq in *. simpl in *.
destruct Hy' as (_,Hy'). auto with arith.
Qed.

Section Permutation_alt.
Variable A:Type.
Implicit Type a : A.
Implicit Type l : list A.



Let adapt f n :=
let m := f (S n) in if le_lt_dec m (f 0) then m else pred m.

Let adapt_injective f : Injective f -> Injective (adapt f).
Proof. hammer_hook "Permutation" "Permutation.Permutation_alt.adapt_injective".
unfold adapt. intros Hf x y EQ.
destruct le_lt_dec as [LE|LT]; destruct le_lt_dec as [LE'|LT'].
- now apply eq_add_S, Hf.
- apply Lt.le_lt_or_eq in LE.
destruct LE as [LT|EQ']; [|now apply Hf in EQ'].
unfold lt in LT. rewrite EQ in LT.
rewrite <- (Lt.S_pred _ _ LT') in LT.
elim (Lt.lt_not_le _ _ LT' LT).
- apply Lt.le_lt_or_eq in LE'.
destruct LE' as [LT'|EQ']; [|now apply Hf in EQ'].
unfold lt in LT'. rewrite <- EQ in LT'.
rewrite <- (Lt.S_pred _ _ LT) in LT'.
elim (Lt.lt_not_le _ _ LT LT').
- apply eq_add_S, Hf.
now rewrite (Lt.S_pred _ _ LT), (Lt.S_pred _ _ LT'), EQ.
Qed.

Let adapt_ok a l1 l2 f : Injective f -> length l1 = f 0 ->
forall n, nth_error (l1++a::l2) (f (S n)) = nth_error (l1++l2) (adapt f n).
Proof. hammer_hook "Permutation" "Permutation.Permutation_alt.adapt_ok".
unfold adapt. intros Hf E n.
destruct le_lt_dec as [LE|LT].
- apply Lt.le_lt_or_eq in LE.
destruct LE as [LT|EQ]; [|now apply Hf in EQ].
rewrite <- E in LT.
rewrite 2 nth_error_app1; auto.
- rewrite (Lt.S_pred _ _ LT) at 1.
rewrite <- E, (Lt.S_pred _ _ LT) in LT.
rewrite 2 nth_error_app2; auto with arith.
rewrite <- Minus.minus_Sn_m; auto with arith.
Qed.

End Permutation_alt.
