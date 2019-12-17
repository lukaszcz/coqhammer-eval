From Hammer Require Import Hammer.

















Require Import List.
From Tait Require Term.

Unset Standard Proposition Elimination Names.



Record substitution : Set :=
mk_sub { support :> list Term.term ; shift : nat }.

Notation " l # n " := (mk_sub l n) (at level 20).

From Tait Require Export Term.

Definition sublift (rs:substitution) :=
([0] :: map (up 0) rs.(support))#(S rs.(shift)).
Hint Unfold sublift.

Fixpoint sub (r:term)(rs:substitution) {struct r}  : term :=
match r with
| [k] => nth k rs [k-length rs+rs.(shift)]
| r;s => (sub r rs);(sub s rs)
| \rho,r => \rho, sub r (sublift rs)
end.



Definition sub1 (r:term) := (r::nil)#0.
Coercion sub1 : term >-> substitution.

Eval compute in (sub (\Iota, (([0];[1]);[2];[3])) [7]).



Definition id (k:nat) : substitution := (map Var (seq 0 k)) # k.

Ltac map_map_S :=
rewrite map_map; simpl; rewrite <- map_map with (f:=S); try rewrite seq_shift.

Lemma map_up : forall l, map (up 0) (map Var l) = map Var (map S l).
Proof. hammer_hook "Subst" "Subst.map_up".
intros; map_map_S; auto.
Qed.

Lemma sublift_id : forall k, sublift (id k) = id (S k).
Proof. hammer_hook "Subst" "Subst.sublift_id".
intros; unfold sublift; simpl; rewrite map_up; rewrite seq_shift; auto.
Qed.

Lemma sublift_id_s : forall k s, sublift (((id k)++s::nil)#k) =
(id (S k)++(up 0 s))#(S k).
Proof. hammer_hook "Subst" "Subst.sublift_id_s".
intros; unfold sublift,id; simpl.
rewrite map_app; map_map_S; auto.
Qed.

Lemma sub_id : forall r k, sub r (id k) = r.
Proof. hammer_hook "Subst" "Subst.sub_id".
induction r; intros; simpl.
destruct (le_lt_dec k n).
rewrite nth_overflow; simpl_list; auto; tomega.
simp; rewrite seq_nth; auto.

simpl; rewrite IHr1; rewrite IHr2;auto.

rewrite sublift_id; rewrite IHr; auto.
Qed.



Lemma sub_occurs :
forall r (rs:substitution) k, shift rs <= length rs ->
occurs (k + length rs - rs.(shift)) r = false ->
existsb (occurs k) rs = false ->
occurs k (sub r rs) = false.
Proof. hammer_hook "Subst" "Subst.sub_occurs".
induction r; intros.

simpl.
destruct (le_lt_dec (length rs) n).
rewrite nth_overflow; auto.
simpl; destruct (eq_nat_dec (n - length rs + shift rs) k); auto.
simpl in H0; destruct (eq_nat_dec n (k + length rs - shift rs)); auto.
impossible.
rewrite existsb_nth; auto.

simpl in H0; auto.
destruct (orb_false_elim _ _ H0); clear H0.
simpl; rewrite (IHr1 rs k); auto.
rewrite (IHr2 rs k); auto.

simpl.
apply IHr.
simp; auto with arith.
rewrite <- H0; simpl; simpl_list; f_equal; omega.

simpl.
generalize H1.
clear H1 H0 H IHr r t.
induction (rs.(support)); simpl; auto.
rewrite lift_up.
intros.
destruct (orb_false_elim _ _ H1); clear H1; auto with bool.
rewrite IHl; auto.
replace (S k) with (1+k); auto.
rewrite lift_occurs; auto with arith bool.
Qed.


Ltac decide_nth3 :=
match goal with |- context [nth ?n (?l++?s::nil) ?d] =>
let tmp := fresh in
(destruct (lt_eq_lt_dec (length l) n) as [[tmp|tmp]|tmp];
generalize tmp; clear tmp; simp;
[ impossible || (intro tmp; rewrite nth_overflow;[idtac|simp; try omega])
| impossible || (intro tmp; rewrite app_nth2; [idtac|simp; try omega])
| impossible || (intro tmp; rewrite app_nth1; [idtac|simp; try omega];
simp; try (rewrite seq_nth; [idtac|simp; try omega]))])
end.


Lemma sub_occurs2 : forall r l k n, k < l -> k < n ->
occurs k r = occurs k (sub r ((id l ++ [n]::nil) # l)).
Proof. hammer_hook "Subst" "Subst.sub_occurs2".
induction r; simpl; auto.
intros; simpl.
replace ([n0]::nil) with (map Var ((n0)::nil)); auto.
rewrite <- map_app.
simp; auto; [generalize n1;clear n1|generalize e; clear e];
decide_nth3; subst;simp; try impossible.

intros; simpl in *; rewrite <- IHr1; auto; rewrite <- IHr2; auto.

intros.
rewriteconv sublift_id_s; simpl.
generalize (IHr (S l) (S k) (S n)); simpl; auto with arith.
Qed.

Lemma subk_occurs_gen : forall r l k,
occurs (S l+k) r = false ->
occurs l r = occurs (l+k) (sub r (((id l)++[l+k]::nil)#l)).
Proof. hammer_hook "Subst" "Subst.subk_occurs_gen".
induction r; simpl; intros.
replace ([l+k]::nil) with (map Var ((l+k)::nil)); auto.
rewrite <- map_app.
simpl_list; simpl.
simp; auto; [generalize n0 | generalize e]; subst;
decide_nth3; simp; impossible.

simpl in *.
destruct (orb_false_elim _ _ H); clear H.
rewrite <- IHr1; auto; rewrite <- IHr2; auto.

rewriteconv sublift_id_s; simpl.
rewrite (IHr (S l) k); simpl; auto.
Qed.

Lemma subk_occurs : forall r k,
occurs (S k) r = false ->
occurs 0 r = occurs k (sub r k).
Proof. hammer_hook "Subst" "Subst.subk_occurs".
exact (fun r => subk_occurs_gen r 0).
Qed.



Lemma down_sub : forall r l s, occurs l r = false ->
down l r = sub r (((id l)++s::nil)#l).
Proof. hammer_hook "Subst" "Subst.down_sub".
induction r; simpl; intros.
simp; try discriminate; decide_nth3; tomega.

destruct (orb_false_elim _ _ H).
rewrite IHr1 with l s; auto; rewrite IHr2 with l s; auto.

rewriteconv sublift_id_s.
rewrite (IHr (S l) (up 0 s)); auto.
Qed.



Definition swap0 (k:nat) : substitution :=
((map (up 0) (id k) ++ [0]::nil)# S (S k)).

Definition sub_swap0 (r:term)(k:nat) := sub r (swap0 k).
