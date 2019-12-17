From Hammer Require Import Hammer.
















From Tait Require Export TaitCore.
From Tait Require Export nc.

Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

Module NormalizationProofNc (R:Requirements).

Import R.

Notation App' := (nc2 App).
Notation app' := (nc2 (@app (_ : Set))).

Lemma app'_ass : forall (l1 l2 l3: context!) ,
app' (app' l1 l2) l3 = app' l1 (app' l2 l3).
Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.app'_ass".
intros; unfold nc2.
case l1; case l2; case l3; intros.
rewrite app_ass; auto.
Qed.

Definition SN (rhos:context!) (rho:type) (r:term!) :=
forall k (sigmas:context!) ,
(letnc taus' := app' rhos sigmas  in letnc r':= r in F taus' rho r' k) ->
{ s:term | letnc taus' := app' rhos sigmas  in letnc r':= r in N taus' rho r' s }.

Definition SA (rhos:context!) (rho:type) (r:term!) :=
forall k (sigmas:context!) ,
(letnc taus' := app' rhos sigmas  in letnc r':= r in F taus' rho r' k) ->
{ s:term | letnc taus' := app' rhos sigmas  in letnc r':= r in A taus' rho r' s }.

Open Scope type_scope.

Fixpoint SC (rhos:context!) (rho:type) (r:term!) {struct rho} : Type :=
(letnc rhos' := rhos in letnc r' := r in TypJ rhos' r' rho) **
match rho with
| Iota => SN rhos Iota r
| rho-->sigma =>
forall s sigmas, SC (app' rhos sigmas) rho s ->
SC (app' rhos sigmas) sigma (App' r s)
end.

Lemma SN_ext_ctx : forall rho rhos sigmas r,
(letnc rhos' := rhos in letnc r' := r in TypJ rhos' r' rho) ->
SN rhos rho r -> SN (app' rhos sigmas) rho r.

Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.SN_ext_ctx".
unfold SN; intros.
rewrite app'_ass in H2; rewrite app'_ass.
apply (H1 k _ H2).
Qed.
Hint Resolve SN_ext_ctx.


Lemma SC_TypJ :
forall rhos rho r, SC rhos rho r ->
(letnc rhos' := rhos in letnc r' := r in TypJ rhos' r' rho).

Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.SC_TypJ".
destruct rho; destruct 1; auto.
Qed.
Hint Resolve SC_TypJ.


Lemma SC_ext_ctx : forall rho rhos sigmas r,
SC rhos rho r -> SC (app' rhos sigmas) rho r.
Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.SC_ext_ctx".
destruct rho; simpl; intuition.
nc; auto.
nc; auto.
rewrite app'_ass; rewrite app'_ass in X; auto.
Qed.

Lemma one :
forall rho rhos r,
(letnc rhos' := rhos in letnc r' := r in TypJ rhos' r' rho) ->
(SC rhos rho r -> SN rhos rho r)*(SA rhos rho r -> SC rhos rho r).

Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.one".
induction rho.
simpl.
split.
intuition.
unfold SA, SN.
intros.
split; auto.
intros.
destruct (H1 k _ H2) as [s Hs].
exists s.
nc.
apply Ax2; auto.

rename rho1 into rho.
rename rho2 into sigma.
split.
rename H0 into T.
simpl.
unfold SN.
destruct 1 as [_ X].
intros k mus; intros.
set (rhos':=app' rhos mus).
set (sigmas := let (rhos'') := rhos' in nc (ext_ctx rhos'' k rho)).
assert (T' : letnc rhosig:=app' rhos' sigmas in TypJ rhosig k rho).
unfold sigmas.
nc.
apply ext_ctx_TypJ; destruct H0; auto.
assert (SA (app' rhos' sigmas) rho (nc [k])).
red; intros.
exists [k].
nc.
apply Ax3.
destruct H0; auto.
assert (SC (app' rhos' sigmas) sigma (App' r (nc [k]))).
unfold rhos' in *.
assert (Eq:=app'_ass rhos mus sigmas); rewrite_all Eq; clear Eq.
apply X.
refine (snd (IHrho1 (app' rhos (app' mus sigmas)) (nc [k]) _) _); auto.
nc; auto.
assert (SN (app' rhos' sigmas) sigma (App' r (nc [k]))).
refine (fst (IHrho2 (app' rhos' sigmas) (App' r (nc [k])) _) _); eauto.
try rename X2 into H2.
destruct (H2 (S k) (nc nil)) as [t Ht]; auto.
split.
nc; eauto.
nc.
rewrite <- app_nil_end.
rewrite ext_ctx_length; auto.
unfold F in *; intuition.
exists (\!k:rho,t); auto.
nc.
do_in Ht simpl_list.
intros; apply Ax1; auto.

unfold SA; simpl; split; auto; intros.
rename H0 into T.
refine (snd (IHrho2 (app' rhos sigmas) (App' r s) _) _); eauto.
nc; eauto.
red; intros.
destruct (H1 k (app' sigmas sigmas0)) as [r' Hr'].
split; auto.
nc; eauto.
rewrite <- app'_ass in H2.
nc; eauto.
unfold F in *; intuition.
assert (IH: SN (app' rhos sigmas) rho s).
refine (fst (IHrho1 (app' rhos sigmas) s _) _); auto.
nc; eauto.
destruct (IH k sigmas0) as [s' Hs']; auto.
unfold F in *.
nc; intuition eauto.
exists (r';s').
rewrite <- app'_ass in Hr'.
nc.
eapply Ax4; eauto.
Defined.

Lemma two : forall rho rhos r s,
(letnc rhos' := rhos in letnc r' := r in TypJ rhos' r' rho) ->
SC rhos rho s ->
(letnc rhos' := rhos in letnc r' := r in letnc s' := s in H rhos' rho r' s') ->
SC rhos rho r.
Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.two".
induction rho; simpl; unfold SN; split; auto; intros.
try rename X into H1.
destruct H1 as [T H4].
destruct (H4 k sigmas) as [s0 Hs0]; auto.
unfold F in *; intuition.
nc; intuition.
nc; intuition.
exists s0.
nc.
eapply Ax5; eauto.
apply Ax_H_ext_ctx; auto.
apply IHrho2 with (s:= App' s s0); intuition.
nc; eauto.
nc.
eapply Ax7; eauto.
eapply Ax_H_ext_ctx; eauto.
Defined.



Definition head (rs:list term) :=
match rs with
| nil => [0]
| r::_ => r
end.

Definition tail (rs:list term) :=
match rs with
| nil => nil
| _::rs => rs
end.

Notation head' := (nc1 head).
Notation tail' := (nc1 tail).
Notation "'nth'' n" := (nc2 (@nth (_:Set) n)) (at level 10).

Fixpoint SCs (sigmas:context!) (rhos: context) (rs: (list term)!) {struct rhos} : Type :=
match rhos with
| nil => letnc rs' := rs in rs' = nil
| rho::rhos =>
(letnc rs' := rs in rs' <> nil) **
(SC sigmas rho (head' rs))*(SCs sigmas rhos (tail' rs))
end.

Lemma SCs_length : forall sigmas rhos rs, SCs sigmas rhos rs ->
letnc rs' := rs in length rhos = length rs'.

Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.SCs_length".
induction rhos; simpl; intros.
nc.
subst; auto.
nc.
intuition; generalize (IHrhos _ b); intros.
nc.
rewrite H0; destruct l; firstorder.
Qed.


Lemma SCs_nth : forall sigmas rhos rho rs r n, n < length rhos ->
SCs sigmas rhos rs ->
SC sigmas (nth n rhos rho)  (nth' n rs r).
Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.SCs_nth".
induction rhos.
intros.
elimtype False.
inversion H0.
intros.
simpl in X.
destruct X.
destruct h.
destruct n.
simpl.
assert (nth' 0 rs r = head' rs).
nc; destruct l; try tauto.
rewrite H1; auto.
assert (nth' (S n) rs r = nth' n (tail' rs) r).
nc; destruct l; tauto.
rewrite H1.
simpl; apply IHrhos; intuition.
Defined.

Lemma SCs_ext_ctx : forall sigmas sigmas0 rhos rs,
SCs sigmas rhos rs -> SCs (app' sigmas sigmas0) rhos rs.
Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.SCs_ext_ctx".
induction rhos; simpl; intuition; apply SC_ext_ctx; auto.
Qed.

Notation "'sub'' r" := (nc1 (sub r)) (at level 10).
Notation support' := (nc1 support).

Lemma three : forall r rs rhos sigmas rho,
SCs sigmas rhos (support' rs) -> TypJ rhos r rho ->
SC sigmas rho (sub' r rs).
Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.three".
induction r.
intros.
destruct H0.
simpl in H1.
subst rho.
set (r:=let (rs'):=rs in nc [n-length rs'+shift rs']).
replace (sub' n rs) with (nth' n (support' rs) r).
apply SCs_nth; auto.
inversion_clear H0; auto.
nc; auto.

intros.
set (sigma := typ rhos r2).
assert (H1: TypJ rhos r1 (sigma-->rho)). eauto.
assert (H2: TypJ rhos r2 (typ rhos r2)). eauto.
assert (IH1:= IHr1 rs rhos sigmas (sigma --> rho) X H1).
assert (IH2:= IHr2 rs rhos sigmas (typ rhos r2) X H2).
simpl in IH1.
destruct IH1 as [_ B].
assert (sigmas = app' sigmas (nc nil)).
nc; rewrite <- app_nil_end; auto.
rewrite H3; replace (sub' (r1;r2) rs) with (App' (sub' r1 rs) (sub' r2 rs)).
apply (B (sub' r2 rs) (nc nil)); simpl_list; auto.
rewrite <- H3; auto.
nc; auto.

rename t into rho.
intros.
destruct H0.
subst rho0.
set (freeze:= sub' (\ rho, r) rs).
assert (letnc sigmas':=sigmas in letnc rs':=rs in
(TypJ sigmas' (sub (\ rho, r) rs') (rho --> typ (rho::rhos) r))).
nc.
apply TypJ_sub2 with rhos; auto.
rewrite <- (SCs_length (nc c) rhos X); auto with arith.
intros.
lapply (@SCs_nth (nc c) rhos d' (support' (nc rs')) (nc d) n); auto.
intros.
eapply SC_TypJ; eauto.
simpl; split; intros.
rename rhos' into sigmas'.
nc; auto.
destruct (@one rho (app' sigmas sigmas0) s); auto.
nc; eauto.
set (rs0 := let (rs'):=rs in let (s'):=s in nc ((s'::rs')#rs'.(shift))).
apply two with (sub' r rs0).
nc; eauto.
apply IHr with (rhos:=rho::rhos).
simpl; intuition.
subst.
nc.
simpl in *; discriminate.
replace (head' (support' rs0)) with s; auto.
nc; auto.
apply SCs_ext_ctx; auto.
replace (tail' (support' rs0)) with (support' rs); auto.
nc; auto.
inversion_clear H0; split; auto.
nc; auto.
apply Ax6; auto.
Qed.

Lemma SCs_seq : forall rhos (sigmas:context!) k,
(letnc sigmas':=sigmas in length sigmas' = k) ->
SCs (app' sigmas (nc rhos)) rhos (nc (map Var (seq k (length rhos)))).

Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.SCs_seq".
induction rhos.
simpl; auto.
nc; auto.
simpl.
split.
destruct (@one a (app' sigmas (nc (a::rhos))) (nc [k])).
nc; auto.
subst; split.
constructor.
simpl_list; simpl; omega.
simpl; simpl_list; auto.
rewrite app_nth2; auto.
simpl_arith; simpl; auto.
split.
nc; discriminate.
apply s0.
unfold SA.
intros.
exists [k].
nc.
apply Ax3.
destruct H1; auto.
set (sigmas0 := let (sigmas'):= sigmas in (nc (sigmas'++a::nil))).
replace (app' sigmas (nc (a::rhos))) with (app' sigmas0 (nc rhos)).
apply IHrhos.
nc; simp; auto.
nc; simp; auto.
rewrite app_ass; simpl; auto.
Defined.


Lemma normalizeTheorem :
forall rhos rho r, TypJ rhos r rho -> { s:term | N rhos rho r s }.
Proof. hammer_hook "TaitCoreNc" "TaitCoreNc.NormalizationProofNc.normalizeTheorem".
intros.
destruct (@one rho (nc rhos) (nc r)); auto.
nc; auto.
assert (SC (nc rhos) rho (nc r)).
rewrite <- (sub_id r (length rhos)).
replace (nc (sub r (id (length rhos)))) with (sub' r (nc (id (length rhos)))).
apply three with rhos; auto.
unfold id; simpl.
generalize (@SCs_seq rhos (nc nil) 0); simpl_list; simpl; auto.
intro H1; apply H1.
nc; eauto.
nc; auto.
destruct (s X (length rhos) (nc nil)); intros.
nc; simp; auto.
exists x.
nc; rewrite <- app_nil_end in n; auto.
Defined.

End NormalizationProofNc.
