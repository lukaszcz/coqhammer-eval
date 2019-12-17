From Hammer Require Import Hammer.

















From Tait Require Export Typing.

Set Implicit Arguments.



Definition is_app (r:term) := match r with
| _;_ => true
| _ => false
end.

Definition left_app (r:term) := match r with
| r;_ => r
| _ => dterm
end.

Definition right_app (r:term) := match r with
| _;r => r
| _ => dterm
end.

Fixpoint get_apps (r:term) : list term :=
match r with
| r;s => get_apps r ++ s::nil
| _ => nil
end.

Fixpoint head_apps (r:term) : term :=
match r with
| r;s => head_apps r
| _ => r
end.

Lemma head_apps_not_App : forall r r1 r2, ~ (head_apps r = r1;r2).
Proof. hammer_hook "Apps" "Apps.head_apps_not_App".
induction r; simpl; intros; auto; discriminate.
Qed.

Definition apps (r:term)(l:list term) := fold_left App l r.
Notation " r ;; l " := (apps r l)(at level 20).

Lemma apps_app : forall r l l', (r;;l);;l' = r;;(l++l').
Proof. hammer_hook "Apps" "Apps.apps_app".
unfold apps; intros; rewrite fold_left_app; auto.
Qed.

Lemma apps_form : forall r, r = (head_apps r);;(get_apps r).
Proof. hammer_hook "Apps" "Apps.apps_form".
induction r;simpl; auto.
rewrite <- apps_app.
rewrite <- IHr1.
simpl; auto.
Qed.

Lemma apps_form_unique1 : forall r r' l l',
r;;l = r';;l' -> is_app r = false -> is_app r' = false -> r = r'.
Proof. hammer_hook "Apps" "Apps.apps_form_unique1".
intros r r'.
assert (forall l l', is_app r = false -> is_app r' = false -> r;; rev l = r';; rev l' -> r = r').
induction l; destruct l'; simpl; auto; repeat rewrite <- apps_app;
simpl; intros; subst; simpl in *; try discriminate.
injection H1; clear H1; intros; subst; eauto.
intros l l'; rewrite <- (rev_involutive l); rewrite <- (rev_involutive l'); eauto.
Qed.

Lemma apps_form_unique2 : forall r r' l l',
r;;l = r';;l' -> is_app r = false -> is_app r' = false -> l = l'.
Proof. hammer_hook "Apps" "Apps.apps_form_unique2".
intros r r'.
assert (forall l l', is_app r = false -> is_app r' = false -> r;; rev l = r';; rev l' -> rev l = rev l').
induction l; destruct l'; simpl; auto; repeat rewrite <- apps_app;
simpl; intros; subst; simpl in *; try discriminate.
injection H1; clear H1; intros; subst; eauto.
rewrite (IHl l'); auto.
intros l l'; rewrite <- (rev_involutive l); rewrite <- (rev_involutive l'); eauto.
Qed.


Lemma apps_occurs : forall l r k, occurs k (r;;l) =
occurs k r || existsb (occurs k) l.
Proof. hammer_hook "Apps" "Apps.apps_occurs".
induction l.
simpl; intros; auto with bool.
simpl; intros.
rewrite IHl.
simpl; auto with bool.
Qed.

Lemma above_apps : forall l r k, above k (r;;l) ->
above k r /\
forall k', k<=k' -> existsb (occurs k') l = false.
Proof. hammer_hook "Apps" "Apps.above_apps".
unfold above; induction l; simpl; auto.
intros.
destruct (IHl (r;a) k H); simpl; intros.
split; intros.
destruct (orb_false_elim _ _ (H0 n H2)); auto.
apply orb_false_intro; auto.
destruct (orb_false_elim _ _ (H0 k' H2)); auto.
Qed.


Lemma CorTyp_apps : forall l r rhos,
CorTyp rhos (r;;l) -> CorTyp rhos r.
Proof. hammer_hook "Apps" "Apps.CorTyp_apps".
induction l.
simpl; auto.
simpl; auto.
intros.
assert (CorTyp rhos (r;a)); auto.
inversion H0; auto.
Qed.

Lemma TypJ_apps : forall l r r' rhos rho sigma,
TypJ rhos r sigma ->
TypJ rhos r' sigma ->
TypJ rhos (r;;l) rho ->
TypJ rhos (r';;l) rho.
Proof. hammer_hook "Apps" "Apps.TypJ_apps".
induction l.
simpl; auto.
intros.
split.
destruct H0; auto.
destruct H.
destruct H1.
destruct H0.
congruence.

simpl; intros.
apply IHl with (r;a) (typ rhos (r';a)); auto.
destruct H.
destruct H0.
split.
apply CorTyp_apps with l; auto.
destruct H1; auto.
simpl.
congruence.

destruct H.
destruct H1.
destruct H0.
split; auto.
assert (CorTyp rhos (r;a)).
apply CorTyp_apps with l; auto.
inversion_clear H5.
econstructor; eauto.
rewrite H4.
rewrite <- H2.
rewrite H8; auto.
Qed.

Lemma sub_apps :
forall l r rs, sub (r;;l) rs = (sub r rs);;(map (fun r => sub r rs) l).
Proof. hammer_hook "Apps" "Apps.sub_apps".
induction l; simpl; auto; intros; rewrite IHl; auto.
Qed.



Definition arrows (rho:type)(l:list type) := fold_right Arrow rho l.
Notation " l ---> rho " := (arrows rho l)(at level 20).

Eval compute in fun r r1 r2 => (r1::r2::nil)--->r.

Lemma arrows_app : forall l l' rho, (l++l')--->rho = l--->(l'--->rho).
Proof. hammer_hook "Apps" "Apps.arrows_app".
induction l; simpl; auto; intros;rewrite IHl; auto.
Qed.
