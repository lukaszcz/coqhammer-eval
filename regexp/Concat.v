From Hammer Require Import Hammer.




Require Export RegExp.Utility.
Require Export RegExp.Definitions.
Require Export RegExp.Boolean.



Lemma Cat_morphism_s : forall s r0 r1 r0' r1',
r0 =R= r1 -> r0' =R= r1' -> (r0 ++ r0') ~= s = (r1 ++ r1') ~= s.
Proof. hammer_hook "Concat" "Concat.Cat_morphism_s".
induction s.

intros r0 r1 r0' r1' H H'.  simpl.  rewrite <- (nu_morphism r0 r1 H).
rewrite <- (nu_morphism r0' r1' H').  auto.

intros r0 r1 r0' r1' H H'.  simpl.  rewrite <- (nu_morphism r0 r1 H).
destruct (nu r0).

repeat erewrite matches_Or.
replace (r1' / a ~= s) with (r0' / a ~= s).
replace ((r1 / a ++ r1') ~= s) with ((r0 / a ++ r0') ~= s).
auto.

eapply IHs; try auto.  eapply derive_morphism; try auto.
unfold ascii_eq; auto.

eapply derive_morphism; try auto.  unfold ascii_eq; auto.

eapply IHs; try auto.  eapply derive_morphism; try auto.
unfold ascii_eq; auto.
Qed.

Add Parametric Morphism : Cat with
signature re_eq ==> re_eq ==> re_eq as Cat_mor.
Proof.
intros x y H x0 y0 H0.  unfold re_eq.  intro s.  eapply Cat_morphism_s; auto.
Qed.




Lemma Cat_left_zero_s : forall s r, (Empty ++ r) ~= s = false.
Proof. hammer_hook "Concat" "Concat.Cat_left_zero_s".
induction s; simpl; auto.
Qed.

Theorem Cat_left_zero : forall r, Empty ++ r =R= Empty.
Proof. hammer_hook "Concat" "Concat.Cat_left_zero".
unfold re_eq.  intros r s.  erewrite Empty_false.
eapply Cat_left_zero_s.
Qed.

Lemma Cat_right_zero_s : forall s r, (r ++ Empty) ~= s = false.
Proof. hammer_hook "Concat" "Concat.Cat_right_zero_s".
induction s; intro r; simpl.
destruct (nu r); simpl; auto.
case_eq (nu r); intro nu_r'.
erewrite matches_Or.  erewrite IHs.  erewrite Empty_false.  simpl; auto.
erewrite IHs.  auto.
Qed.

Theorem Cat_right_zero : forall r, r ++ Empty =R= Empty.
Proof. hammer_hook "Concat" "Concat.Cat_right_zero".
unfold re_eq.  intros r s.  erewrite Empty_false.
eapply Cat_right_zero_s.
Qed.



Lemma matches_Cat : forall s s' r r',
r ~==s -> r' ~== s' -> (r ++ r') ~== (s ++ s')%string.
Proof. hammer_hook "Concat" "Concat.matches_Cat".
induction s.

induction s'.

simpl. intros r r' nu_r nu_r'. rewrite nu_r. rewrite nu_r'. simpl; auto.

simpl. intros r r' nu_r Hra.  rewrite nu_r.  erewrite matches_Or.
rewrite Hra.  destruct ((r / a ++ r') ~= s'); simpl; auto.

intros s' r r' Hr Hr'.
replace (String a s ++ s')%string with (String a (s ++ s'))%string.
rewrite derivation.  simpl.  case_eq (nu r); intro nu_r'.

rewrite derivation in Hr.  erewrite matches_Or.
specialize (IHs s' (r/a) r' Hr Hr').  rewrite IHs.  simpl; auto.

rewrite derivation in Hr.  specialize (IHs s' (r/a) r' Hr Hr').  auto.

simpl; auto.
Qed.



Lemma divide_Cat : forall s r' r'', (r' ++ r'') ~== s ->
{s':string & {s'':string | s = (s' ++ s'')%string /\ r' ~== s' /\ r'' ~== s'' }}.
Proof. hammer_hook "Concat" "Concat.divide_Cat".
induction s.

intros r' r'' H.  exists ""%string.  exists ""%string.  simpl.
split.  auto.  simpl in H.
destruct (nu r'); destruct (nu r''); split; simpl; auto; inversion H.

intros r' r'' H.  simpl in H.
case_eq (nu r'); intro nu_r'; rewrite nu_r' in H; simpl in H.

erewrite matches_Or in H.
case_eq ((r' / a ++ r'') ~= s); case_eq (r'' / a ~= s);
intros Hr''_a Hr'_r''_a; simpl in H.

specialize (IHs (r'/a) r'' Hr'_r''_a).
destruct IHs as [s' [s'' [H1 [H2 H3]]]].
exists (String a s').  exists s''.
split.  simpl.  rewrite <- H1.  auto.  split; auto.

specialize (IHs (r'/a) r'' Hr'_r''_a).
destruct IHs as [s' [s'' [H1 [H2 H3]]]].
exists (String a s').  exists s''.
split.  simpl.  rewrite <- H1.  auto.  split; auto.

exists ""%string.  exists (String a s).
split.  simpl.  auto.  split; simpl; auto.

rewrite Hr''_a in H.  rewrite Hr'_r''_a in H.  simpl in H.  inversion H.

specialize (IHs (r'/a) r'' H).
destruct IHs as [s' [s'' [H1 [H2 H3]]]].
exists (String a s').  exists s''.
split.  simpl.  rewrite <- H1.  auto.  split; auto.
Defined.

Lemma divide_Cat_false : forall s r' r'', (r' ++ r'') ~!= s ->
forall s' s'', ((s = s' ++ s'')%string -> r' ~!= s' \/ r'' ~!= s'').
Proof. hammer_hook "Concat" "Concat.divide_Cat_false".
intros s r' r'' H0.
intros s' s''.
case_eq (r' ~= s'); case_eq (r'' ~= s''); intros Hr''s'' Hr's' Hs; try auto.

specialize(matches_Cat s' s'' r' r'' Hr's' Hr''s'').
left.  rewrite <- Hs in H.  rewrite H0 in H.  discriminate H.
Qed.




Lemma Cat_left_id_s : forall s r, (Eps ++ r) ~= s = r ~= s.
Proof. hammer_hook "Concat" "Concat.Cat_left_id_s".
induction s.
simpl; auto.
simpl. intros r. erewrite matches_Or.
erewrite Cat_left_zero_s.  simpl; auto.
Qed.

Theorem Cat_left_id : forall r, Eps ++ r =R= r.
Proof. hammer_hook "Concat" "Concat.Cat_left_id".
unfold re_eq. intros r s. eapply Cat_left_id_s.
Qed.

Lemma Cat_right_id_s : forall s r, (r ++ Eps) ~= s = r ~= s.
Proof. hammer_hook "Concat" "Concat.Cat_right_id_s".
intros s r.  case_eq (r ~= s); intro Hrs.

replace ((r ++ Eps) ~= s) with ((r ++ Eps) ~= (s ++ EmptyString)).
eapply matches_Cat; auto.
erewrite string_right_id.  auto.

generalize dependent r.
induction s.
intros r H.  simpl in *.  rewrite H.  auto.
intros r H.  simpl in *.  case_eq (nu r); intro nu_r'.

erewrite matches_Or.  erewrite Empty_false.
replace (((r / a ++ Eps) ~= s) || false)%bool with ((r / a ++ Eps) ~= s).
erewrite IHs; auto.
destruct ((r / a ++ Eps) ~= s); auto.

erewrite IHs; auto.
Qed.

Theorem Cat_right_id : forall r, r ++ Eps =R= r.
Proof. hammer_hook "Concat" "Concat.Cat_right_id".
unfold re_eq.  intros r s.  eapply Cat_right_id_s.
Qed.



Lemma matches_Cat_Cat_left : forall s s' s'' r r' r'',
r ~== s -> r' ~== s' -> r'' ~== s'' ->
((r ++ r') ++ r'') ~== ((s ++ s') ++ s'').
Proof. hammer_hook "Concat" "Concat.matches_Cat_Cat_left".
intros s s' s'' r r' r'' H H' H''.
repeat eapply matches_Cat; auto.
Qed.

Lemma matches_Cat_Cat_right : forall s s' s'' r r' r'',
r ~== s -> r' ~== s' -> r'' ~== s'' ->
(r ++ (r' ++ r'')) ~== (s ++ (s' ++ s'')).
Proof. hammer_hook "Concat" "Concat.matches_Cat_Cat_right".
intros s s' s'' r r' r'' H H' H''.
repeat eapply matches_Cat; auto.
Qed.

Lemma Cat_assoc_s : forall s r r' r'',
((r ++ r') ++ r'') ~= s = (r ++ (r' ++ r'')) ~= s.
Proof. hammer_hook "Concat" "Concat.Cat_assoc_s".
intros s r r' r''.  case_eq (((r ++ r') ++ r'') ~= s); intro H; symmetry.

specialize(divide_Cat s (r ++ r') r'' H).  intro H0.
destruct H0 as [srr' [s_'' [H01 [H02 Hs_''r'']]]].
specialize(divide_Cat srr' r r' H02).  intro H0.
destruct H0 as [s_ [s_' [Hs_s_' [Hs_r Hs_'r']]]].
replace s with (s_ ++ (s_' ++ s_''))%string.
eapply matches_Cat_Cat_right; auto.
rewrite <- string_assoc.  rewrite <- Hs_s_'.  rewrite <- H01.  auto.

specialize(divide_Cat_false s (r ++ r') r'' H). intros H0.
case_eq ((r ++ r' ++ r'') ~= s); intro H1.

specialize(divide_Cat s r (r' ++ r'') H1). intros H2.
destruct H2 as [s0 [s_ [Hs_ [Hrs Hs__]]]].
specialize (divide_Cat s_ r' r'' Hs__). intros H2.
destruct H2 as [s0' [s0'' [Hs [Hrs' Hrs'']]]].
specialize (matches_Cat s0 s0' r r' Hrs Hrs'). intros H2.
specialize (matches_Cat (s0 ++ s0')%string s0'' (r ++ r') r'' H2 Hrs'').
intros H3.
replace (((s0 ++ s0') ++ s0'')%string) with s in H3.
rewrite H in H3.  discriminate H3.

erewrite string_assoc.  rewrite <- Hs.  rewrite <- Hs_.  auto.

auto.
Qed.

Theorem Cat_assoc : forall r r' r'', (r ++ r') ++ r'' =R= r ++ (r' ++ r'').
Proof. hammer_hook "Concat" "Concat.Cat_assoc".
intros r r' r''.  unfold re_eq.  intro s.
eapply Cat_assoc_s.
Qed.



Lemma Cat_left_distr_s : forall s r r' r'',
(r ++ (r' || r'')) ~= s = ((r ++ r') || (r ++ r'')) ~= s.
Proof. hammer_hook "Concat" "Concat.Cat_left_distr_s".
induction s.

intros r r' r''.  simpl.
destruct(nu r); destruct(nu r'); destruct(nu r''); auto.

intros r r' r''.  simpl.  case_eq (nu r); intro nu_r.

rewrite (matches_Or s (r / a ++ r' || r'') (r' / a || r'' / a)).
rewrite (IHs (r / a) r' r'').
repeat erewrite matches_Or.
destruct ((r / a ++ r') ~= s); destruct ((r / a ++ r'') ~= s);
destruct (r' / a ~= s); destruct (r'' / a ~= s); auto.

eapply IHs.
Qed.

Lemma Cat_left_distr : forall r r' r'',
(r ++ (r' || r'')) =R= ((r ++ r') || (r ++ r'')).
Proof. hammer_hook "Concat" "Concat.Cat_left_distr".
unfold re_eq.  intros r r' r'' s.  eapply Cat_left_distr_s.
Qed.

Lemma Cat_right_distr_s : forall s r r' r'',
((r || r') ++ r'') ~= s = ((r ++ r'') || (r' ++ r'')) ~= s.
Proof. hammer_hook "Concat" "Concat.Cat_right_distr_s".
induction s.

intros r r' r''.  simpl.
destruct (nu r); destruct (nu r'); destruct (nu r''); auto.

intros r r' r''.  simpl.
case_eq (nu r); intro nu_r; case_eq (nu r'); intro nu_r'; simpl.

rewrite (matches_Or s (r / a || r' / a ++ r'') (r'' / a)).
rewrite (IHs (r / a) (r' / a) r'').
repeat erewrite matches_Or.
destruct ((r / a ++ r'') ~= s); destruct ((r' / a ++ r'') ~= s);
destruct (r'' / a ~= s); auto.

rewrite (matches_Or s (r / a || r' / a ++ r'') (r''/a)).
rewrite (IHs (r/a) (r'/a) r'').
repeat erewrite matches_Or.
destruct ((r / a ++ r'') ~= s); destruct ((r' / a ++ r'') ~= s);
destruct (r'' / a ~= s); auto.

rewrite (matches_Or s (r / a || r' / a ++ r'') (r''/a)).
rewrite (IHs (r/a) (r'/a) r'').
repeat erewrite matches_Or.
destruct ((r / a ++ r'') ~= s); destruct ((r' / a ++ r'') ~= s);
destruct (r'' / a ~= s); auto.

rewrite (IHs (r/a) (r'/a) r'').
erewrite matches_Or.  auto.
Qed.

Lemma Cat_right_distr : forall r r' r'',
((r || r') ++ r'') =R= ((r ++ r'') || (r' ++ r'')).
Proof. hammer_hook "Concat" "Concat.Cat_right_distr".
unfold re_eq.  intros r r' r'' s.  eapply Cat_right_distr_s.
Qed.
