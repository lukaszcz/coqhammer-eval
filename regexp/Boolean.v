From Hammer Require Import Hammer.




Require Export RegExp.Utility.
Require Export RegExp.Definitions.




Lemma Empty_false : forall s, Empty ~!= s.
Proof. hammer_hook "Boolean" "Boolean.Empty_false".
induction s.
reflexivity.
simpl.  apply IHs.
Qed.




Lemma Eps_true : Eps ~== EmptyString.
Proof. hammer_hook "Boolean" "Boolean.Eps_true".
simpl.  reflexivity.
Qed.

Lemma Eps_false : forall s, s <> ""%string -> Eps ~!= s.
Proof. hammer_hook "Boolean" "Boolean.Eps_false".
induction s.
intro Hs. elim Hs. auto.
intro Has. simpl. eapply Empty_false.
Qed.




Add Parametric Morphism : Or with
signature re_eq ==> re_eq ==> re_eq as Or_morphism.
Proof.
intros x y H x0 y0 H0.  unfold re_eq in *.  intro s.
generalize dependent x.  generalize dependent y.
generalize dependent x0. generalize dependent y0.
induction s.

intros y0 x0 H0 y x H.  specialize (H0 ""%string).  specialize (H ""%string).
simpl in *.  rewrite <- H0.  rewrite <- H.  reflexivity.

simpl.  intros y0 x0 H0 y x H.  eapply IHs.
intros.  repeat rewrite <- derivation.  eapply H0.
intros.  repeat rewrite <- derivation.  eapply H.
Qed.

Add Parametric Morphism : And with
signature re_eq ==> re_eq ==> re_eq as And_morphism.
Proof.
intros x y H x0 y0 H0.  unfold re_eq in *.  intros s.
generalize dependent x.  generalize dependent y.
generalize dependent x0. generalize dependent y0.
induction s.

intros y0 x0 H0 y x H.  specialize (H0 ""%string).  specialize (H ""%string).
simpl in *.  rewrite <- H0.  rewrite <- H.  reflexivity.

simpl.  intros y0 x0 H0 y x H.  eapply IHs.
intros s0.  repeat rewrite <- derivation.  eapply H0.
intros s0.  repeat rewrite <- derivation.  eapply H.
Qed.

Add Parametric Morphism : Not with
signature re_eq ==> re_eq as Not_morphism.
Proof.
intros x y H.  unfold re_eq in *.  intros s.
generalize dependent x. generalize dependent y.
induction s.

intros y x H.  specialize (H ""%string).  simpl in *.  rewrite <- H.  reflexivity.

simpl.  intros y x H.  eapply IHs.
intros s0.  repeat rewrite <- derivation.  eapply H.
Qed.



Lemma matches_Or : forall s r r',  r || r' ~= s = ((r ~= s) || (r' ~= s))%bool.
Proof. hammer_hook "Boolean" "Boolean.matches_Or".
induction s.
simpl.  reflexivity.
simpl.  intros r r'.  eapply IHs.
Qed.

Lemma matches_And : forall s r r',  matches (And r r') s = ((r ~= s) && (r' ~= s))%bool.
Proof. hammer_hook "Boolean" "Boolean.matches_And".
induction s.
simpl.  reflexivity.
simpl.  intros.  eapply IHs.
Qed.

Lemma matches_Not : forall s r,  (Not r) ~= s = negb (r ~= s).
Proof. hammer_hook "Boolean" "Boolean.matches_Not".
induction s.
simpl.  reflexivity.
simpl.  intros.  eapply IHs.
Qed.




Lemma Or_comm_s : forall s r r', (r || r') ~= s = (r' || r) ~= s.
Proof. hammer_hook "Boolean" "Boolean.Or_comm_s".
intros s r r'.  repeat erewrite matches_Or.
destruct (r ~= s); destruct (r' ~= s); reflexivity.
Qed.

Theorem Or_comm : forall r r', r || r' =R= r' || r.
Proof. hammer_hook "Boolean" "Boolean.Or_comm".
unfold re_eq.  intros r r' s.  eapply Or_comm_s.
Qed.

Lemma Or_assoc_s : forall s r r' r'',
((r || r') || r'') ~= s = (r || (r' || r'')) ~= s.
Proof. hammer_hook "Boolean" "Boolean.Or_assoc_s".
intros.   repeat erewrite matches_Or.
destruct (r ~= s); destruct (r' ~= s); destruct (r'' ~= s); reflexivity.
Qed.

Theorem Or_assoc : forall r r' r'', (r || r') || r'' =R= r || (r' || r'').
Proof. hammer_hook "Boolean" "Boolean.Or_assoc".
unfold re_eq.  intros r r' r'' s.  eapply Or_assoc_s.
Qed.

Lemma And_comm : forall r r', And r r' =R= And r' r.
Proof. hammer_hook "Boolean" "Boolean.And_comm".
unfold re_eq.  intros r r' s.  repeat erewrite matches_And.
destruct (r ~= s); destruct (r' ~= s); reflexivity.
Qed.

Lemma And_assoc : forall r r' r'', And (And r r') r'' =R= And r (And r' r'').
Proof. hammer_hook "Boolean" "Boolean.And_assoc".
unfold re_eq.  intros r r' r'' s.  repeat erewrite matches_And.
destruct (r ~= s); destruct (r' ~= s); destruct (r'' ~= s); reflexivity.
Qed.



Lemma Or_left_id_s : forall s r, (Empty || r) ~= s = r ~= s.
Proof. hammer_hook "Boolean" "Boolean.Or_left_id_s".
induction s.
simpl.  reflexivity.
simpl.  intros r.  eapply IHs.
Qed.

Theorem Or_left_id : forall r, Empty || r =R= r.
Proof. hammer_hook "Boolean" "Boolean.Or_left_id".
unfold re_eq.  intros r s.  eapply Or_left_id_s.
Qed.

Theorem Or_right_id : forall r, r || Empty =R= r.
intros.  setoid_rewrite Or_comm.
eapply Or_left_id.
Qed.

Corollary Or_right_id_s : forall s r, (r || Empty) ~= s = r ~= s.
Proof. hammer_hook "Boolean" "Boolean.Or_right_id_s".
intros s r.  specialize Or_right_id.
intros H.  unfold re_eq in H.  eapply H.
Qed.



Lemma Or_idem_s : forall s r, (r || r) ~= s = r ~= s.
Proof. hammer_hook "Boolean" "Boolean.Or_idem_s".
intros s r.  erewrite matches_Or.  destruct (r ~= s); reflexivity.
Qed.

Theorem Or_idem : forall r, r || r =R= r.
Proof. hammer_hook "Boolean" "Boolean.Or_idem".
unfold re_eq.  intros r s.  eapply Or_idem_s.
Qed.
