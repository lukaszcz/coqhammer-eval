From Hammer Require Import Hammer.







Require Export RegExp.Utility.
Require Export Setoid.
Require Export Relation_Definitions.



Inductive RegExp : Set :=
| Empty : RegExp
| Eps : RegExp
| Char : ascii -> RegExp
| Cat : RegExp -> RegExp -> RegExp
| Or : RegExp -> RegExp -> RegExp
| Star : RegExp -> RegExp
| Not : RegExp -> RegExp
| And : RegExp -> RegExp -> RegExp.

Notation "a ++ b" := (Cat a b).
Notation "a || b" := (Or a b).



Fixpoint nu(re:RegExp):bool :=
match re with
| Empty => false
| Eps => true
| Char c => false
| Cat r s => (nu r && nu s)%bool
| Or r s => (nu r || nu s)%bool
| Star r => true
| Not r => negb (nu r)
| And r s => (nu r && nu s)%bool
end.



Fixpoint derive(a:ascii)(re:RegExp):RegExp :=
match re with
| Empty => Empty
| Eps => Empty
| Char c => match (ascii_dec c a) with
| left _ => Eps
| right _ => Empty
end
| Cat r s => match (nu r) with
| true => ((derive a r) ++ s) || (derive a s)
| false => (derive a r) ++ s
end
| Or r s => (derive a r) || (derive a s)
| Star r => (derive a r) ++ (Star r)
| Not r => Not (derive a r)
| And r s => And (derive a r) (derive a s)
end.

Notation "re / a" := (derive a re).



Fixpoint matches (re:RegExp)(s:string) : bool :=
match s with
| EmptyString => nu re
| String a w => matches (re / a) w
end.

Notation "re ~= s" := (matches re s) (at level 60).
Notation "re ~== s" := (matches re s = true) (at level 60).
Notation "re ~!= s" := (matches re s = false) (at level 60).



Theorem derivation : forall (a:ascii)(w:string)(re:RegExp),
re ~= (String a w) = (re / a) ~= w.
Proof. hammer_hook "Definitions" "Definitions.derivation".
intros a w re.  simpl.  auto.
Qed.




Definition re_eq (re re':RegExp) : Prop := forall s, re ~= s = re' ~= s.

Notation "a =R= b" := (re_eq a b) (at level 70).

Lemma re_eq_refl : reflexive RegExp re_eq.
Proof. hammer_hook "Definitions" "Definitions.re_eq_refl".
unfold reflexive. intro x. unfold re_eq. intro s.  auto.
Qed.

Lemma re_eq_sym : symmetric RegExp re_eq.
Proof. hammer_hook "Definitions" "Definitions.re_eq_sym".
unfold symmetric. intros x y H.  unfold re_eq in *.
intros s.  eauto.
Qed.

Lemma re_eq_trans : transitive RegExp re_eq.
Proof. hammer_hook "Definitions" "Definitions.re_eq_trans".
unfold transitive.  intros x y z.  unfold re_eq in *. intros Hxy Hyz s.
transitivity (y ~= s); eauto.
Qed.

Add Parametric Relation : RegExp re_eq
reflexivity proved by re_eq_refl
symmetry proved by re_eq_sym
transitivity proved by re_eq_trans
as RegExp_setoid.



Lemma nu_equals : forall r r', r =R= r' -> nu r = nu r'.
Proof. hammer_hook "Definitions" "Definitions.nu_equals".
unfold re_eq in *.  intros r r' H.
specialize (H ""%string); simpl in H.  auto.
Qed.

Add Parametric Morphism : nu with
signature re_eq ==> bool_eq as nu_morphism.
Proof.
intros x y H.  eapply nu_equals.  auto.
Qed.

Lemma derive_equals : forall r r', r =R= r' -> (forall a, r / a =R= r' / a).
Proof. hammer_hook "Definitions" "Definitions.derive_equals".
intros r r' H.  unfold re_eq.  intros a s.
repeat rewrite <- derivation.
unfold re_eq in H.  eauto.
Qed.

Lemma derive_equals_inv : forall r r',
(forall a, (r / a) =R= (r' / a)) -> nu r = nu r' -> r =R= r'.
Proof. hammer_hook "Definitions" "Definitions.derive_equals_inv".
intros r r' Ha Hnu. unfold re_eq.
induction s.
simpl.  auto.
repeat erewrite derivation.  eapply Ha.
Qed.

Add Parametric Morphism : derive with
signature ascii_eq ==> re_eq ==> re_eq as derive_morphism.
Proof.
intros x y H x0 y0 H0.
inversion H.  rewrite <- H1.
eapply derive_equals.  auto.
Qed.
