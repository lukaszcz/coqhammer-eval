From Hammer Require Import Hammer.




Require Export RegExp.Utility.
Require Export RegExp.Definitions.
Require Export RegExp.Boolean.
Require Export RegExp.Concat.

Unset Standard Proposition Elimination Names.



Lemma Char_true : forall c, (Char c) ~== (String c ""%string).
Proof. hammer_hook "Char" "Char.Char_true".
intro c.  simpl.
destruct(ascii_dec c c); simpl.
auto.
elim n. auto.
Qed.

Lemma Char_false : forall s c, s <> (String c ""%string) -> (Char c) ~!= s.
Proof. hammer_hook "Char" "Char.Char_false".
induction s.
intros c Hs.  simpl.  auto.
induction s; intros c Hs; simpl.
destruct(ascii_dec c a); simpl.
rewrite e in Hs.  elim Hs.  auto.
auto.
destruct(ascii_dec c a); simpl.
eapply Empty_false.
eapply Empty_false.
Qed.

Add Parametric Morphism : Char with
signature ascii_eq ==> re_eq as Char_mor.
Proof.
intros x y Hxy.  destruct Hxy.  setoid_reflexivity.
Qed.

Lemma derive_Char_is_id : forall a r, derive a (Char a ++ r) =R= r.
Proof. hammer_hook "Char" "Char.derive_Char_is_id".
intros a r.  simpl.
destruct(ascii_dec a a).
setoid_rewrite Cat_left_id.  setoid_reflexivity.
elim n.  auto.
Qed.




Fixpoint string_to_re (s:string):RegExp :=
match s with
| EmptyString => Eps
| String a s' => (Char a) ++ (string_to_re s')
end.

Lemma string_to_re_true : forall s:string, (string_to_re s) ~== s.
Proof. hammer_hook "Char" "Char.string_to_re_true".
induction s.
simpl.  auto.
simpl.  destruct(ascii_dec a a).
erewrite Cat_left_id_s.  auto.
elim n.  auto.
Qed.

Lemma string_to_re_false : forall s s':string, s <> s' -> (string_to_re s) ~!= s'.
Proof. hammer_hook "Char" "Char.string_to_re_false".
induction s.
intros s' Hs.  simpl.  eapply Eps_false.  auto.
induction s'.
intros Hs.  simpl.  auto.
intro Hs.  simpl.  destruct(ascii_dec a a0).
erewrite Cat_left_id_s.  rewrite e in Hs.  eapply IHs.
destruct(string_dec s s').
rewrite e0 in Hs.  elim Hs. auto.
auto.
erewrite Cat_left_zero_s.  auto.
Qed.
