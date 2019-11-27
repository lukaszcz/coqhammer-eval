From Hammer Require Import Hammer.





Require Import List.
From hahn Require Import HahnBase.
Set Implicit Arguments.




Section FunctionUpdate.

Variables (A B: Type).

Definition upd (f : A -> B) a b x :=
if excluded_middle_informative (x = a) then b else f x.

Lemma upds f a b : upd f a b a = b.
Proof. hammer_hook "HahnFun" "HahnFun.upds". unfold upd; desf. Qed.

Lemma updo f a b c (NEQ: c <> a) : upd f a b c = f c.
Proof. hammer_hook "HahnFun" "HahnFun.updo". unfold upd; desf. Qed.

Lemma updss f l x y : upd (upd f l x) l y = upd f l y.
Proof. hammer_hook "HahnFun" "HahnFun.updss".
extensionality z; unfold upd; desf.
Qed.

Lemma updC l l' (NEQ: l <> l') f x y :
upd (upd f l x) l' y = upd (upd f l' y) l x.
Proof. hammer_hook "HahnFun" "HahnFun.updC".
extensionality z; unfold upd; desf.
Qed.

Lemma updI f a : upd f a (f a) = f.
Proof. hammer_hook "HahnFun" "HahnFun.updI".
extensionality a'; unfold upd; desf.
Qed.

Lemma map_upd_irr a l (NIN: ~ In a l) f b :
map (upd f a b) l = map f l.
Proof. hammer_hook "HahnFun" "HahnFun.map_upd_irr".
unfold upd; induction l; ins.
apply not_or_and in NIN; desf; f_equal; eauto.
Qed.

End FunctionUpdate.

Ltac rupd := repeat first [rewrite upds | rewrite updo ; try done].





Section DecidableUpdate.

Variables (A: eqType) (B: Type).

Definition mupd (f: A -> B) y z :=
fun x => if eq_op x y then z else f x.

Lemma mupds f x y : mupd f x y x = y.
Proof. hammer_hook "HahnFun" "HahnFun.mupds". by unfold mupd; desf; desf. Qed.

Lemma mupdo f x y z : x <> z -> mupd f x y z = f z.
Proof. hammer_hook "HahnFun" "HahnFun.mupdo". by unfold mupd; desf; desf. Qed.

Lemma mupdss f l x y : mupd (mupd f l x) l y = mupd f l y.
Proof. hammer_hook "HahnFun" "HahnFun.mupdss".
extensionality z; unfold mupd; desf; desf.
Qed.

Lemma mupdC l l' (NEQ: l <> l') f x y :
mupd (mupd f l x) l' y = mupd (mupd f l' y) l x.
Proof. hammer_hook "HahnFun" "HahnFun.mupdC".
extensionality z; unfold mupd; desf; desf.
Qed.

Lemma mupdI f a : mupd f a (f a) = f.
Proof. hammer_hook "HahnFun" "HahnFun.mupdI".
extensionality z; unfold mupd; desf; desf.
Qed.

Lemma map_mupd_irr a l (NIN: ~ In a l) f b :
map (mupd f a b) l = map f l.
Proof. hammer_hook "HahnFun" "HahnFun.map_mupd_irr".
unfold mupd; induction l; ins.
apply not_or_and in NIN; desf; desf; f_equal; eauto.
Qed.

End DecidableUpdate.

Arguments mupd [A B] f y z x.
