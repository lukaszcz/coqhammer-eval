From Hammer Require Import Hammer.

Set Implicit Arguments.

Require Import List.
From QuicksortComplexity Require Import monads.
From QuicksortComplexity Require Import monoid_monad_trans.
From QuicksortComplexity Require qs_definitions.
Import qs_definitions.mon_nondet.
From QuicksortComplexity Require ne_tree_monad.
Require Import Plus.
From QuicksortComplexity Require Import monoid_tree_monad.
From QuicksortComplexity Require Import sort_order.

Section contents.

Variable X : E.

Definition M: Monad := MonoidMonadTrans.M NatAddMonoid ne_tree_monad.ext.

Definition cmp (x y : X) : M comparison :=
@ret ne_tree_monad.M _ (1%nat, sort_order.Ecmp X x y).

Definition pick := monoid_tree_monad.pick NatAddMonoid.

Lemma Mext: extMonad M.
Proof. hammer_hook "NDP" "NDP.Mext". exact (MonoidMonadTrans.Mext NatAddMonoid ne_tree_monad.ext). Qed.

Lemma partition d l: partition M cmp d l = ne_tree.Leaf (length l, qs_definitions.simplerPartition X d l).
Proof with auto. hammer_hook "NDP" "NDP.partition".
induction l...
simpl.
rewrite (@mon_assoc (ne_tree_monad.M)).
rewrite IHl.
simpl.
rewrite plus_0_r...
Qed.

Definition qs := qs cmp pick.

End contents.
