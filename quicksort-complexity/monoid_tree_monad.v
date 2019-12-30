From Hammer Require Import Hammer.

Set Implicit Arguments.

Require Import List.
Require Import Le.
Require Import Lt.
Require Import Plus.
Require Import Arith.
From QuicksortComplexity Require Import monads.
From QuicksortComplexity Require Import util.
From QuicksortComplexity Require Import monoid_monad_trans.
From QuicksortComplexity Require Import sums_and_averages.
Require Import Rbase.
Require Import Fourier.
From QuicksortComplexity Require ne_tree_monad.

Section contents.

Variable m: Monoid.
Variable X: Set.

Definition pick (l: ne_list.L X): MonoidMonadTrans.M m ne_tree_monad.ext X
:= lift (MonoidMonadTrans.T m) ne_tree_monad.ext X (ne_tree_monad.pick l).

Lemma pick_toLower:
ext_eq pick (@ne_tree_monad.pick _ ∘ ne_list.map (pair (monoid_zero m))).
Proof with auto. hammer_hook "monoid_tree_monad" "monoid_tree_monad.pick_toLower".
unfold compose, ext_eq.
unfold pick.
unfold lift.
simpl.
unfold ne_tree_monad.pick.
intros.
unfold compose.
simpl.
repeat rewrite ne_list.map_map...
Qed.

Lemma In_pick_inv (l: ne_list.L X) (r: prod m X):
ne_tree.In r (pick l) -> fst r = monoid_zero m /\ In (snd r) (ne_list.to_plain l).
Proof with auto. hammer_hook "monoid_tree_monad" "monoid_tree_monad.In_pick_inv".
unfold pick.
simpl.
rewrite ne_list.map_map.
intros.
inversion_clear H.
induction l.
simpl in H0.
inversion_clear H0.
rewrite comp_apply in H.
simpl in H.
rewrite comp_apply in H.
inversion_clear H.
simpl.
firstorder.
simpl in H0.
inversion_clear H0.
rewrite comp_apply in H.
simpl in H.
rewrite comp_apply in H.
simpl in H.
inversion_clear H.
simpl.
firstorder.
destruct (IHl H).
firstorder; try right...
Qed.

End contents.
