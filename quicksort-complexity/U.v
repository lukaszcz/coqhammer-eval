From Hammer Require Import Hammer.

Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

From QuicksortComplexity Require Import util.
Require Import Le.
Require Import EqNat.
Require Import Compare_dec.
Require Import Bool.
Require Import Lt.
From QuicksortComplexity Require Import list_utils.
Require Import List.
Require Import Compare_dec.
From QuicksortComplexity Require Import monads.
From QuicksortComplexity Require Import monoid_monad_trans.
From QuicksortComplexity Require Import nat_seqs.
From QuicksortComplexity Require Import qs_definitions.
From QuicksortComplexity Require Import monoid_expec.
From QuicksortComplexity Require qs_parts.
From QuicksortComplexity Require Import sort_order.
From QuicksortComplexity Require Import indices.
Require Import Arith.
From QuicksortComplexity Require Import nat_below.
Require Vector.
From QuicksortComplexity Require ne_tree_monad.

Import mon_nondet.

Section contents.

Variable (e: E) (ol: list e).



Definition monoid := ListMonoid.M (nat * nat).

Definition M: Monad := MonoidMonadTrans.M monoid ne_tree_monad.ext.

Lemma Mext: extMonad M.
Proof. hammer_hook "U" "U.Mext". exact (MonoidMonadTrans.Mext monoid ne_tree_monad.ext). Qed.

Definition unordered_nat_pair (x y: nat): nat * nat :=
if le_lt_dec x y then (x, y) else (y, x).

Definition cmp (x y: Index e ol): M comparison
:= ret (unordered_nat_pair x y :: nil, Ecmp e (subscript x) (subscript y)).

Definition homo: monoidHomo monoid NatAddMonoid (fun x => length x).
Proof with auto. hammer_hook "U" "U.homo". apply Build_monoidHomo... simpl. intros. rewrite app_length... Qed.

Definition pick := monoid_tree_monad.pick monoid.

Require Import Rdefinitions.

Lemma partition d (l: list (Index e ol)):
partition M cmp d l =
ne_tree.Leaf (map (fun i: Index e ol => unordered_nat_pair i d) l, simplerPartition (UE e ol) d l).
Proof with auto. hammer_hook "U" "U.partition".
induction l...
simpl.
rewrite (@mon_assoc (ne_tree_monad.M)).
rewrite IHl.
simpl.
rewrite app_nil_r...
Qed.

Lemma simplePartition_component (ee: E) i cr l:
proj1_sig (simplerPartition ee i l) cr =
filter (fun f => unsum_bool (cmp_cmp (Ecmp ee f i) cr)) l.
Proof with auto. hammer_hook "U" "U.simplePartition_component".
induction l...
simpl.
rewrite IHl.
destruct (Ecmp ee a i); destruct cr...
Qed.

Section Uqs_ind.

Variable P: list (Index e ol) -> M (list (Index e ol)) -> Prop.
Hypothesis Pnil: P nil (ret nil).

Hypothesis Pcons: forall n (v: Vector.t (Index e ol) (S n)),
(forall x0 cr, P (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) cr)) (vec.to_list (vec.remove v x0))) (qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) cr)) (vec.to_list (vec.remove v x0))))) ->
P (vec.to_list v)
(ne_tree.Node
(ne_list.map
(fun x0: natBelow (S n) =>
ne_tree.map
(map_fst (C:=list (Index e ol)) (app (map (fun i0: Index e ol => unordered_nat_pair i0 (vec.nth v x0)) (vec.to_list (vec.remove v x0)))))
(foo <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Lt)) (vec.to_list (vec.remove v x0)));
bar <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Gt)) (vec.to_list (vec.remove v x0)));
ret (foo ++ (vec.nth v x0 :: filter (fun f0: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f0 (vec.nth v x0)) Eq)) (vec.to_list (vec.remove v x0))) ++ bar)))
(ne_list.from_vec (vec.nats 0 (S n))))).

Theorem qs_ind: forall l, P l (qs cmp pick l).
Proof with auto. hammer_hook "U" "U.qs_ind".
apply qs_parts.rect...
apply Mext.
intros.
unfold qs_parts.body.
replace (qs_parts.selectPivotPart M pick cmp v) with (ne_tree.Node (ne_list.map (fun x0: natBelow (S n) => ne_tree.map (map_fst (app (map (fun i0: Index e ol => unordered_nat_pair i0 ((vec.nth v x0))) (vec.to_list (vec.remove v x0))))) (
foo <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Lt)) (vec.to_list (vec.remove v x0)));
bar <- qs cmp pick (filter (fun f: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f (vec.nth v x0)) Gt)) (vec.to_list (vec.remove v x0)));
ret (m:=ne_tree_monad.M) (nil, foo ++ (vec.nth v x0 :: filter (fun f0: Index e ol => unsum_bool (cmp_cmp (Ecmp (UE e ol) f0 (vec.nth v x0)) Eq)) (vec.to_list (vec.remove v x0))) ++ bar))) (ne_list.from_vec (vec.nats 0 (S n))))).
simpl @ret in Pcons.
Focus 1.
specialize (Pcons v).
simpl vec.to_list in Pcons.
apply Pcons. clear Pcons.
intros.
apply H.
rewrite length_filter.
apply le_lt_trans with (length (vec.to_list (vec.remove v x0))).
apply count_le.
rewrite vec.length...
unfold qs_parts.selectPivotPart.
unfold qs_parts.partitionPart.
unfold qs_parts.lowRecPart.
simpl.
f_equal.
repeat rewrite ne_list.map_map.
apply ne_list.map_ext. intro.
unfold compose. simpl.
rewrite ne_tree_monad.map_bind.
rewrite (@mon_assoc (ne_tree_monad.M)).
rewrite partition. simpl.
rewrite (@mon_assoc (ne_tree_monad.M)). simpl.
rewrite (@mon_assoc (ne_tree_monad.M)). simpl.
rewrite (@simplePartition_component (UE e ol)).
apply ne_tree_monad.ext. intro.
rewrite (@mon_assoc (ne_tree_monad.M)). simpl.
rewrite ne_tree_monad.map_bind.
rewrite (@mon_assoc (ne_tree_monad.M)). simpl.
rewrite (@mon_assoc (ne_tree_monad.M)). simpl.
rewrite (@simplePartition_component (UE e ol)).
apply ne_tree_monad.ext. intro.
unfold compose, map_fst.
simpl.
rewrite (@simplePartition_component (UE e ol)).
reflexivity.
Qed.

End Uqs_ind.

Lemma UcmpDec (x y: nat * nat): { x = y } + { x <> y }.
Proof with auto. hammer_hook "U" "U.UcmpDec".
intros.
destruct x.
destruct y.
destruct (eq_nat_dec n n1).
destruct (eq_nat_dec n0 n2).
subst.
left...
right. intro. inversion H...
right. intro. inversion H...
Qed.

Definition UcmpCmp (x y: nat * nat): bool := unsum_bool (UcmpDec x y).

Definition ijcount (i j: nat): monoid -> nat := count (UcmpCmp (i, j)).

Lemma ijcount_0 i j l: ~ In (i, j) l -> ijcount i j l = 0.
Proof with auto. hammer_hook "U" "U.ijcount_0".
unfold ijcount.
intros.
apply count_0.
intros.
unfold UcmpCmp.
case_eq (UcmpDec (i, j) x); intros...
elimtype False.
apply H.
rewrite e0...
Qed.

Lemma hom_ijcount i j: monoidHomo monoid NatAddMonoid (ijcount i j).
Proof with auto. hammer_hook "U" "U.hom_ijcount".
unfold ijcount.
intros.
apply Build_monoidHomo; intros; simpl...
apply count_app.
Qed.

Hint Resolve hom_ijcount.

Lemma ijcount_eq_count i j: ijcount i j = eq_count UcmpDec (i, j).
Proof. hammer_hook "U" "U.ijcount_eq_count". auto. Qed.

Definition qs: list (Index e ol) -> M (list (Index e ol)) := qs cmp pick.

End contents.
