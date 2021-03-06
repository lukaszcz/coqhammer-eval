From Hammer Require Import Hammer.

Set Implicit Arguments.

From QuicksortComplexity Require Import util.
Require Import List.
Require Import Le.
Require Import Lt.
Require Import Plus.
From QuicksortComplexity Require Import monads.
Require Import Coq.Program.Wf.
From QuicksortComplexity Require Import nat_seqs.
From QuicksortComplexity Require Import list_utils.
Require Import Bool.
Require Import Recdef.
From QuicksortComplexity Require Import monoid_monad_trans.
Require Import Compare_dec.
Require Coq.Program.Wf.
Require Import Wf_nat.
From QuicksortComplexity Require Import arith_lems.
From QuicksortComplexity Require ne_list.
Require Import Omega.
From QuicksortComplexity Require fix_measure_utils.



Set Shrink Obligations.

Definition numbers: list nat := 3 :: 1 :: 0 :: 4 :: 5 :: 2 :: nil.

Hint Resolve length_filter_le.

Module nonmonadic.
Section nonmonadic.

Variables (T: Set) (le: T -> T -> bool).

Definition gt (x y: T): bool := negb (le x y).

Program Fixpoint qs (l: list T) {measure (length l) lt}: list T :=
match l with
| nil => nil
| pivot :: t => qs (filter (gt pivot) t) ++ (pivot :: nil) ++ qs (filter (le pivot) t)
end.

Next Obligation. simpl; auto with arith. Qed.
Next Obligation. simpl; auto with arith. Qed.

Definition body (l : list T) (qs0 : {l' : list T | length l' < length l} -> list T) :=
match l as l0 return (l0 = l -> list T) with
| nil => fun _ => nil
| pivot :: t0 => fun Heq_l =>
qs0 (exist (fun l' => length l' < length l) (filter (gt pivot) t0) (qs_obligation_1 (fun l H => qs0 (exist _ l H)) Heq_l)) ++
(pivot :: nil) ++
qs0 (exist (fun l' => length l' < length l) (filter (le pivot) t0) (qs_obligation_2 (fun l H => qs0 (exist _ l H)) Heq_l))
end refl_equal.

Lemma body_eq:
forall (x0 : list T) (g h0 : {y : list T | length y < length x0} -> list T),
(forall (x : list T) (p p' : length x < length x0),
g (exist (fun y : list T => length y < length x0) x p) =
h0 (exist (fun y : list T => length y < length x0) x p')) ->
body x0 g = body x0 h0.
Proof with auto. hammer_hook "qs_definitions" "qs_definitions.nonmonadic.body_eq".
intros.
destruct x0...
simpl.
f_equal...
f_equal...
Qed.

Lemma unfold: forall l, qs l = Fix_sub (list T) (MR lt (fun l0 : list T => length l0)) qs_obligation_3 (fun _ : list T => list T) body l.
Proof. hammer_hook "qs_definitions" "qs_definitions.nonmonadic.unfold". reflexivity. Qed.

Lemma qs_unfold (t: list T) (h: T): qs (h :: t) = qs (filter (gt h) t) ++ (h :: nil) ++ qs (filter (le h) t).
Proof with auto. hammer_hook "qs_definitions" "qs_definitions.nonmonadic.qs_unfold".
intros.
unfold qs.
fold body.
rewrite fix_measure_utils.unfold.
unfold body at 1.
simpl proj1_sig.
f_equal.
apply body_eq.
Qed.

Section rect.

Variable P: list T -> list T -> Prop.

Hypothesis Pnil: P nil nil.

Hypothesis Pcons: forall h t,
P (filter (gt h) t) (qs (filter (gt h) t)) ->
P (filter (le h) t) (qs (filter (le h) t)) -> P (h :: t) (qs (filter (gt h) t) ++ h :: nil ++ qs (filter (le h) t)).

Lemma qs_rect: forall l, P l (qs l).
Proof with auto with arith. hammer_hook "qs_definitions" "qs_definitions.nonmonadic.qs_rect".
unfold qs.
fold body.
apply fix_measure_utils.rect.
apply body_eq.
intros.
destruct x...
simpl.
apply Pcons; apply H; unfold MR; simpl...
Qed.

End rect.



End nonmonadic.
End nonmonadic.



Module mon_det.
Section mon_det.

Variables (M: Monad) (T: Set).

Definition filter (c: T -> M bool) (l: list T): M { l': list T | length l' <= length l }.

Proof with auto with arith. hammer_hook "qs_definitions" "qs_definitions.mon_det.filter".
induction l.
refine (ret (exist _ nil _))...
refine (
b <- c a ;
t <- IHl ;
ret (if b then exist _ (a :: proj1_sig t) _ else exist _ (proj1_sig t) _)
); simpl; destruct t...
Defined.

Lemma hm (e: extMonad M) c l: forall U (f: list T -> M U) g,
ext_eq g (f ∘ @proj1_sig _ _) -> filter c l >>= g = filterM c l >>= f.
Proof with auto. hammer_hook "qs_definitions" "qs_definitions.mon_det.hm".
induction l.
simpl. intros.
repeat rewrite mon_lunit.
rewrite H.
unfold compose...
intros.
simpl.
repeat rewrite mon_assoc.
apply e. intro.
repeat rewrite mon_assoc.
apply IHl.
intro. unfold compose.
repeat rewrite mon_lunit.
rewrite H.
unfold compose.
destruct x...
Qed.

Fixpoint simple_filter (c: T -> M bool) (l: list T): M (list T) :=
match l with
| nil => ret nil
| h :: t =>
t' <- simple_filter c t ;
b <- c h ;
ret (if b then h :: t' else t')
end.

Definition fold_filter (c: T -> M bool): list T -> M (list T) :=
foldrM (fun x l => b <- c x ; ret (if b then x :: l else l)) nil.

Lemma simple_fold_filter: forall c l, simple_filter c l = fold_filter c l.
Proof with auto. hammer_hook "qs_definitions" "qs_definitions.mon_det.simple_fold_filter".
unfold fold_filter.
induction l...
simpl.
rewrite IHl...
Qed.

Variable le: T -> T -> M bool.

Definition gt (x y: T): M bool := liftM negb (le x y).

Program Fixpoint qs (l: list T) {measure (length l) lt}: M (list T) :=
match l with
| nil => ret nil
| pivot :: t =>
lower <- filter (gt pivot) t >>= (fun l => qs l);
upper <- filter (le pivot) t >>= (fun l => qs l);
ret (lower ++ pivot :: upper)
end.

Next Obligation. simpl. auto with arith. Qed.
Next Obligation. simpl. auto with arith. Qed.


Definition body (l: list T) (qs0: {l': list T | length l' < length l} -> M (list T)) :=
match l as l1 return (l1 = l -> M (list T)) with
| nil => fun _ => ret (m:=M) nil
| pivot :: t => fun Heq_l =>
lower <-
x <- filter (gt pivot) t;
qs0 (exist _ (proj1_sig x) (qs_obligation_1 (fun l H => qs0 (exist _ l H)) Heq_l x));
upper <-
x <- filter (le pivot) t;
qs0 (exist _ (proj1_sig x) (qs_obligation_2 (fun l H => qs0 (exist _ l H)) Heq_l x));
ret (m:=M) (lower ++ pivot :: upper)
end refl_equal.

Lemma unfold: forall l, qs l =
Fix_sub (list T) (MR lt (fun l0 : list T => length l0)) qs_obligation_3 (fun _ : list T => M (list T)) body l.
Proof. hammer_hook "qs_definitions" "qs_definitions.mon_det.unfold". reflexivity. Qed.

Variable e: extMonad M.

Lemma body_eq:
forall (x0 : list T)
(g h : {y : list T | length y < length x0} -> M (list T)),
(forall (x1 : list T) (p p' : length x1 < length x0),
g (exist (fun y : list T => length y < length x0) x1 p) =
h (exist (fun y : list T => length y < length x0) x1 p')) ->
body x0 g = body x0 h.
Proof with auto. hammer_hook "qs_definitions" "qs_definitions.mon_det.body_eq".
intros. destruct x0...
simpl.
rewrite mon_assoc. rewrite mon_assoc.
apply e. intro.
simpl @length in H.
erewrite H.
apply e. intro.
do 2 rewrite mon_assoc.
apply e. intro.
erewrite H...
Qed.

Lemma unfold' pivot t: qs (pivot :: t) =
lower <- filterM (gt pivot) t >>= qs;
upper <- filterM (le pivot) t >>= qs;
ret (lower ++ pivot :: upper).
Proof with auto. hammer_hook "qs_definitions" "qs_definitions.mon_det.unfold'".
intros.
unfold qs at 1.
simpl.
fold body.
rewrite fix_measure_utils.unfold.
simpl.
repeat rewrite mon_assoc.
apply hm...
intro.
unfold compose.
unfold qs.
fold body.
apply e.
intro.
repeat rewrite mon_assoc.
apply hm...
intro...
apply body_eq.
Qed.



End mon_det.
End mon_det.

Arguments mon_det.qs [M T].

Lemma mon_det_nonmonadic_eq (X: Set) (Xle: X -> X -> Prop) (leb: X -> X -> IdMonad.M bool):
forall l, mon_det.qs leb l = nonmonadic.qs leb l.
Proof with auto. hammer_hook "qs_definitions" "qs_definitions.mon_det_nonmonadic_eq".
intros.
pattern l, (nonmonadic.qs leb l).
apply nonmonadic.qs_rect...
simpl.
intros.
rewrite mon_det.unfold'.
simpl. unfold IdMonad.bind, IdMonad.ret.
do 2 rewrite <- filterM_id.
rewrite H0.
unfold mon_det.gt.
unfold nonmonadic.gt in H.
simpl. unfold IdMonad.bind, IdMonad.ret.
rewrite H...
intro...
Qed.



Definition profiled_leb (x y: nat): SimplyProfiled bool := (1, leb x y).
Eval vm_compute in mon_det.qs profiled_leb numbers.

Eval vm_compute in mon_det.qs (M:=IdMonad.M) leb numbers.






Module mon_det_partition.
Section mon_det_partition.

Variables (T: Set) (M: Monad) (cmp: T -> T -> M comparison).

Fixpoint partition (pivot: T) (l: list T) :
M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } :=

match l return M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } with
| nil => ret (@emp T)
| h :: t =>
b <- cmp h pivot;
tt <- partition pivot t ;
ret (addToPartitioning b h tt)
end.

Program Fixpoint qs (l: list T) {measure (length l) lt}: M (list T) :=
match l with
| nil => ret nil
| h :: t =>
part <- partition h t;
low <- qs (part Lt);
upp <- qs (part Gt);
ret (low ++ h :: part Eq ++ upp)
end.

Next Obligation. simpl. rewrite <- H. repeat rewrite app_length. omega. Qed.
Next Obligation. simpl. rewrite <- H. repeat rewrite app_length. omega. Qed.

End mon_det_partition.
End mon_det_partition.

Module mon_nondet.
Section mon_nondet.

Variables (T: Set) (M: Monad) (cmp: T -> T -> M comparison).

Fixpoint partition (pivot: T) (l: list T) :
M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } :=

match l return M { p: Partitioning T | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } with
| nil => ret (@emp T)
| h :: t =>
b <- cmp h pivot;
tt <- partition pivot t ;
ret (addToPartitioning b h tt)
end.

Variable pick: forall (A: Set), ne_list.L A -> M A.

Program Fixpoint qs (l: list T) {measure (length l) lt}: M (list T) :=
match l with
| nil => ret nil
| h :: t =>
i <- pick (ne_list.from_vec (vec.nats 0 (length (h :: t))));
part <- partition (vec.nth (vec.from_list (h :: t)) i) (vec.to_list (vec.remove (vec.from_list (h :: t)) i));
low <- qs (part Lt);
upp <- qs (part Gt);
ret (low ++ vec.nth (vec.from_list (h :: t)) i :: part Eq ++ upp)
end.

Next Obligation.
simpl.
replace (length t) with (length (vec.to_list (vec.remove (vec.from_list (h :: t)) i))).
simpl.
rewrite <- H.
repeat rewrite app_length.
omega.
rewrite vec.length.
reflexivity.
Qed.

Next Obligation.
simpl.
replace (length t) with (length (vec.to_list (vec.remove (vec.from_list (h :: t)) i))).
simpl.
rewrite <- H.
repeat rewrite app_length.
omega.
rewrite vec.length.
reflexivity.
Qed.

End mon_nondet.
End mon_nondet.

From QuicksortComplexity Require Import sort_order.

Fixpoint simplerPartition (e: E) (d: e) (l: list e) {struct l}: { p: Partitioning e | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } :=
match l return { p: Partitioning e | Permutation.Permutation (p Eq ++ p Lt ++ p Gt) l } with
| nil => emp e
| h :: t => addToPartitioning (Ecmp e h d) _ (simplerPartition e d t)
end.

Arguments mon_nondet.qs [T M].



Module nonmonadic_using_Function.

Function qs (l: list nat) {measure length l}: list nat :=
match l with
| nil => nil
| pivot :: t => qs (filter (geb pivot) t) ++ (pivot :: nil) ++ qs (filter (ltb pivot) t)
end.
Proof with simpl; auto with arith. hammer_hook "qs_definitions" "qs_definitions.profiled_leb". intros... intros... Defined.



End nonmonadic_using_Function.
