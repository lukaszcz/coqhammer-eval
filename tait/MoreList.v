From Hammer Require Import Hammer.

















Require Import List.
Require Import Zmisc.
Require Import Arith.
Require Import Bool.

Set Implicit Arguments.



Section MoreLists.

Variable A:Set.

Section Nth.

Lemma nth_overflow : forall (l:list A) n d, length l <= n -> nth n l d = d.
Proof. hammer_hook "MoreList" "MoreList.nth_overflow".
induction l; destruct n; simpl; intros; auto.
inversion H.
apply IHl; auto with arith.
Qed.

Lemma nth_indep :
forall (l:list A) n d d', n < length l -> nth n l d = nth n l d'.
Proof. hammer_hook "MoreList" "MoreList.nth_indep".
induction l; simpl; intros; auto.
inversion H.
destruct n; simpl; auto with arith.
Qed.

End Nth.

Section App.

Lemma app_length : forall l l':list A, length (l++l') = length l + length l'.
Proof. hammer_hook "MoreList" "MoreList.app_length".
induction l; simpl; auto.
Qed.

Lemma app_nth1 :
forall (l l':list A) d n, n < length l -> nth n (l++l') d = nth n l d.
Proof. hammer_hook "MoreList" "MoreList.app_nth1".
induction l.
intros.
inversion H.
intros l' d n.
case n; simpl; auto.
intros; rewrite IHl; auto with arith.
Qed.

Lemma app_nth2 :
forall (l l':list A) d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
Proof. hammer_hook "MoreList" "MoreList.app_nth2".
induction l.
intros.
simpl.
rewrite <- minus_n_O; auto.
intros l' d n.
case n; simpl; auto.
intros.
inversion H.
intros.
rewrite IHl; auto with arith.
Qed.

Lemma fold_left_app : forall (B: Set)(f : A -> B -> A)(l l':list B)(a:A),
fold_left f (l++l') a = fold_left f l' (fold_left f l a).
Proof. hammer_hook "MoreList" "MoreList.fold_left_app".
induction l.
simpl; auto.
intros.
simpl.
auto.
Qed.

End App.

Section Rev.

Lemma rev_length : forall l:list A, length (rev l) = length l.
Proof. hammer_hook "MoreList" "MoreList.rev_length".
induction l;simpl; auto.
rewrite app_length.
rewrite IHl.
simpl; rewrite plus_comm; auto.
Qed.

Lemma rev_nth : forall (l: list A)(d:A)(n:nat),  n < length l ->
nth n (rev l) d = nth (length l - S n) l d.
Proof. hammer_hook "MoreList" "MoreList.rev_nth".
induction l.
intros; inversion H.
intros.
simpl in H.
simpl (rev (a :: l)).
simpl (length (a :: l) - S n).
inversion H.
rewrite <- minus_n_n; simpl.
rewrite <- rev_length.
rewrite app_nth2; auto.
rewrite <- minus_n_n; auto.
rewrite app_nth1; auto.
rewrite (minus_plus_simpl_l_reverse (length l) n 1).
replace (1 + length l) with (S (length l)); auto with arith.
rewrite <- minus_Sn_m; auto with arith; simpl.
apply IHl; auto.
rewrite rev_length; auto.
Qed.

End Rev.

Section Rev_acc.



Fixpoint rev_acc (l l': list A) {struct l} : list A :=
match l with
| nil => l'
| a::l => rev_acc l (a::l')
end.

Lemma rev_acc_rev : forall l l', rev_acc l l' = rev l ++ l'.
Proof. hammer_hook "MoreList" "MoreList.rev_acc_rev".
induction l; simpl; auto; intros.
rewrite <- ass_app; firstorder.
Qed.

Lemma rev_rev_acc : forall l, rev l = rev_acc l nil.
Proof. hammer_hook "MoreList" "MoreList.rev_rev_acc".
intros; rewrite rev_acc_rev.
apply app_nil_end.
Qed.

End Rev_acc.

Section Seq.

Fixpoint seq (start len:nat) {struct len} : list nat :=
match len with
| 0 => nil
| S len => start :: seq (S start) len
end.

Lemma seq_length : forall len start, length (seq start len) = len.
Proof. hammer_hook "MoreList" "MoreList.seq_length".
induction len; simpl; auto.
Qed.

Lemma seq_nth : forall len start n d,
n < len -> nth n (seq start len) d = start+n.
Proof. hammer_hook "MoreList" "MoreList.seq_nth".
induction len; intros.
inversion H.
simpl seq.
destruct n; simpl.
auto with arith.
rewrite IHlen;simpl; auto with arith.
Qed.

Lemma seq_shift : forall len start,
map S (seq start len) = seq (S start) len.
Proof. hammer_hook "MoreList" "MoreList.seq_shift".
induction len; simpl; auto.
intros.
rewrite IHlen.
auto with arith.
Qed.

End Seq.

Section Map.

Variable B: Set.
Variable f : A-> B.

Lemma In_map2 : forall l y, In y (map f l) -> exists x, f x = y /\ In x l.
Proof. hammer_hook "MoreList" "MoreList.In_map2".
induction l; firstorder.
Qed.

Lemma map_length : forall l, length (map f l) = length l.
Proof. hammer_hook "MoreList" "MoreList.map_length".
induction l; simpl; auto.
Qed.

Lemma map_nth : forall l d n,
nth n (map f l) (f d) = f (nth n l d).
Proof. hammer_hook "MoreList" "MoreList.map_nth".
induction l; simpl map; destruct n; firstorder.
Qed.

Lemma map_app : forall l l',
map f (l++l') = (map f l) ++ (map f l').
Proof. hammer_hook "MoreList" "MoreList.map_app".
induction l; simpl; auto.
intros; rewrite IHl; auto.
Qed.

Lemma map_rev : forall l, map f (rev l) = rev (map f l).
Proof. hammer_hook "MoreList" "MoreList.map_rev".
induction l; simpl; auto.
rewrite map_app.
rewrite IHl; auto.
Qed.

Lemma map_map : forall (C:Set)(f:A->B)(g:B->C) l,
map g (map f l) = map (fun x => g (f x)) l.
Proof. hammer_hook "MoreList" "MoreList.map_map".
induction l; simpl; auto.
rewrite IHl; auto.
Qed.

Lemma map_ext :
forall g, (forall a, f a = g a) -> forall l, map f l = map g l.
Proof. hammer_hook "MoreList" "MoreList.map_ext".
induction l; simpl; auto.
rewrite H; rewrite IHl; auto.
Qed.

End Map.

Section SplitLast.

Fixpoint last (l:list A)(d:A)  {struct l} : A :=
match l with
| nil => d
| a :: nil => a
| a :: l => last l d
end.

Fixpoint removelast (l:list A) {struct l} : list A :=
match l with
| nil =>  nil
| a :: nil => nil
| a :: l => a :: removelast l
end.

Lemma app_removelast_last :
forall l d, l<>nil -> l = removelast l ++ (last l d :: nil).
Proof. hammer_hook "MoreList" "MoreList.app_removelast_last".
induction l.
destruct 1; auto.
intros d _.
destruct l; auto.
pattern (a0::l) at 1; rewrite IHl with d; auto; discriminate.
Qed.

Lemma exists_last :
forall l, l<>nil -> { l' : list A & { a : A | l = l'++a::nil}}.
Proof. hammer_hook "MoreList" "MoreList.exists_last".
induction l.
destruct 1; auto.
intros _.
destruct l.
exists (@nil A); exists a; auto.
destruct IHl as [l' (a',H)]; try discriminate.
rewrite H.
exists (a::l'); exists a'; auto.
Qed.

End SplitLast.

Section ConsN.



Definition consn n a (l:list A) := nat_rect _ l (fun _ => cons a) n.

Lemma consn_length : forall n a l, length (consn n a l) = n + length l.
Proof. hammer_hook "MoreList" "MoreList.consn_length".
unfold consn; induction n; simpl; auto.
Qed.

Lemma consn_nth1 :
forall n a l k d,  k < n -> nth k (consn n a l) d = a.
Proof. hammer_hook "MoreList" "MoreList.consn_nth1".
unfold consn; induction n.
inversion 1.
destruct k; simpl; auto with arith.
Qed.

Lemma consn_nth2 :
forall n a l k d,  n <= k -> nth k (consn n a l) d = nth (k-n) l d.
Proof. hammer_hook "MoreList" "MoreList.consn_nth2".
unfold consn; induction n.
intros; rewrite <- minus_n_O; auto.
destruct k; [ inversion 1 | simpl; auto with arith ].
Qed.

End ConsN.

Section Existsb.

Fixpoint existsb (f:A->bool)(l:list A) {struct l}: bool :=
match l with
| nil => false
| a::l => f a || existsb f l
end.

Lemma existsb_nth : forall (f:A->bool)(l:list A) n d, n < length l ->
existsb f l = false -> f (nth n l d) = false.
Proof. hammer_hook "MoreList" "MoreList.existsb_nth".
induction l.
inversion 1.
simpl; intros.
destruct (orb_false_elim _ _ H0); clear H0; auto.
destruct n ; auto.
rewrite IHl; auto with arith.
Qed.

End Existsb.



Fixpoint firstn (n:nat)(l:list A) {struct n} : list A :=
match n with
| 0 => nil
| S n => match l with
| nil => nil
| a::l => a::(firstn n l)
end
end.

End MoreLists.

Arguments consn [A].

Hint Rewrite
rev_involutive
rev_unit
map_nth
map_length
seq_length
app_length
rev_length
consn_length
: list.

Hint Rewrite <-
app_nil_end
: list.

Ltac simpl_list := autorewrite with list.
Ltac ssimpl_list := autorewrite with list using simpl.
