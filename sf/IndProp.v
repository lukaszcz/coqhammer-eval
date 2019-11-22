From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.





















Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).



Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).












Theorem ev_4 : even 4.
Proof. hammer_hook "IndProp" "IndProp.ev_4". apply ev_SS. apply ev_SS. apply ev_0. Qed.



Theorem ev_4' : even 4.
Proof. hammer_hook "IndProp" "IndProp.ev_4'". apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.



Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof. hammer_hook "IndProp" "IndProp.ev_plus4".
intros n. simpl. intros Hn.
apply ev_SS. apply ev_SS. apply Hn.
Qed.


Theorem ev_double : forall n,
even (double n).
Proof. hammer_hook "IndProp" "IndProp.ev_double".
Admitted.
















Theorem ev_inversion :
forall (n : nat), even n ->
(n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof. hammer_hook "IndProp" "IndProp.ev_inversion".
intros n E.
destruct E as [ | n' E'].
-
left. reflexivity.
-
right. exists n'. split. reflexivity. apply E'.
Qed.



Theorem ev_minus2 : forall n,
even n -> even (pred (pred n)).
Proof. hammer_hook "IndProp" "IndProp.ev_minus2".
intros n E.
destruct E as [| n' E'].
-  simpl. apply ev_0.
-  simpl. apply E'.
Qed.



Theorem evSS_ev : forall n,
even (S (S n)) -> even n.

Proof. hammer_hook "IndProp" "IndProp.evSS_ev".
intros n E.
destruct E as [| n' E'].
-

Abort.





Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. hammer_hook "IndProp" "IndProp.evSS_ev". intros n H. apply ev_inversion in H. destruct H.
- discriminate H.
- destruct H as [n' [Hnm Hev]]. injection Hnm.
intro Heq. rewrite Heq. apply Hev.
Qed.





Theorem evSS_ev' : forall n,
even (S (S n)) -> even n.
Proof. hammer_hook "IndProp" "IndProp.evSS_ev'".
intros n E.
inversion E as [| n' E'].

apply E'.
Qed.


Theorem one_not_even : ~ even 1.
Proof. hammer_hook "IndProp" "IndProp.one_not_even".
intros H. apply ev_inversion in H.
destruct H as [ | [m [Hm _]]].
- discriminate H.
- discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
intros H. inversion H. Qed.



Theorem SSSSev__even : forall n,
even (S (S (S (S n)))) -> even n.
Proof. hammer_hook "IndProp" "IndProp.SSSSev__even".
Admitted.




Theorem even5_nonsense :
even 5 -> 2 + 2 = 9.
Proof. hammer_hook "IndProp" "IndProp.even5_nonsense".
Admitted.




Theorem inversion_ex1 : forall (n m o : nat),
[n; m] = [o; o] ->
[n] = [m].
Proof. hammer_hook "IndProp" "IndProp.inversion_ex1".
intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
S n = O ->
2 + 2 = 5.
Proof. hammer_hook "IndProp" "IndProp.inversion_ex2".
intros n contra. inversion contra. Qed.





Lemma ev_even_firsttry : forall n,
even n -> exists k, n = double k.
Proof. hammer_hook "IndProp" "IndProp.ev_even_firsttry".




intros n E. inversion E as [| n' E'].
-
exists 0. reflexivity.
-  simpl.



assert (I : (exists k', n' = double k') ->
(exists k, S (S n') = double k)).
{ intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
apply I.

Abort.








Lemma ev_even : forall n,
even n -> exists k, n = double k.
Proof. hammer_hook "IndProp" "IndProp.ev_even".
intros n E.
induction E as [|n' E' IH].
-
exists 0. reflexivity.
-
destruct IH as [k' Hk'].
rewrite Hk'. exists (S k'). reflexivity.
Qed.





Theorem ev_even_iff : forall n,
even n <-> exists k, n = double k.
Proof. hammer_hook "IndProp" "IndProp.ev_even_iff".
intros n. split.
-  apply ev_even.
-  intros [k Hk]. rewrite Hk. apply ev_double.
Qed.






Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof. hammer_hook "IndProp" "IndProp.ev_sum".
Admitted.




Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).



Theorem even'_ev : forall n, even' n <-> even n.
Proof. hammer_hook "IndProp" "IndProp.even'_ev".
Admitted.




Theorem ev_ev__ev : forall n m,
even (n+m) -> even n -> even m.
Proof. hammer_hook "IndProp" "IndProp.ev_ev__ev".
Admitted.




Theorem ev_plus_plus : forall n m p,
even (n+m) -> even (n+p) -> even (m+p).
Proof. hammer_hook "IndProp" "IndProp.ev_plus_plus".
Admitted.







Module Playground.





Inductive le : nat -> nat -> Prop :=
| le_n n : le n n
| le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).





Theorem test_le1 :
3 <= 3.
Proof. hammer_hook "IndProp" "IndProp.Playground.test_le1".

apply le_n.  Qed.

Theorem test_le2 :
3 <= 6.
Proof. hammer_hook "IndProp" "IndProp.Playground.test_le2".

apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
(2 <= 1) -> 2 + 2 = 5.
Proof. hammer_hook "IndProp" "IndProp.Playground.test_le3".

intros H. inversion H. inversion H2.  Qed.



End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).



Inductive square_of : nat -> nat -> Prop :=
| sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 n : even (S n) -> next_even n (S n)
| ne_2 n (H : even (S (S n))) : next_even n (S (S n)).













Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof. hammer_hook "IndProp" "IndProp.le_trans".
Admitted.

Theorem O_le_n : forall n,
0 <= n.
Proof. hammer_hook "IndProp" "IndProp.O_le_n".
Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
n <= m -> S n <= S m.
Proof. hammer_hook "IndProp" "IndProp.n_le_m__Sn_le_Sm".
Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
S n <= S m -> n <= m.
Proof. hammer_hook "IndProp" "IndProp.Sn_le_Sm__n_le_m".
Admitted.

Theorem le_plus_l : forall a b,
a <= a + b.
Proof. hammer_hook "IndProp" "IndProp.le_plus_l".
Admitted.

Theorem plus_lt : forall n1 n2 m,
n1 + n2 < m ->
n1 < m /\ n2 < m.
Proof. hammer_hook "IndProp" "IndProp.plus_lt".
unfold lt.
Admitted.

Theorem lt_S : forall n m,
n < m ->
n < S m.
Proof. hammer_hook "IndProp" "IndProp.lt_S".
Admitted.

Theorem leb_complete : forall n m,
n <=? m = true -> n <= m.
Proof. hammer_hook "IndProp" "IndProp.leb_complete".
Admitted.



Theorem leb_correct : forall n m,
n <= m ->
n <=? m = true.
Proof. hammer_hook "IndProp" "IndProp.leb_correct".
Admitted.



Theorem leb_true_trans : forall n m o,
n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof. hammer_hook "IndProp" "IndProp.leb_true_trans".
Admitted.



Theorem leb_iff : forall n m,
n <=? m = true <-> n <= m.
Proof. hammer_hook "IndProp" "IndProp.leb_iff".
Admitted.


Module R.



Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0
| c2 m n o (H : R m n o) : R (S m) n (S o)
| c3 m n o (H : R m n o) : R m (S n) (S o)
| c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
| c5 m n o (H : R m n o) : R n m o.




Definition manual_grade_for_R_provability : option (nat*string) := None.




Definition fR : nat -> nat -> nat
. Admitted.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof. hammer_hook "IndProp" "IndProp.R.R_equiv_fR".
Admitted.


End R.



Inductive subseq : list nat -> list nat -> Prop :=

.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof. hammer_hook "IndProp" "IndProp.subseq_refl".
Admitted.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
subseq l1 l2 ->
subseq l1 (l2 ++ l3).
Proof. hammer_hook "IndProp" "IndProp.subseq_app".
Admitted.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
subseq l1 l2 ->
subseq l2 l3 ->
subseq l1 l3.
Proof. hammer_hook "IndProp" "IndProp.subseq_trans".
Admitted.













Inductive reg_exp {T : Type} : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp)
| Union (r1 r2 : reg_exp)
| Star (r : reg_exp).







Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar x : exp_match [x] (Char x)
| MApp s1 re1 s2 re2
(H1 : exp_match s1 re1)
(H2 : exp_match s2 re2) :
exp_match (s1 ++ s2) (App re1 re2)
| MUnionL s1 re1 re2
(H1 : exp_match s1 re1) :
exp_match s1 (Union re1 re2)
| MUnionR re1 s2 re2
(H2 : exp_match s2 re2) :
exp_match s2 (Union re1 re2)
| MStar0 re : exp_match [] (Star re)
| MStarApp s1 s2 re
(H1 : exp_match s1 re)
(H2 : exp_match s2 (Star re)) :
exp_match (s1 ++ s2) (Star re).



Notation "s =~ re" := (exp_match s re) (at level 80).





Example reg_exp_ex1 : [1] =~ Char 1.
Proof. hammer_hook "IndProp" "IndProp.reg_exp_ex1".
apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof. hammer_hook "IndProp" "IndProp.reg_exp_ex2".
apply (MApp [1] _ [2]).
- apply MChar.
- apply MChar.
Qed.



Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof. hammer_hook "IndProp" "IndProp.reg_exp_ex3".
intros H. inversion H.
Qed.



Fixpoint reg_exp_of_list {T} (l : list T) :=
match l with
| [] => EmptyStr
| x :: l' => App (Char x) (reg_exp_of_list l')
end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof. hammer_hook "IndProp" "IndProp.reg_exp_ex4".
simpl. apply (MApp [1]).
{ apply MChar. }
apply (MApp [2]).
{ apply MChar. }
apply (MApp [3]).
{ apply MChar. }
apply MEmpty.
Qed.



Lemma MStar1 :
forall T s (re : @reg_exp T) ,
s =~ re ->
s =~ Star re.
Proof. hammer_hook "IndProp" "IndProp.MStar1".
intros T s re H.
rewrite <- (app_nil_r _ s).
apply (MStarApp s [] re).
- apply H.
- apply MStar0.
Qed.





Lemma empty_is_empty : forall T (s : list T),
~ (s =~ EmptySet).
Proof. hammer_hook "IndProp" "IndProp.empty_is_empty".
Admitted.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
s =~ re1 \/ s =~ re2 ->
s =~ Union re1 re2.
Proof. hammer_hook "IndProp" "IndProp.MUnion'".
Admitted.



Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
(forall s, In s ss -> s =~ re) ->
fold app ss [] =~ Star re.
Proof. hammer_hook "IndProp" "IndProp.MStar'".
Admitted.




Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof. hammer_hook "IndProp" "IndProp.reg_exp_of_list_spec".
Admitted.






Fixpoint re_chars {T} (re : reg_exp) : list T :=
match re with
| EmptySet => []
| EmptyStr => []
| Char x => [x]
| App re1 re2 => re_chars re1 ++ re_chars re2
| Union re1 re2 => re_chars re1 ++ re_chars re2
| Star re => re_chars re
end.



Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
s =~ re ->
In x s ->
In x (re_chars re).
Proof. hammer_hook "IndProp" "IndProp.in_re_match".
intros T s re x Hmatch Hin.
induction Hmatch
as [| x'
| s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
| s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
| re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].

-
apply Hin.
-
apply Hin.
- simpl. rewrite In_app_iff in *.
destruct Hin as [Hin | Hin].
+
left. apply (IH1 Hin).
+
right. apply (IH2 Hin).
-
simpl. rewrite In_app_iff.
left. apply (IH Hin).
-
simpl. rewrite In_app_iff.
right. apply (IH Hin).
-
destruct Hin.



-
simpl. rewrite In_app_iff in Hin.
destruct Hin as [Hin | Hin].
+
apply (IH1 Hin).
+
apply (IH2 Hin).
Qed.



Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool
. Admitted.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
(exists s, s =~ re) <-> re_not_empty re = true.
Proof. hammer_hook "IndProp" "IndProp.re_not_empty_correct".
Admitted.







Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
s1 =~ Star re ->
s2 =~ Star re ->
s1 ++ s2 =~ Star re.
Proof. hammer_hook "IndProp" "IndProp.star_app".
intros T s1 s2 re H1.



induction H1
as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
|s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
|re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].



-
simpl. intros H. apply H.



-
Abort.



Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
re' = Star re ->
s1 =~ re' ->
s2 =~ Star re ->
s1 ++ s2 =~ Star re.



Abort.



Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
s1 =~ Star re ->
s2 =~ Star re ->
s1 ++ s2 =~ Star re.
Proof. hammer_hook "IndProp" "IndProp.star_app".
intros T s1 s2 re H1.
remember (Star re) as re'.



generalize dependent s2.
induction H1
as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
|s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
|re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].



-   discriminate.
-    discriminate.
-     discriminate.
-  discriminate.
-  discriminate.



-
injection Heqre'. intros Heqre'' s H. apply H.

-
injection Heqre'. intros H0.
intros s2 H1. rewrite <- app_assoc.
apply MStarApp.
+ apply Hmatch1.
+ apply IH2.
* rewrite H0. reflexivity.
* apply H1.
Qed.





Lemma MStar'' : forall T (s : list T) (re : reg_exp),
s =~ Star re ->
exists ss : list (list T),
s = fold app ss []
/\ forall s', In s' ss -> s' =~ re.
Proof. hammer_hook "IndProp" "IndProp.MStar''".
Admitted.




Module Pumping.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
match re with
| EmptySet => 0
| EmptyStr => 1
| Char _ => 2
| App re1 re2 =>
pumping_constant re1 + pumping_constant re2
| Union re1 re2 =>
pumping_constant re1 + pumping_constant re2
| Star _ => 1
end.



Fixpoint napp {T} (n : nat) (l : list T) : list T :=
match n with
| 0 => []
| S n' => l ++ napp n' l
end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
napp (n + m) l = napp n l ++ napp m l.
Proof. hammer_hook "IndProp" "IndProp.Pumping.napp_plus".
intros T n m l.
induction n as [|n IHn].
- reflexivity.
- simpl. rewrite IHn, app_assoc. reflexivity.
Qed.



Lemma pumping : forall T (re : @reg_exp T) s,
s =~ re ->
pumping_constant re <= length s ->
exists s1 s2 s3,
s = s1 ++ s2 ++ s3 /\
s2 <> [] /\
forall m, s1 ++ napp m s2 ++ s3 =~ re.



Import Coq.omega.Omega.

Proof. hammer_hook "IndProp" "IndProp.Pumping.pumping".
intros T re s Hmatch.
induction Hmatch
as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
| s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
| re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
-
simpl. omega.
Admitted.

End Pumping.







Theorem filter_not_empty_In : forall n l,
filter (fun x => n =? x) l <> [] ->
In n l.
Proof. hammer_hook "IndProp" "IndProp.filter_not_empty_In".
intros n l. induction l as [|m l' IHl'].
-
simpl. intros H. apply H. reflexivity.
-
simpl. destruct (n =? m) eqn:H.
+
intros _. rewrite eqb_eq in H. rewrite H.
left. reflexivity.
+
intros H'. right. apply IHl'. apply H'.
Qed.





Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.



Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof. hammer_hook "IndProp" "IndProp.iff_reflect".

intros P b H. destruct b.
- apply ReflectT. rewrite H. reflexivity.
- apply ReflectF. rewrite H. intros H'. discriminate.
Qed.




Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof. hammer_hook "IndProp" "IndProp.reflect_iff".
Admitted.




Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof. hammer_hook "IndProp" "IndProp.eqbP".
intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.





Theorem filter_not_empty_In' : forall n l,
filter (fun x => n =? x) l <> [] ->
In n l.
Proof. hammer_hook "IndProp" "IndProp.filter_not_empty_In'".
intros n l. induction l as [|m l' IHl'].
-
simpl. intros H. apply H. reflexivity.
-
simpl. destruct (eqbP n m) as [H | H].
+
intros _. rewrite H. left. reflexivity.
+
intros H'. right. apply IHl'. apply H'.
Qed.



Fixpoint count n l :=
match l with
| [] => 0
| m :: l' => (if n =? m then 1 else 0) + count n l'
end.

Theorem eqbP_practice : forall n l,
count n l = 0 -> ~(In n l).
Proof. hammer_hook "IndProp" "IndProp.eqbP_practice".
Admitted.









Inductive nostutter {X:Type} : list X -> Prop :=

.


Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Admitted.


Example test_nostutter_2:  nostutter (@nil nat).
Admitted.


Example test_nostutter_3:  nostutter [5].
Admitted.


Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Admitted.



Definition manual_grade_for_nostutter : option (nat*string) := None.







Definition manual_grade_for_filter_challenge : option (nat*string) := None.











Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.























Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.






Lemma in_split : forall (X:Type) (x:X) (l:list X),
In x l ->
exists l1 l2, l = l1 ++ x :: l2.
Proof. hammer_hook "IndProp" "IndProp.in_split".
Admitted.



Inductive repeats {X:Type} : list X -> Prop :=

.



Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
excluded_middle ->
(forall x, In x l1 -> In x l2) ->
length l2 < length l1 ->
repeats l1.
Proof. hammer_hook "IndProp" "IndProp.pigeonhole_principle".
intros X l1. induction l1 as [|x l1' IHl1'].
Admitted.


Definition manual_grade_for_check_repeats : option (nat*string) := None.








Require Export Coq.Strings.Ascii.

Definition string := list ascii.






Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof. hammer_hook "IndProp" "IndProp.provable_equiv_true".
intros.
split.
- intros. constructor.
- intros _. apply H.
Qed.


Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof. hammer_hook "IndProp" "IndProp.not_equiv_false".
intros.
split.
- apply H.
- intros. destruct H0.
Qed.


Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof. hammer_hook "IndProp" "IndProp.null_matches_none".
intros.
apply not_equiv_false.
unfold not. intros. inversion H.
Qed.


Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof. hammer_hook "IndProp" "IndProp.empty_matches_eps".
split.
- intros. inversion H. reflexivity.
- intros. rewrite H. apply MEmpty.
Qed.


Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof. hammer_hook "IndProp" "IndProp.empty_nomatch_ne".
intros.
apply not_equiv_false.
unfold not. intros. inversion H.
Qed.


Lemma char_nomatch_char :
forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof. hammer_hook "IndProp" "IndProp.char_nomatch_char".
intros.
apply not_equiv_false.
unfold not.
intros.
apply H.
inversion H0.
reflexivity.
Qed.


Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof. hammer_hook "IndProp" "IndProp.char_eps_suffix".
split.
- intros. inversion H. reflexivity.
- intros. rewrite H. apply MChar.
Qed.


Lemma app_exists : forall (s : string) re0 re1,
s =~ App re0 re1 <->
exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof. hammer_hook "IndProp" "IndProp.app_exists".
intros.
split.
- intros. inversion H. exists s1, s2. split.
* reflexivity.
* split. apply H3. apply H4.
- intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.


Lemma app_ne : forall (a : ascii) s re0 re1,
a :: s =~ (App re0 re1) <->
([ ] =~ re0 /\ a :: s =~ re1) \/
exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof. hammer_hook "IndProp" "IndProp.app_ne".
Admitted.



Lemma union_disj : forall (s : string) re0 re1,
s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof. hammer_hook "IndProp" "IndProp.union_disj".
intros. split.
- intros. inversion H.
+ left. apply H2.
+ right. apply H1.
- intros [ H | H ].
+ apply MUnionL. apply H.
+ apply MUnionR. apply H.
Qed.



Lemma star_ne : forall (a : ascii) s re,
a :: s =~ Star re <->
exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof. hammer_hook "IndProp" "IndProp.star_ne".
Admitted.



Definition refl_matches_eps m :=
forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).


Fixpoint match_eps (re: @reg_exp ascii) : bool
. Admitted.



Lemma match_eps_refl : refl_matches_eps match_eps.
Proof. hammer_hook "IndProp" "IndProp.match_eps_refl".
Admitted.






Definition is_der re (a : ascii) re' :=
forall s, a :: s =~ re <-> s =~ re'.


Definition derives d := forall a re, is_der re a (d a re).


Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
. Admitted.



Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.


Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. hammer_hook "IndProp" "IndProp.test_der0".
Admitted.


Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. hammer_hook "IndProp" "IndProp.test_der1".
Admitted.


Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. hammer_hook "IndProp" "IndProp.test_der2".
Admitted.


Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. hammer_hook "IndProp" "IndProp.test_der3".
Admitted.


Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. hammer_hook "IndProp" "IndProp.test_der4".
Admitted.


Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. hammer_hook "IndProp" "IndProp.test_der5".
Admitted.


Example test_der6 :
match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. hammer_hook "IndProp" "IndProp.test_der6".
Admitted.


Example test_der7 :
match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. hammer_hook "IndProp" "IndProp.test_der7".
Admitted.


Lemma derive_corr : derives derive.
Proof. hammer_hook "IndProp" "IndProp.derive_corr".
Admitted.





Definition matches_regex m : Prop :=
forall (s : string) re, reflect (s =~ re) (m s re).


Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
. Admitted.



Theorem regex_refl : matches_regex regex_match.
Proof. hammer_hook "IndProp" "IndProp.regex_refl".
Admitted.



