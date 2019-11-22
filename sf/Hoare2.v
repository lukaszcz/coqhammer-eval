From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From PLF Require Import Hoare.
From PLF Require Import Imp.







































Definition manual_grade_for_decorations_in_if_minus_plus_reloaded : option (nat*string) := None.









Definition reduce_to_zero' : com :=
(WHILE ~(X = 0) DO
X ::= X - 1
END)%imp.

Theorem reduce_to_zero_correct' :
{{fun st => True}}
reduce_to_zero'
{{fun st => st X = 0}}.
Proof. hammer_hook "Hoare2" "Hoare2.reduce_to_zero_correct'".
unfold reduce_to_zero'.

eapply hoare_consequence_post.
apply hoare_while.
-

eapply hoare_consequence_pre. apply hoare_asgn.

intros st [HT Hbp]. unfold assn_sub. constructor.
-
intros st [Inv GuardFalse].
unfold bassn in GuardFalse. simpl in GuardFalse.
rewrite not_true_iff_false in GuardFalse.
rewrite negb_false_iff in GuardFalse.
apply eqb_eq in GuardFalse.
apply GuardFalse. Qed.






























Definition manual_grade_for_decorations_in_slow_assignment : option (nat*string) := None.














Fixpoint parity x :=
match x with
| 0 => 0
| 1 => 1
| S (S x') => parity x'
end.





Lemma parity_ge_2 : forall x,
2 <= x ->
parity (x - 2) = parity x.
Proof. hammer_hook "Hoare2" "Hoare2.parity_ge_2".
induction x; intro. reflexivity.
destruct x. inversion H. inversion H1.
simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
~ 2 <= x ->
parity (x) = x.
Proof. hammer_hook "Hoare2" "Hoare2.parity_lt_2".
intros. induction x. reflexivity. destruct x. reflexivity.
exfalso. apply H. omega.
Qed.

Theorem parity_correct : forall m,
{{ fun st => st X = m }}
WHILE 2 <= X DO
X ::= X - 2
END
{{ fun st => st X = parity m }}.
Proof. hammer_hook "Hoare2" "Hoare2.parity_correct".
Admitted.






















Definition manual_grade_for_decorations_in_factorial : option (nat*string) := None.










Definition manual_grade_for_decorations_in_Min_Hoare : option (nat*string) := None.





Definition manual_grade_for_decorations_in_two_loops : option (nat*string) := None.
















Definition is_wp P c Q :=
{{P}} c {{Q}} /\
forall P', {{P'}} c {{Q}} -> (P' ->> P).








Theorem is_wp_example :
is_wp (fun st => st Y <= 4)
(X ::= Y + 1) (fun st => st X <= 5).
Proof. hammer_hook "Hoare2" "Hoare2.is_wp_example".
Admitted.




Theorem hoare_asgn_weakest : forall Q X a,
is_wp (Q [X |-> a]) (X ::= a) Q.
Proof. hammer_hook "Hoare2" "Hoare2.hoare_asgn_weakest".
Admitted.



Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : string),
{{ P }} HAVOC X {{ Q }} ->
P ->> havoc_pre X Q.
Proof. hammer_hook "Hoare2" "Hoare2.Himp2.hoare_havoc_weakest".
Admitted.
End Himp2.














Inductive dcom : Type :=
| DCSkip :  Assertion -> dcom
| DCSeq : dcom -> dcom -> dcom
| DCAsgn : string -> aexp ->  Assertion -> dcom
| DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom
-> Assertion-> dcom
| DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
| DCPre : Assertion -> dcom -> dcom
| DCPost : dcom -> Assertion -> dcom.

Inductive decorated : Type :=
| Decorated : Assertion -> dcom -> decorated.

Delimit Scope default with default.

Notation "'SKIP' {{ P }}"
:= (DCSkip P)
(at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
:= (DCAsgn l a P)
(at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
:= (DCWhile b Pbody d Ppost)
(at level 80, right associativity) : dcom_scope.
Notation "'TEST' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
:= (DCIf b P d P' d' Q)
(at level 80, right associativity)  : dcom_scope.
Notation "'->>' {{ P }} d"
:= (DCPre P d)
(at level 90, right associativity)  : dcom_scope.
Notation "d '->>' {{ P }}"
:= (DCPost d P)
(at level 80, right associativity)  : dcom_scope.
Notation " d ;; d' "
:= (DCSeq d d')
(at level 80, right associativity)  : dcom_scope.
Notation "{{ P }} d"
:= (Decorated P d)
(at level 90)  : dcom_scope.

Delimit Scope dcom_scope with dcom.
Open Scope dcom_scope.

Example dec0 :=
SKIP {{ fun st => True }}.
Example dec1 :=
WHILE true DO {{ fun st => True }} SKIP {{ fun st => True }} END
{{ fun st => True }}.
Set Printing All.



Example dec_while : decorated :=
{{ fun st => True }}
WHILE ~(X = 0)
DO
{{ fun st => True /\ st X <> 0}}
X ::= X - 1
{{ fun _ => True }}
END
{{ fun st => True /\ st X = 0}} ->>
{{ fun st => st X = 0 }}.



Fixpoint extract (d : dcom) : com :=
match d with
| DCSkip _           => SKIP
| DCSeq d1 d2        => (extract d1 ;; extract d2)
| DCAsgn X a _       => X ::= a
| DCIf b _ d1 _ d2 _ => TEST b THEN extract d1 ELSE extract d2 FI
| DCWhile b _ d _    => WHILE b DO extract d END
| DCPre _ d          => extract d
| DCPost d _         => extract d
end.

Definition extract_dec (dec : decorated) : com :=
match dec with
| Decorated P d => extract d
end.





Fixpoint post (d : dcom) : Assertion :=
match d with
| DCSkip P                => P
| DCSeq d1 d2             => post d2
| DCAsgn X a Q            => Q
| DCIf  _ _ d1 _ d2 Q     => Q
| DCWhile b Pbody c Ppost => Ppost
| DCPre _ d               => post d
| DCPost c Q              => Q
end.



Definition pre_dec (dec : decorated) : Assertion :=
match dec with
| Decorated P d => P
end.

Definition post_dec (dec : decorated) : Assertion :=
match dec with
| Decorated P d => post d
end.



Definition dec_correct (dec : decorated) :=
{{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.










Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
match d with
| DCSkip Q =>
(P ->> Q)
| DCSeq d1 d2 =>
verification_conditions P d1
/\ verification_conditions (post d1) d2
| DCAsgn X a Q =>
(P ->> Q [X |-> a])
| DCIf b P1 d1 P2 d2 Q =>
((fun st => P st /\ bassn b st) ->> P1)
/\ ((fun st => P st /\ ~ (bassn b st)) ->> P2)
/\ (post d1 ->> Q) /\ (post d2 ->> Q)
/\ verification_conditions P1 d1
/\ verification_conditions P2 d2
| DCWhile b Pbody d Ppost =>

(P ->> post d)
/\ ((fun st => post d st /\ bassn b st) ->> Pbody)
/\ ((fun st => post d st /\ ~(bassn b st)) ->> Ppost)
/\ verification_conditions Pbody d
| DCPre P' d =>
(P ->> P') /\ verification_conditions P' d
| DCPost d Q =>
verification_conditions P d /\ (post d ->> Q)
end.



Theorem verification_correct : forall d P,
verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof. hammer_hook "Hoare2" "Hoare2.verification_correct".
induction d; intros P H; simpl in *.
-
eapply hoare_consequence_pre.
apply hoare_skip.
assumption.
-
destruct H as [H1 H2].
eapply hoare_seq.
apply IHd2. apply H2.
apply IHd1. apply H1.
-
eapply hoare_consequence_pre.
apply hoare_asgn.
assumption.
-
destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]].
apply IHd1 in HThen. clear IHd1.
apply IHd2 in HElse. clear IHd2.
apply hoare_if.
+ eapply hoare_consequence_post with (Q':=post d1); eauto.
eapply hoare_consequence_pre; eauto.
+ eapply hoare_consequence_post with (Q':=post d2); eauto.
eapply hoare_consequence_pre; eauto.
-
destruct H as [Hpre [Hbody1 [Hpost1  Hd]]].
eapply hoare_consequence_pre; eauto.
eapply hoare_consequence_post; eauto.
apply hoare_while.
eapply hoare_consequence_pre; eauto.
-
destruct H as [HP Hd].
eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
-
destruct H as [Hd HQ].
eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.






Definition verification_conditions_dec (dec : decorated) : Prop :=
match dec with
| Decorated P d => verification_conditions P d
end.

Lemma verification_correct_dec : forall dec,
verification_conditions_dec dec -> dec_correct dec.
Proof. hammer_hook "Hoare2" "Hoare2.verification_correct_dec".
intros [P d]. apply verification_correct.
Qed.



Eval simpl in (verification_conditions_dec dec_while).




Tactic Notation "verify" :=
apply verification_correct;
repeat split;
simpl; unfold assert_implies;
unfold bassn in *; unfold beval in *; unfold aeval in *;
unfold assn_sub; intros;
repeat rewrite t_update_eq;
repeat (rewrite t_update_neq; [| (intro X; inversion X)]);
simpl in *;
repeat match goal with [H : _ /\ _ |- _] => destruct H end;
repeat rewrite not_true_iff_false in *;
repeat rewrite not_false_iff_true in *;
repeat rewrite negb_true_iff in *;
repeat rewrite negb_false_iff in *;
repeat rewrite eqb_eq in *;
repeat rewrite eqb_neq in *;
repeat rewrite leb_iff in *;
repeat rewrite leb_iff_conv in *;
try subst;
repeat
match goal with
[st : state |- _] =>
match goal with
[H : st _ = _ |- _] => rewrite -> H in *; clear H
| [H : _ = st _ |- _] => rewrite <- H in *; clear H
end
end;
try eauto; try omega.



Theorem dec_while_correct :
dec_correct dec_while.
Proof. hammer_hook "Hoare2" "Hoare2.dec_while_correct". verify. Qed.



Example subtract_slowly_dec (m : nat) (p : nat) : decorated :=
{{ fun st => st X = m /\ st Z = p }} ->>
{{ fun st => st Z - st X = p - m }}
WHILE ~(X = 0)
DO   {{ fun st => st Z - st X = p - m /\ st X <> 0 }} ->>
{{ fun st => (st Z - 1) - (st X - 1) = p - m }}
Z ::= Z - 1
{{ fun st => st Z - (st X - 1) = p - m }} ;;
X ::= X - 1
{{ fun st => st Z - st X = p - m }}
END
{{ fun st => st Z - st X = p - m /\ st X = 0 }} ->>
{{ fun st => st Z = p - m }}.

Theorem subtract_slowly_dec_correct : forall m p,
dec_correct (subtract_slowly_dec m p).
Proof. hammer_hook "Hoare2" "Hoare2.subtract_slowly_dec_correct". intros m p. verify.  Qed.









Definition swap : com :=
X ::= X + Y;;
Y ::= X - Y;;
X ::= X - Y.

Definition swap_dec m n : decorated :=
{{ fun st => st X = m /\ st Y = n}} ->>
{{ fun st => (st X + st Y) - ((st X + st Y) - st Y) = n
/\ (st X + st Y) - st Y = m }}
X ::= X + Y
{{ fun st => st X - (st X - st Y) = n /\ st X - st Y = m }};;
Y ::= X - Y
{{ fun st => st X - st Y = n /\ st Y = m }};;
X ::= X - Y
{{ fun st => st X = n /\ st Y = m}}.

Theorem swap_correct : forall m n,
dec_correct (swap_dec m n).
Proof. hammer_hook "Hoare2" "Hoare2.swap_correct". intros; verify. Qed.




Definition if_minus_plus_com :=
(TEST X <= Y
THEN Z ::= Y - X
ELSE Y ::= X + Z
FI)%imp.

Definition if_minus_plus_dec :=
{{fun st => True}}
TEST X <= Y  THEN
{{ fun st => True /\ st X <= st Y }} ->>
{{ fun st => st Y = st X + (st Y - st X) }}
Z ::= Y - X
{{ fun st => st Y = st X + st Z }}
ELSE
{{ fun st => True /\ ~(st X <= st Y) }} ->>
{{ fun st => st X + st Z = st X + st Z }}
Y ::= X + Z
{{ fun st => st Y = st X + st Z }}
FI
{{fun st => st Y = st X + st Z}}.

Theorem if_minus_plus_correct :
dec_correct if_minus_plus_dec.
Proof. hammer_hook "Hoare2" "Hoare2.if_minus_plus_correct". verify. Qed.

Definition if_minus_dec :=
{{fun st => True}}
TEST X <= Y THEN
{{fun st => True /\ st X <= st Y }} ->>
{{fun st => (st Y - st X) + st X = st Y
\/ (st Y - st X) + st Y = st X}}
Z ::= Y - X
{{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
ELSE
{{fun st => True /\ ~(st X <= st Y) }} ->>
{{fun st => (st X - st Y) + st X = st Y
\/ (st X - st Y) + st Y = st X}}
Z ::= X - Y
{{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
FI
{{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}.

Theorem if_minus_correct :
dec_correct if_minus_dec.
Proof. hammer_hook "Hoare2" "Hoare2.if_minus_correct". verify. Qed.




Definition div_mod_dec (a b : nat) : decorated :=
{{ fun st => True }} ->>
{{ fun st => b * 0 + a = a }}
X ::= a
{{ fun st => b * 0 + st X = a }};;
Y ::= 0
{{ fun st => b * st Y + st X = a }};;
WHILE b <= X DO
{{ fun st => b * st Y + st X = a /\ b <= st X }} ->>
{{ fun st => b * (st Y + 1) + (st X - b) = a }}
X ::= X - b
{{ fun st => b * (st Y + 1) + st X = a }};;
Y ::= Y + 1
{{ fun st => b * st Y + st X = a }}
END
{{ fun st => b * st Y + st X = a /\ ~(b <= st X) }} ->>
{{ fun st => b * st Y + st X = a /\ (st X < b) }}.

Theorem div_mod_dec_correct : forall a b,
dec_correct (div_mod_dec a b).
Proof. hammer_hook "Hoare2" "Hoare2.div_mod_dec_correct". intros a b. verify.
rewrite mult_plus_distr_l. omega.
Qed.




Definition find_parity : com :=
WHILE 2 <= X DO
X ::= X - 2
END.



Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Definition find_parity_dec m : decorated :=
{{ fun st => st X = m}} ->>
{{ fun st => st X <= m /\ ev (m - st X) }}
WHILE 2 <= X DO
{{ fun st => (st X <= m /\ ev (m - st X)) /\ 2 <= st X }} ->>
{{ fun st => st X - 2 <= m /\ (ev (m - (st X - 2))) }}
X ::= X - 2
{{ fun st => st X <= m /\ ev (m - st X) }}
END
{{ fun st => (st X <= m /\ ev (m - st X)) /\ st X < 2 }} ->>
{{ fun st => st X=0 <-> ev m }}.

Lemma l1 : forall m n p,
p <= n ->
n <= m ->
m - (n - p) = m - n + p.
Proof. hammer_hook "Hoare2" "Hoare2.l1". intros. omega. Qed.

Lemma l2 : forall m,
ev m ->
ev (m + 2).
Proof. hammer_hook "Hoare2" "Hoare2.l2". intros. rewrite plus_comm. simpl. constructor. assumption. Qed.

Lemma l3' : forall m,
ev m ->
~ev (S m).
Proof. hammer_hook "Hoare2" "Hoare2.l3'". induction m; intros H1 H2. inversion H2. apply IHm.
inversion H2; subst; assumption. assumption. Qed.

Lemma l3 : forall m,
1 <= m ->
ev m ->
ev (m - 1) ->
False.
Proof. hammer_hook "Hoare2" "Hoare2.l3". intros. apply l2 in H1.
assert (G : m - 1 + 2 = S m). clear H0 H1. omega.
rewrite G in H1. apply l3' in H0. apply H0. assumption. Qed.

Theorem find_parity_correct : forall m,
dec_correct (find_parity_dec m).
Proof. hammer_hook "Hoare2" "Hoare2.find_parity_correct".
intro m. verify;

fold (2 <=? (st X)) in *;
try rewrite leb_iff in *;
try rewrite leb_iff_conv in *; eauto; try omega.
-
rewrite minus_diag. constructor.
-
rewrite l1; try assumption.
apply l2; assumption.
-
rewrite <- minus_n_O in H2. assumption.
-
destruct (st X) as [| [| n]].

+
reflexivity.
+
apply l3 in H; try assumption. inversion H.
+
clear H0 H2.
omega.
Qed.



Definition find_parity_dec' m : decorated :=
{{ fun st => st X = m}} ->>
{{ fun st => ev (st X) <-> ev m }}
WHILE 2 <= X DO
{{ fun st => (ev (st X) <-> ev m) /\ 2 <= st X }} ->>
{{ fun st => (ev (st X - 2) <-> ev m) }}
X ::= X - 2
{{ fun st => (ev (st X) <-> ev m) }}
END
{{ fun st => (ev (st X) <-> ev m) /\ ~(2 <= st X) }} ->>
{{ fun st => st X=0 <-> ev m }}.

Lemma l4 : forall m,
2 <= m ->
(ev (m - 2) <-> ev m).
Proof. hammer_hook "Hoare2" "Hoare2.l4".
induction m; intros. split; intro; constructor.
destruct m. inversion H. inversion H1. simpl in *.
rewrite <- minus_n_O in *. split; intro.
constructor. assumption.
inversion H0. assumption.
Qed.

Theorem find_parity_correct' : forall m,
dec_correct (find_parity_dec' m).
Proof. hammer_hook "Hoare2" "Hoare2.find_parity_correct'".
intros m. verify;

fold (2 <=? (st X)) in *;
try rewrite leb_iff in *;
try rewrite leb_iff_conv in *; intuition; eauto; try omega.
-
rewrite l4 in H0; eauto.
-
rewrite l4; eauto.
-
apply H0. constructor.
-
destruct (st X) as [| [| n]].
+
reflexivity.
+
inversion H.
+
clear H0 H H3.
omega.
Qed.



Definition parity_dec m : decorated :=
{{ fun st => st X = m}} ->>
{{ fun st => parity (st X) = parity m }}
WHILE 2 <= X DO
{{ fun st => parity (st X) = parity m /\ 2 <= st X }} ->>
{{ fun st => parity (st X - 2) = parity m }}
X ::= X - 2
{{ fun st => parity (st X) = parity m }}
END
{{ fun st => parity (st X) = parity m /\ ~(2 <= st X) }} ->>
{{ fun st => st X = parity m }}.

Theorem parity_dec_correct : forall m,
dec_correct (parity_dec m).
Proof. hammer_hook "Hoare2" "Hoare2.parity_dec_correct".
intros. verify;

fold (2 <=? (st X)) in *;
try rewrite leb_iff in *;
try rewrite leb_iff_conv in *; eauto; try omega.
-
rewrite <- H. apply parity_ge_2. assumption.
-
rewrite <- H. symmetry. apply parity_lt_2. assumption.
Qed.




Definition sqrt_dec m : decorated :=
{{ fun st => st X = m }} ->>
{{ fun st => st X = m /\ 0*0 <= m }}
Z ::= 0
{{ fun st => st X = m /\ st Z*st Z <= m }};;
WHILE (Z+1)*(Z+1) <= X DO
{{ fun st => (st X = m /\ st Z*st Z<=m)
/\ (st Z + 1)*(st Z + 1) <= st X }} ->>
{{ fun st => st X = m /\ (st Z+1)*(st Z+1)<=m }}
Z ::= Z + 1
{{ fun st => st X = m /\ st Z*st Z<=m }}
END
{{ fun st => (st X = m /\ st Z*st Z<=m)
/\ ~((st Z + 1)*(st Z + 1) <= st X) }} ->>
{{ fun st => st Z*st Z<=m /\ m<(st Z+1)*(st Z+1) }}.

Theorem sqrt_correct : forall m,
dec_correct (sqrt_dec m).
Proof. hammer_hook "Hoare2" "Hoare2.sqrt_correct". intro m. verify. Qed.






Definition square_dec (m : nat) : decorated :=
{{ fun st => st X = m }}
Y ::= X
{{ fun st => st X = m /\ st Y = m }};;
Z ::= 0
{{ fun st => st X = m /\ st Y = m /\ st Z = 0}} ->>
{{ fun st => st Z + st X * st Y = m * m }};;
WHILE ~(Y = 0) DO
{{ fun st => st Z + st X * st Y = m * m /\ st Y <> 0 }} ->>
{{ fun st => (st Z + st X) + st X * (st Y - 1) = m * m }}
Z ::= Z + X
{{ fun st => st Z + st X * (st Y - 1) = m * m }};;
Y ::= Y - 1
{{ fun st => st Z + st X * st Y = m * m }}
END
{{ fun st => st Z + st X * st Y = m * m /\ st Y = 0 }} ->>
{{ fun st => st Z = m * m }}.

Theorem square_dec_correct : forall m,
dec_correct (square_dec m).
Proof. hammer_hook "Hoare2" "Hoare2.square_dec_correct".
intro n. verify.
-
destruct (st Y) as [| y']. apply False_ind. apply H0.
reflexivity.
simpl. rewrite <- minus_n_O.
assert (G : forall n m, n * S m = n + n * m). {
clear. intros. induction n. reflexivity. simpl.
rewrite IHn. omega. }
rewrite <- H. rewrite G. rewrite plus_assoc. reflexivity.
Qed.

Definition square_dec' (n : nat) : decorated :=
{{ fun st => True }}
X ::= n
{{ fun st => st X = n }};;
Y ::= X
{{ fun st => st X = n /\ st Y = n }};;
Z ::= 0
{{ fun st => st X = n /\ st Y = n /\ st Z = 0 }} ->>
{{ fun st => st Z = st X * (st X - st Y)
/\ st X = n /\ st Y <= st X }};;
WHILE ~(Y = 0) DO
{{ fun st => (st Z = st X * (st X - st Y)
/\ st X = n /\ st Y <= st X)
/\ st Y <> 0 }}
Z ::= Z + X
{{ fun st => st Z = st X * (st X - (st Y - 1))
/\ st X = n /\ st Y <= st X }};;
Y ::= Y - 1
{{ fun st => st Z = st X * (st X - st Y)
/\ st X = n /\ st Y <= st X }}
END
{{ fun st => (st Z = st X * (st X - st Y)
/\ st X = n /\ st Y <= st X)
/\ st Y = 0 }} ->>
{{ fun st => st Z = n * n }}.

Theorem square_dec'_correct : forall n,
dec_correct (square_dec' n).
Proof. hammer_hook "Hoare2" "Hoare2.square_dec'_correct".
intro n. verify.
-
rewrite minus_diag. omega.
-  subst.
rewrite mult_minus_distr_l.
repeat rewrite mult_minus_distr_l. rewrite mult_1_r.
assert (G : forall n m p,
m <= n -> p <= m -> n - (m - p) = n - m + p).
intros. omega.
rewrite G. reflexivity. apply mult_le_compat_l. assumption.
destruct (st Y). apply False_ind. apply H0. reflexivity.
clear. rewrite mult_succ_r. rewrite plus_comm.
apply le_plus_l.
-
rewrite <- minus_n_O. reflexivity.
Qed.

Definition square_simpler_dec (m : nat) : decorated :=
{{ fun st => st X = m }} ->>
{{ fun st => 0 = 0*m /\ st X = m }}
Y ::= 0
{{ fun st => 0 = (st Y)*m /\ st X = m }};;
Z ::= 0
{{ fun st => st Z = (st Y)*m /\ st X = m }}->>
{{ fun st => st Z = (st Y)*m /\ st X = m }};;
WHILE ~(Y = X) DO
{{ fun st => (st Z = (st Y)*m /\ st X = m)
/\ st Y <> st X }} ->>
{{ fun st => st Z + st X = ((st Y) + 1)*m /\ st X = m }}
Z ::= Z + X
{{ fun st => st Z = ((st Y) + 1)*m /\ st X = m }};;
Y ::= Y + 1
{{ fun st => st Z = (st Y)*m /\ st X = m }}
END
{{ fun st => (st Z = (st Y)*m /\ st X = m) /\ st Y = st X }} ->>
{{ fun st => st Z = m*m }}.

Theorem square_simpler_dec_correct : forall m,
dec_correct (square_simpler_dec m).
Proof. hammer_hook "Hoare2" "Hoare2.square_simpler_dec_correct".
intro m. verify.
rewrite mult_plus_distr_r. simpl. rewrite <- plus_n_O.
reflexivity.
Qed.




Definition two_loops_dec (a b c : nat) : decorated :=
{{ fun st => True }} ->>
{{ fun st => c = 0 + c /\ 0 = 0 }}
X ::= 0
{{ fun st => c = st X + c /\ 0 = 0 }};;
Y ::= 0
{{ fun st => c = st X + c /\ st Y = 0 }};;
Z ::= c
{{ fun st => st Z = st X + c /\ st Y = 0 }};;
WHILE ~(X = a) DO
{{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X <> a }} ->>
{{ fun st => st Z + 1 = st X + 1 + c /\ st Y = 0 }}
X ::= X + 1
{{ fun st => st Z + 1 = st X + c /\ st Y = 0 }};;
Z ::= Z + 1
{{ fun st => st Z = st X + c /\ st Y = 0 }}
END
{{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X = a }} ->>
{{ fun st => st Z = a + st Y + c }};;
WHILE ~(Y = b) DO
{{ fun st => st Z = a + st Y + c /\ st Y <> b }} ->>
{{ fun st => st Z + 1 = a + st Y + 1 + c }}
Y ::= Y + 1
{{ fun st => st Z + 1 = a + st Y + c }};;
Z ::= Z + 1
{{ fun st => st Z = a + st Y + c }}
END
{{ fun st => (st Z = a + st Y + c) /\ st Y = b }} ->>
{{ fun st => st Z = a + b + c }}.

Theorem two_loops_correct : forall a b c,
dec_correct (two_loops_dec a b c).
Proof. hammer_hook "Hoare2" "Hoare2.two_loops_correct". intros a b c. verify. Qed.




Fixpoint pow2 n :=
match n with
| 0 => 1
| S n' => 2 * (pow2 n')
end.

Definition dpow2_down (n : nat) :=
{{ fun st => True }} ->>
{{ fun st => 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 0 }}
X ::= 0
{{ fun st => 1 = (pow2 (0 + 1))-1 /\ 1 = pow2 (st X) }};;
Y ::= 1
{{ fun st => st Y = (pow2 (st X + 1))-1 /\ 1 = pow2 (st X) }};;
Z ::= 1
{{ fun st => st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X) }};;
WHILE ~(X = n) DO
{{ fun st => (st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X))
/\ st X <> n }} ->>
{{ fun st => st Y + 2 * st Z = (pow2 (st X + 2))-1
/\ 2 * st Z = pow2 (st X + 1) }}
Z ::= 2 * Z
{{ fun st => st Y + st Z = (pow2 (st X + 2))-1
/\ st Z = pow2 (st X + 1) }};;
Y ::= Y + Z
{{ fun st => st Y = (pow2 (st X + 2))-1
/\ st Z = pow2 (st X + 1) }};;
X ::= X + 1
{{ fun st => st Y = (pow2 (st X + 1))-1
/\ st Z = pow2 (st X) }}
END
{{ fun st => (st Y = (pow2 (st X + 1))-1 /\ st Z = pow2 (st X))
/\ st X = n }} ->>
{{ fun st => st Y = pow2 (n+1) - 1 }}.

Lemma pow2_plus_1 : forall n,
pow2 (n+1) = pow2 n + pow2 n.
Proof. hammer_hook "Hoare2" "Hoare2.pow2_plus_1". induction n; simpl. reflexivity. omega. Qed.

Lemma pow2_le_1 : forall n, pow2 n >= 1.
Proof. hammer_hook "Hoare2" "Hoare2.pow2_le_1". induction n. simpl. constructor. simpl. omega. Qed.

Theorem dpow2_down_correct : forall n,
dec_correct (dpow2_down n).
Proof. hammer_hook "Hoare2" "Hoare2.dpow2_down_correct".
intro m. verify.
-
rewrite pow2_plus_1. rewrite <- H0. reflexivity.
-
rewrite <- plus_n_O.
rewrite <- pow2_plus_1. remember (st X) as n.
replace (pow2 (n + 1) - 1 + pow2 (n + 1))
with (pow2 (n + 1) + pow2 (n + 1) - 1) by omega.
rewrite <- pow2_plus_1.
replace (n + 1 + 1) with (n + 2) by omega.
reflexivity.
-
rewrite <- plus_n_O. rewrite <- pow2_plus_1.
reflexivity.
-
replace (st X + 1 + 1) with (st X + 2) by omega.
reflexivity.
Qed.






Example slow_assignment_dec (m : nat) : decorated
. Admitted.

Theorem slow_assignment_dec_correct : forall m,
dec_correct (slow_assignment_dec m).
Proof. hammer_hook "Hoare2" "Hoare2.slow_assignment_dec_correct".  Admitted.


Definition manual_grade_for_check_defn_of_slow_assignment_dec : option (nat*string) := None.




Fixpoint real_fact (n : nat) : nat :=
match n with
| O => 1
| S n' => n * (real_fact n')
end.






Definition manual_grade_for_factorial_dec : option (nat*string) := None.




Fixpoint fib n :=
match n with
| 0 => 1
| S n' => match n' with
| 0 => 1
| S n'' => fib n' + fib n''
end
end.



Lemma fib_eqn : forall n,
n > 0 ->
fib n + fib (Init.Nat.pred n) = fib (n + 1).
Proof. hammer_hook "Hoare2" "Hoare2.fib_eqn".
Admitted.




Definition T : string := "T".

Definition dfib (n : nat) : decorated
. Admitted.

Theorem dfib_correct : forall n,
dec_correct (dfib n).
Admitted.











