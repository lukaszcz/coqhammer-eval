From Hammer Require Import Hammer.



Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.



Check 3 = 3.


Check forall n m : nat, n + m = m + n.






Check 2 = 2.


Check forall n : nat, n = 2.


Check 3 = 4.






Theorem plus_2_2_is_4 :
2 + 2 = 4.
Proof. hammer_hook "Logic" "Logic.plus_2_2_is_4". reflexivity.  Qed.



Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.




Theorem plus_fact_is_true :
plus_fact.
Proof. hammer_hook "Logic" "Logic.plus_fact_is_true". reflexivity.  Qed.





Definition is_three (n : nat) : Prop :=
n = 3.
Check is_three.




Definition injective {A B} (f : A -> B) :=
forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof. hammer_hook "Logic" "Logic.succ_inj".
intros n m H. injection H as H1. apply H1.
Qed.



Check @eq.












Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.



Proof. hammer_hook "Logic" "Logic.and_example".
split.
-  reflexivity.
-  reflexivity.
Qed.



Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof. hammer_hook "Logic" "Logic.and_intro".
intros A B HA HB. split.
- apply HA.
- apply HB.
Qed.



Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. hammer_hook "Logic" "Logic.and_example'".
apply and_intro.
-  reflexivity.
-  reflexivity.
Qed.


Example and_exercise :
forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. hammer_hook "Logic" "Logic.and_exercise".
Admitted.




Lemma and_example2 :
forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof. hammer_hook "Logic" "Logic.and_example2".

intros n m H.
destruct H as [Hn Hm].
rewrite Hn. rewrite Hm.
reflexivity.
Qed.



Lemma and_example2' :
forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof. hammer_hook "Logic" "Logic.and_example2'".
intros n m [Hn Hm].
rewrite Hn. rewrite Hm.
reflexivity.
Qed.



Lemma and_example2'' :
forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof. hammer_hook "Logic" "Logic.and_example2''".
intros n m Hn Hm.
rewrite Hn. rewrite Hm.
reflexivity.
Qed.



Lemma and_example3 :
forall n m : nat, n + m = 0 -> n * m = 0.
Proof. hammer_hook "Logic" "Logic.and_example3".

intros n m H.
assert (H' : n = 0 /\ m = 0).
{ apply and_exercise. apply H. }
destruct H' as [Hn Hm].
rewrite Hn. reflexivity.
Qed.



Lemma proj1 : forall P Q : Prop,
P /\ Q -> P.
Proof. hammer_hook "Logic" "Logic.proj1".
intros P Q [HP HQ].
apply HP.  Qed.


Lemma proj2 : forall P Q : Prop,
P /\ Q -> Q.
Proof. hammer_hook "Logic" "Logic.proj2".
Admitted.




Theorem and_commut : forall P Q : Prop,
P /\ Q -> Q /\ P.
Proof. hammer_hook "Logic" "Logic.and_commut".
intros P Q [HP HQ].
split.
-  apply HQ.
-  apply HP.  Qed.



Theorem and_assoc : forall P Q R : Prop,
P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof. hammer_hook "Logic" "Logic.and_assoc".
intros P Q R [HP [HQ HR]].
Admitted.




Check and.









Lemma or_example :
forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof. hammer_hook "Logic" "Logic.or_example".

intros n m [Hn | Hm].
-
rewrite Hn. reflexivity.
-
rewrite Hm. rewrite <- mult_n_O.
reflexivity.
Qed.



Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof. hammer_hook "Logic" "Logic.or_intro".
intros A B HA.
left.
apply HA.
Qed.



Lemma zero_or_succ :
forall n : nat, n = 0 \/ n = S (pred n).
Proof. hammer_hook "Logic" "Logic.zero_or_succ".

intros [|n].
- left. reflexivity.
- right. reflexivity.
Qed.


Lemma mult_eq_0 :
forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. hammer_hook "Logic" "Logic.mult_eq_0".
Admitted.



Theorem or_commut : forall P Q : Prop,
P \/ Q  -> Q \/ P.
Proof. hammer_hook "Logic" "Logic.or_commut".
Admitted.







Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.


End MyNot.



Theorem ex_falso_quodlibet : forall (P:Prop),
False -> P.
Proof. hammer_hook "Logic" "Logic.ex_falso_quodlibet".

intros P contra.
destruct contra.  Qed.





Fact not_implies_our_not : forall (P:Prop),
~ P -> (forall (Q:Prop), P -> Q).
Proof. hammer_hook "Logic" "Logic.not_implies_our_not".
Admitted.






Theorem zero_not_one : 0 <> 1.
Proof. hammer_hook "Logic" "Logic.zero_not_one".

unfold not.

intros contra.

discriminate contra.
Qed.



Theorem not_False :
~ False.
Proof. hammer_hook "Logic" "Logic.not_False".
unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
(P /\ ~P) -> Q.
Proof. hammer_hook "Logic" "Logic.contradiction_implies_anything".

intros P Q [HP HNA]. unfold not in HNA.
apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
P -> ~~P.
Proof. hammer_hook "Logic" "Logic.double_neg".

intros P H. unfold not. intros G. apply G. apply H.  Qed.






Definition manual_grade_for_double_neg_inf : option (nat*string) := None.



Theorem contrapositive : forall (P Q : Prop),
(P -> Q) -> (~Q -> ~P).
Proof. hammer_hook "Logic" "Logic.contrapositive".
Admitted.



Theorem not_both_true_and_false : forall P : Prop,
~ (P /\ ~P).
Proof. hammer_hook "Logic" "Logic.not_both_true_and_false".
Admitted.







Definition manual_grade_for_informal_not_PNP : option (nat*string) := None.




Theorem not_true_is_false : forall b : bool,
b <> true -> b = false.
Proof. hammer_hook "Logic" "Logic.not_true_is_false".
intros [] H.
-
unfold not in H.
apply ex_falso_quodlibet.
apply H. reflexivity.
-
reflexivity.
Qed.



Theorem not_true_is_false' : forall b : bool,
b <> true -> b = false.
Proof. hammer_hook "Logic" "Logic.not_true_is_false'".
intros [] H.
-
unfold not in H.
exfalso.
apply H. reflexivity.
-  reflexivity.
Qed.






Lemma True_is_true : True.
Proof. hammer_hook "Logic" "Logic.True_is_true". apply I. Qed.








Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
(at level 95, no associativity)
: type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
(P <-> Q) -> (Q <-> P).
Proof. hammer_hook "Logic" "Logic.iff_sym".

intros P Q [HAB HBA].
split.
-  apply HBA.
-  apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
b <> true <-> b = false.
Proof. hammer_hook "Logic" "Logic.not_true_iff_false".

intros b. split.
-  apply not_true_is_false.
-
intros H. rewrite H. intros H'. discriminate H'.
Qed.



Theorem iff_refl : forall P : Prop,
P <-> P.
Proof. hammer_hook "Logic" "Logic.iff_refl".
Admitted.

Theorem iff_trans : forall P Q R : Prop,
(P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. hammer_hook "Logic" "Logic.iff_trans".
Admitted.



Theorem or_distributes_over_and : forall P Q R : Prop,
P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. hammer_hook "Logic" "Logic.or_distributes_over_and".
Admitted.




From Coq Require Import Setoids.Setoid.



Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof. hammer_hook "Logic" "Logic.mult_0".
split.
- apply mult_eq_0.
- apply or_example.
Qed.

Lemma or_assoc :
forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof. hammer_hook "Logic" "Logic.or_assoc".
intros P Q R. split.
- intros [H | [H | H]].
+ left. left. apply H.
+ left. right. apply H.
+ right. apply H.
- intros [[H | H] | H].
+ left. apply H.
+ right. left. apply H.
+ right. right. apply H.
Qed.



Lemma mult_0_3 :
forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof. hammer_hook "Logic" "Logic.mult_0_3".
intros n m p.
rewrite mult_0. rewrite mult_0. rewrite or_assoc.
reflexivity.
Qed.



Lemma apply_iff_example :
forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof. hammer_hook "Logic" "Logic.apply_iff_example".
intros n m H. apply mult_0. apply H.
Qed.








Lemma four_is_even : exists n : nat, 4 = n + n.
Proof. hammer_hook "Logic" "Logic.four_is_even".
exists 2. reflexivity.
Qed.



Theorem exists_example_2 : forall n,
(exists m, n = 4 + m) ->
(exists o, n = 2 + o).
Proof. hammer_hook "Logic" "Logic.exists_example_2".

intros n [m Hm].
exists (2 + m).
apply Hm.  Qed.



Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
(forall x, P x) -> ~ (exists x, ~ P x).
Proof. hammer_hook "Logic" "Logic.dist_not_exists".
Admitted.




Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
(exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. hammer_hook "Logic" "Logic.dist_exists_or".
Admitted.









Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
match l with
| [] => False
| x' :: l' => x' = x \/ In x l'
end.



Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof. hammer_hook "Logic" "Logic.In_example_1".

simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
forall n, In n [2; 4] ->
exists n', n = 2 * n'.
Proof. hammer_hook "Logic" "Logic.In_example_2".

simpl.
intros n [H | [H | []]].
- exists 1. rewrite <- H. reflexivity.
- exists 2. rewrite <- H. reflexivity.
Qed.




Lemma In_map :
forall (A B : Type) (f : A -> B) (l : list A) (x : A),
In x l ->
In (f x) (map f l).
Proof. hammer_hook "Logic" "Logic.In_map".
intros A B f l x.
induction l as [|x' l' IHl'].
-
simpl. intros [].
-
simpl. intros [H | H].
+ rewrite H. left. reflexivity.
+ right. apply IHl'. apply H.
Qed.




Lemma In_map_iff :
forall (A B : Type) (f : A -> B) (l : list A) (y : B),
In y (map f l) <->
exists x, f x = y /\ In x l.
Proof. hammer_hook "Logic" "Logic.In_map_iff".
Admitted.



Lemma In_app_iff : forall A l l' (a:A),
In a (l++l') <-> In a l \/ In a l'.
Proof. hammer_hook "Logic" "Logic.In_app_iff".
Admitted.




Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
. Admitted.

Lemma All_In :
forall T (P : T -> Prop) (l : list T),
(forall x, In x l -> P x) <->
All P l.
Proof. hammer_hook "Logic" "Logic.All_In".
Admitted.




Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
. Admitted.



Theorem combine_odd_even_intro :
forall (Podd Peven : nat -> Prop) (n : nat),
(oddb n = true -> Podd n) ->
(oddb n = false -> Peven n) ->
combine_odd_even Podd Peven n.
Proof. hammer_hook "Logic" "Logic.combine_odd_even_intro".
Admitted.

Theorem combine_odd_even_elim_odd :
forall (Podd Peven : nat -> Prop) (n : nat),
combine_odd_even Podd Peven n ->
oddb n = true ->
Podd n.
Proof. hammer_hook "Logic" "Logic.combine_odd_even_elim_odd".
Admitted.

Theorem combine_odd_even_elim_even :
forall (Podd Peven : nat -> Prop) (n : nat),
combine_odd_even Podd Peven n ->
oddb n = false ->
Peven n.
Proof. hammer_hook "Logic" "Logic.combine_odd_even_elim_even".
Admitted.









Check plus_comm.










Lemma plus_comm3 :
forall x y z, x + (y + z) = (z + y) + x.



Proof. hammer_hook "Logic" "Logic.plus_comm3".

intros x y z.
rewrite plus_comm.
rewrite plus_comm.

Abort.



Lemma plus_comm3_take2 :
forall x y z, x + (y + z) = (z + y) + x.
Proof. hammer_hook "Logic" "Logic.plus_comm3_take2".
intros x y z.
rewrite plus_comm.
assert (H : y + z = z + y).
{ rewrite plus_comm. reflexivity. }
rewrite H.
reflexivity.
Qed.



Lemma plus_comm3_take3 :
forall x y z, x + (y + z) = (z + y) + x.
Proof. hammer_hook "Logic" "Logic.plus_comm3_take3".
intros x y z.
rewrite plus_comm.
rewrite (plus_comm y z).
reflexivity.
Qed.



Lemma in_not_nil :
forall A (x : A) (l : list A), In x l -> l <> [].
Proof. hammer_hook "Logic" "Logic.in_not_nil".
intros A x l H. unfold not. intro Hl. destruct l.
- simpl in H. destruct H.
- discriminate Hl.
Qed.





Lemma in_not_nil_42 :
forall l : list nat, In 42 l -> l <> [].
Proof. hammer_hook "Logic" "Logic.in_not_nil_42".

intros l H.
Fail apply in_not_nil.
Abort.


Lemma in_not_nil_42_take2 :
forall l : list nat, In 42 l -> l <> [].
Proof. hammer_hook "Logic" "Logic.in_not_nil_42_take2".
intros l H.
apply in_not_nil with (x := 42).
apply H.
Qed.


Lemma in_not_nil_42_take3 :
forall l : list nat, In 42 l -> l <> [].
Proof. hammer_hook "Logic" "Logic.in_not_nil_42_take3".
intros l H.
apply in_not_nil in H.
apply H.
Qed.


Lemma in_not_nil_42_take4 :
forall l : list nat, In 42 l -> l <> [].
Proof. hammer_hook "Logic" "Logic.in_not_nil_42_take4".
intros l H.
apply (in_not_nil nat 42).
apply H.
Qed.


Lemma in_not_nil_42_take5 :
forall l : list nat, In 42 l -> l <> [].
Proof. hammer_hook "Logic" "Logic.in_not_nil_42_take5".
intros l H.
apply (in_not_nil _ _ _ H).
Qed.



Example lemma_application_ex :
forall {n : nat} {ns : list nat},
In n (map (fun m => m * 0) ns) ->
n = 0.
Proof. hammer_hook "Logic" "Logic.lemma_application_ex".
intros n ns H.
destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
as [m [Hm _]].
rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.













Example function_equality_ex1 :
(fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. hammer_hook "Logic" "Logic.function_equality_ex1". reflexivity. Qed.







Example function_equality_ex2 :
(fun x => plus x 1) = (fun x => plus 1 x).
Proof. hammer_hook "Logic" "Logic.function_equality_ex2".

Abort.



Axiom functional_extensionality : forall {X Y: Type}
{f g : X -> Y},
(forall (x:X), f x = g x) -> f = g.





Example function_equality_ex2 :
(fun x => plus x 1) = (fun x => plus 1 x).
Proof. hammer_hook "Logic" "Logic.function_equality_ex2".
apply functional_extensionality. intros x.
apply plus_comm.
Qed.





Print Assumptions function_equality_ex2.




Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
match l1 with
| [] => l2
| x :: l1' => rev_append l1' (x :: l2)
end.

Definition tr_rev {X} (l : list X) : list X :=
rev_append l [].



Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Admitted.








Example even_42_bool : evenb 42 = true.
Proof. hammer_hook "Logic" "Logic.even_42_bool". reflexivity. Qed.


Example even_42_prop : exists k, 42 = double k.
Proof. hammer_hook "Logic" "Logic.even_42_prop". exists 21. reflexivity. Qed.




Theorem evenb_double : forall k, evenb (double k) = true.
Proof. hammer_hook "Logic" "Logic.evenb_double".
intros k. induction k as [|k' IHk'].
- reflexivity.
- simpl. apply IHk'.
Qed.


Theorem evenb_double_conv : forall n,
exists k, n = if evenb n then double k
else S (double k).
Proof. hammer_hook "Logic" "Logic.evenb_double_conv".

Admitted.


Theorem even_bool_prop : forall n,
evenb n = true <-> exists k, n = double k.
Proof. hammer_hook "Logic" "Logic.even_bool_prop".
intros n. split.
- intros H. destruct (evenb_double_conv n) as [k Hk].
rewrite Hk. rewrite H. exists k. reflexivity.
- intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.





Theorem eqb_eq : forall n1 n2 : nat,
n1 =? n2 = true <-> n1 = n2.
Proof. hammer_hook "Logic" "Logic.eqb_eq".
intros n1 n2. split.
- apply eqb_true.
- intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.







Fail Definition is_even_prime n :=
if n = 2 then true
else false.



Example even_1000 : exists k, 1000 = double k.



Proof. hammer_hook "Logic" "Logic.even_1000". exists 500. reflexivity. Qed.



Example even_1000' : evenb 1000 = true.
Proof. hammer_hook "Logic" "Logic.even_1000'". reflexivity. Qed.



Example even_1000'' : exists k, 1000 = double k.
Proof. hammer_hook "Logic" "Logic.even_1000''". apply even_bool_prop. reflexivity. Qed.





Example not_even_1001 : evenb 1001 = false.
Proof. hammer_hook "Logic" "Logic.not_even_1001".

reflexivity.
Qed.



Example not_even_1001' : ~(exists k, 1001 = double k).
Proof. hammer_hook "Logic" "Logic.not_even_1001'".

rewrite <- even_bool_prop.
unfold not.
simpl.
intro H.
discriminate H.
Qed.



Lemma plus_eqb_example : forall n m p : nat,
n =? m = true -> n + p =? m + p = true.
Proof. hammer_hook "Logic" "Logic.plus_eqb_example".

intros n m p H.
rewrite eqb_eq in H.
rewrite H.
rewrite eqb_eq.
reflexivity.
Qed.





Lemma andb_true_iff : forall b1 b2:bool,
b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof. hammer_hook "Logic" "Logic.andb_true_iff".
Admitted.

Lemma orb_true_iff : forall b1 b2,
b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof. hammer_hook "Logic" "Logic.orb_true_iff".
Admitted.




Theorem eqb_neq : forall x y : nat,
x =? y = false <-> x <> y.
Proof. hammer_hook "Logic" "Logic.eqb_neq".
Admitted.




Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
(l1 l2 : list A) : bool
. Admitted.

Lemma eqb_list_true_iff :
forall A (eqb : A -> A -> bool),
(forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof. hammer_hook "Logic" "Logic.eqb_list_true_iff".
Admitted.




Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
match l with
| [] => true
| x :: l' => andb (test x) (forallb test l')
end.



Theorem forallb_true_iff : forall X test (l : list X),
forallb test l = true <-> All (fun x => test x = true) l.
Proof. hammer_hook "Logic" "Logic.forallb_true_iff".
Admitted.










Definition excluded_middle := forall P : Prop,
P \/ ~ P.





Theorem restricted_excluded_middle : forall P b,
(P <-> b = true) -> P \/ ~ P.
Proof. hammer_hook "Logic" "Logic.restricted_excluded_middle".
intros P [] H.
- left. rewrite H. reflexivity.
- right. rewrite H. intros contra. discriminate contra.
Qed.



Theorem restricted_excluded_middle_eq : forall (n m : nat),
n = m \/ n <> m.
Proof. hammer_hook "Logic" "Logic.restricted_excluded_middle_eq".
intros n m.
apply (restricted_excluded_middle (n = m) (n =? m)).
symmetry.
apply eqb_eq.
Qed.









Theorem excluded_middle_irrefutable: forall (P:Prop),
~ ~ (P \/ ~ P).
Proof. hammer_hook "Logic" "Logic.excluded_middle_irrefutable".
Admitted.




Theorem not_exists_dist :
excluded_middle ->
forall (X:Type) (P : X -> Prop),
~ (exists x, ~ P x) -> (forall x, P x).
Proof. hammer_hook "Logic" "Logic.not_exists_dist".
Admitted.




Definition peirce := forall P Q: Prop,
((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
(P->Q) -> (~P\/Q).




