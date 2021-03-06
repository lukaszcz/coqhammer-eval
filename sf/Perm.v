From Hammer Require Import Hammer.





Require Import Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.






Check Nat.lt.
Check lt.
Goal Nat.lt = lt. Proof. reflexivity. Qed.
Check Nat.ltb.
Locate "_ < _".
Locate "<?".



Check Nat.ltb_lt.




Notation  "a >=? b" := (Nat.leb b a)
(at level 70, only parsing) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a)
(at level 70, only parsing) : nat_scope.
Notation " a =? b"  := (beq_nat a b)
(at level 70) : nat_scope.






Print reflect.



Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof. hammer_hook "Perm" "Perm.beq_reflect".
intros x y.
apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof. hammer_hook "Perm" "Perm.blt_reflect".
intros x y.
apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof. hammer_hook "Perm" "Perm.ble_reflect".
intros x y.
apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.



Example reflect_example1: forall a, (if a<?5 then a else 2) < 6.
Proof. hammer_hook "Perm" "Perm.reflect_example1".
intros.
destruct (blt_reflect a 5) as [H|H].
*
omega.
*
apply not_lt in H.
omega.
Qed.







Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.



Ltac bdestruct X :=
let H := fresh in let e := fresh "e" in
evar (e: Prop);
assert (H: reflect e X); subst e;
[eauto with bdestruct
| destruct H as [H|H];
[ | try first [apply not_lt in H | apply not_le in H]]].



Example reflect_example2: forall a, (if a<?5 then a else 2) < 6.
Proof. hammer_hook "Perm" "Perm.reflect_example2".
intros.
bdestruct (a<?5).
*
omega.
*
omega.
Qed.





Ltac inv H := inversion H; clear H; subst.






Module Exploration1.

Theorem omega_example1:
forall i j k,
i < j ->
~ (k - 3 <= j) ->
k > i.
Proof. hammer_hook "Perm" "Perm.Exploration1.omega_example1".
intros.




Search (~ _ <= _ -> _).
apply not_le in H0.

Search (_ > _ -> _ > _ -> _ > _).
apply gt_trans with j.
apply gt_trans with (k-3).

Abort.

Theorem bogus_subtraction: ~ (forall k:nat, k > k - 3).
Proof. hammer_hook "Perm" "Perm.Exploration1.bogus_subtraction".

intro.

specialize (H O).
simpl in H. inversion H.
Qed.



Theorem omega_example1:
forall i j k,
i < j ->
~ (k - 3 <= j) ->
k > i.
Proof. hammer_hook "Perm" "Perm.Exploration1.omega_example1".
intros.
apply not_le in H0.
unfold gt in H0.
unfold gt.

Search (_ < _ -> _ <= _ -> _ < _).
apply lt_le_trans with j.
apply H.
apply le_trans with (k-3).
Search (_ < _ -> _ <= _).
apply lt_le_weak.
auto.
apply le_minus.
Qed.



Theorem omega_example2:
forall i j k,
i < j ->
~ (k - 3 <= j) ->
k > i.
Proof. hammer_hook "Perm" "Perm.Exploration1.omega_example2".
intros.
omega.
Qed.



Definition maybe_swap (al: list nat) : list nat :=
match al with
| a :: b :: ar => if a >? b then b::a::ar else a::b::ar
| _ => al
end.

Example maybe_swap_123:
maybe_swap [1; 2; 3] = [1; 2; 3].
Proof. hammer_hook "Perm" "Perm.Exploration1.maybe_swap_123". reflexivity. Qed.

Example maybe_swap_321:
maybe_swap [3; 2; 1] = [2; 3; 1].
Proof. hammer_hook "Perm" "Perm.Exploration1.maybe_swap_321". reflexivity. Qed.



Check (1>2).
Check (1>?2).



Locate ">?".



Print Nat.ltb.

Locate ">=?".



Locate leb.
Print leb.
Print Nat.leb.



Theorem maybe_swap_idempotent:
forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof. hammer_hook "Perm" "Perm.Exploration1.maybe_swap_idempotent".
intros.
destruct al as [ | a al].
simpl.
reflexivity.
destruct al as [ | b al].
simpl.
reflexivity.
simpl.



destruct (b <? a) eqn:H.
simpl.
destruct (a <? b) eqn:H0.



try omega.



Abort.



Theorem maybe_swap_idempotent:
forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof. hammer_hook "Perm" "Perm.Exploration1.maybe_swap_idempotent".
intros.
destruct al as [ | a al].
simpl.
reflexivity.
destruct al as [ | b al].
simpl.
reflexivity.
simpl.



destruct (blt_reflect b a).



*
simpl.
bdestruct (a <? b).
omega.



reflexivity.
*
simpl.
bdestruct (b <? a).
omega.
reflexivity.
Qed.



Theorem maybe_swap_idempotent':
forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof. hammer_hook "Perm" "Perm.Exploration1.maybe_swap_idempotent'".
intros.
destruct al as [ | a al].
simpl.
reflexivity.
destruct al as [ | b al].
simpl.
reflexivity.
simpl.
bdestruct (b <? a).
*
simpl.
bdestruct (a <? b).
omega.
reflexivity.
*
simpl.
bdestruct (b <? a).
omega.
reflexivity.
Qed.






Locate Permutation.
Check Permutation.



Print Permutation.









Search Permutation.



Definition manual_grade_for_Permutation_properties : option (prod nat string) := None.




Example butterfly: forall b u t e r f l y : nat,
Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof. hammer_hook "Perm" "Perm.Exploration1.butterfly".
intros.

change [b;u;t;t;e;r] with ([b]++[u;t;t;e;r]).
change [f;l;u;t;t;e;r] with ([f;l]++[u;t;t;e;r]).
remember [u;t;t;e;r] as utter.
clear Hequtter.

Check app_assoc.
rewrite <- app_assoc.
rewrite <- app_assoc.
Check perm_trans.
apply perm_trans with (utter ++ [f;l;y] ++ [b]).
rewrite (app_assoc utter [f;l;y]).
Check Permutation_app_comm.
apply Permutation_app_comm.
eapply perm_trans.
2: apply Permutation_app_comm.
rewrite <- app_assoc.
Search (Permutation (_++_) (_++_)).
apply Permutation_app_head.

eapply perm_trans.
2: apply Permutation_app_comm.
simpl.
Check perm_skip.
apply perm_skip.
apply perm_skip.
Search (Permutation (_::_) (_::_)).
apply perm_swap.
Qed.






Check perm_skip.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.

Example permut_example: forall (a b: list nat),
Permutation (5::6::a++b) ((5::b)++(6::a++[])).
Proof. hammer_hook "Perm" "Perm.Exploration1.permut_example".

Admitted.





Check Permutation_cons_inv.
Check Permutation_length_1_inv.

Example not_a_permutation:
~ Permutation [1;1] [1;2].
Proof. hammer_hook "Perm" "Perm.Exploration1.not_a_permutation".
Admitted.




Theorem maybe_swap_perm: forall al,
Permutation al (maybe_swap al).
Proof. hammer_hook "Perm" "Perm.Exploration1.maybe_swap_perm".

intros.
destruct al as [ | a al].
simpl. apply Permutation_refl.
destruct al as [ | b al].
simpl. apply Permutation_refl.
simpl.
bdestruct (a>?b).
apply perm_swap.
apply Permutation_refl.
Qed.



Definition first_le_second (al: list nat) : Prop :=
match al with
| a::b::_ => a <= b
| _ => True
end.

Theorem maybe_swap_correct: forall al,
Permutation al (maybe_swap al)
/\ first_le_second (maybe_swap al).
Proof. hammer_hook "Perm" "Perm.Exploration1.maybe_swap_correct".
intros.
split.
apply maybe_swap_perm.

destruct al as [ | a al].
simpl. auto.
destruct al as [ | b al].
simpl. auto.
simpl.
bdestruct (b <? a).
simpl.
omega.
simpl.
omega.
Qed.

End Exploration1.









Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
Permutation al bl ->
Forall f al -> Forall f bl.
Proof. hammer_hook "Perm" "Perm.Forall_perm".
Admitted.



