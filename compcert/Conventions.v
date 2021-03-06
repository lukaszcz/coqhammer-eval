From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import AST.
From compcert Require Import Locations.
From compcert Require Export Conventions1.



Lemma loc_arguments_acceptable_2:
forall s l,
In l (regs_of_rpairs (loc_arguments s)) -> loc_argument_acceptable l.
Proof. hammer_hook "Conventions" "Conventions.loc_arguments_acceptable_2".
intros until l. generalize (loc_arguments_acceptable s). generalize (loc_arguments s).
induction l0 as [ | p pl]; simpl; intros.
- contradiction.
- rewrite in_app_iff in H0. destruct H0.
exploit H; eauto. destruct p; simpl in *; intuition congruence.
apply IHpl; auto.
Qed.





Definition parameter_of_argument (l: loc) : loc :=
match l with
| S Outgoing n ty => S Incoming n ty
| _ => l
end.

Definition loc_parameters (s: signature) : list (rpair loc) :=
List.map (map_rpair parameter_of_argument) (loc_arguments s).

Lemma incoming_slot_in_parameters:
forall ofs ty sg,
In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters sg)) ->
In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)).
Proof. hammer_hook "Conventions" "Conventions.incoming_slot_in_parameters".
intros.
replace (regs_of_rpairs (loc_parameters sg)) with (List.map parameter_of_argument (regs_of_rpairs (loc_arguments sg))) in H.
change (S Incoming ofs ty) with (parameter_of_argument (S Outgoing ofs ty)) in H.
exploit list_in_map_inv. eexact H. intros [x [A B]]. simpl in A.
exploit loc_arguments_acceptable_2; eauto. unfold loc_argument_acceptable; intros.
destruct x; simpl in A; try discriminate.
destruct sl; try contradiction.
inv A. auto.
unfold loc_parameters. generalize (loc_arguments sg). induction l as [ | p l]; simpl; intros.
auto.
rewrite map_app. f_equal; auto. destruct p; auto.
Qed.







Definition tailcall_possible (s: signature) : Prop :=
forall l, In l (regs_of_rpairs (loc_arguments s)) ->
match l with R _ => True | S _ _ _ => False end.



Definition tailcall_is_possible (sg: signature) : bool :=
List.forallb
(fun l => match l with R _ => true | S _ _ _ => false end)
(regs_of_rpairs (loc_arguments sg)).

Lemma tailcall_is_possible_correct:
forall s, tailcall_is_possible s = true -> tailcall_possible s.
Proof. hammer_hook "Conventions" "Conventions.tailcall_is_possible_correct".
unfold tailcall_is_possible; intros. rewrite forallb_forall in H.
red; intros. apply H in H0. destruct l; [auto|discriminate].
Qed.

Lemma zero_size_arguments_tailcall_possible:
forall sg, size_arguments sg = 0 -> tailcall_possible sg.
Proof. hammer_hook "Conventions" "Conventions.zero_size_arguments_tailcall_possible".
intros; red; intros. exploit loc_arguments_acceptable_2; eauto.
unfold loc_argument_acceptable.
destruct l; intros. auto. destruct sl; try contradiction. destruct H1.
generalize (loc_arguments_bounded _ _ _ H0).
generalize (typesize_pos ty). omega.
Qed.






Definition callee_save_loc (l: loc) :=
match l with
| R r => is_callee_save r = true
| S sl ofs ty => sl <> Outgoing
end.

Definition agree_callee_save (ls1 ls2: Locmap.t) : Prop :=
forall l, callee_save_loc l -> ls1 l = ls2 l.





Lemma locmap_get_set_loc_result:
forall sg v rs l,
match l with R r => is_callee_save r = true | S _ _ _ => True end ->
Locmap.setpair (loc_result sg) v rs l = rs l.
Proof. hammer_hook "Conventions" "Conventions.locmap_get_set_loc_result".
intros. apply Locmap.gpo.
assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
{ intros. destruct l; simpl. congruence. auto. }
generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

Lemma locmap_get_set_loc_result_callee_save:
forall sg v rs l,
callee_save_loc l ->
Locmap.setpair (loc_result sg) v rs l = rs l.
Proof. hammer_hook "Conventions" "Conventions.locmap_get_set_loc_result_callee_save".
intros. apply locmap_get_set_loc_result.
red in H; destruct l; auto.
Qed.
