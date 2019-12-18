From Hammer Require Import Hammer.














From Coq Require Import List Syntax Derive.
From Coq.ssr Require Import ssreflect.
From compcert Require Automaton.
From compcert Require Import Alphabet.
From compcert Require Import Validator_classes.

Module Make(Import A:Automaton.T).


Definition singleton_state_pred (state:state) :=
(fun state' => match compare state state' with Eq => true |_ => false end).


Definition past_state_of_state (state:state) :=
match state with
| Init _ => []
| Ninit nis => past_state_of_non_init_state nis
end.


Definition head_symbs_of_state (state:state) :=
match state with
| Init _ => []
| Ninit s =>
last_symb_of_non_init_state s::past_symb_of_non_init_state s
end.
Definition head_states_of_state (state:state) :=
singleton_state_pred state::past_state_of_state state.




Inductive prefix: list symbol -> list symbol -> Prop :=
| prefix_nil: forall l, prefix [] l
| prefix_cons: forall l1 l2 x, prefix l1 l2 -> prefix (x::l1) (x::l2).


Lemma prefix_trans:
forall (l1 l2 l3:list symbol), prefix l1 l2 -> prefix l2 l3 -> prefix l1 l3.
Proof. hammer_hook "Validator_safe" "Validator_safe.Make.prefix_trans".
intros l1 l2 l3 H1 H2. revert l3 H2.
induction H1; [now constructor|]. inversion 1. subst. constructor. eauto.
Qed.

Fixpoint is_prefix (l1 l2:list symbol) :=
match l1, l2 with
| [], _ => true
| t1::q1, t2::q2 => (compare_eqb t1 t2 && is_prefix q1 q2)%bool
| _::_, [] => false
end.

Instance prefix_is_validator l1 l2 : IsValidator (prefix l1 l2) (is_prefix l1 l2).
Proof. hammer_hook "Validator_safe" "Validator_safe.Make.prefix_is_validator".
revert l2. induction l1 as [|x1 l1 IH]=>l2 Hpref.
- constructor.
- destruct l2 as [|x2 l2]=>//.
move: Hpref=> /andb_prop [/compare_eqb_iff -> /IH ?]. by constructor.
Qed.


Definition shift_head_symbs :=
forall s,
match action_table s with
| Lookahead_act awp => forall t,
match awp t with
| Shift_act s2 _ =>
prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
| _ => True
end
| _ => True
end.


Definition goto_head_symbs :=
forall s nt,
match goto_table s nt with
| Some (exist _ s2 _) =>
prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
| None => True
end.


Inductive prefix_pred: list (state->bool) -> list (state->bool) -> Prop :=
| prefix_pred_nil: forall l, prefix_pred [] l
| prefix_pred_cons: forall l1 l2 f1 f2,
(forall x, implb (f2 x) (f1 x) = true) ->
prefix_pred l1 l2 -> prefix_pred (f1::l1) (f2::l2).


Lemma prefix_pred_trans:
forall (l1 l2 l3:list (state->bool)),
prefix_pred l1 l2 -> prefix_pred l2 l3 -> prefix_pred l1 l3.
Proof. hammer_hook "Validator_safe" "Validator_safe.Make.prefix_pred_trans".
intros l1 l2 l3 H1 H2. revert l3 H2.
induction H1 as [|l1 l2 f1 f2 Hf2f1]; [now constructor|].
intros l3. inversion 1 as [|??? f3 Hf3f2]. subst. constructor; [|now eauto].
intros x. specialize (Hf3f2 x). specialize (Hf2f1 x).
repeat destruct (_ x); auto.
Qed.

Fixpoint is_prefix_pred (l1 l2:list (state->bool)) :=
match l1, l2 with
| [], _ => true
| f1::q1, f2::q2 =>
(forallb (fun x => implb (f2 x) (f1 x)) all_list
&& is_prefix_pred q1 q2)%bool
| _::_, [] => false
end.

Instance prefix_pred_is_validator l1 l2 :
IsValidator (prefix_pred l1 l2) (is_prefix_pred l1 l2).
Proof. hammer_hook "Validator_safe" "Validator_safe.Make.prefix_pred_is_validator".
revert l2. induction l1 as [|x1 l1 IH]=>l2 Hpref.
- constructor.
- destruct l2 as [|x2 l2]=>//.
move: Hpref=> /andb_prop [/forallb_forall ? /IH ?].
constructor; auto using all_list_forall.
Qed.


Definition shift_past_state :=
forall s,
match action_table s with
| Lookahead_act awp => forall t,
match awp t with
| Shift_act s2 _ =>
prefix_pred (past_state_of_non_init_state s2)
(head_states_of_state s)
| _ => True
end
| _ => True
end.


Definition goto_past_state :=
forall s nt,
match goto_table s nt with
| Some (exist _ s2 _) =>
prefix_pred (past_state_of_non_init_state s2)
(head_states_of_state s)
| None => True
end.


Inductive state_valid_after_pop (s:state):
list symbol -> list (state -> bool) -> Prop :=
| state_valid_after_pop_nil1:
forall p pl, p s = true -> state_valid_after_pop s [] (p::pl)
| state_valid_after_pop_nil2:
forall sl, state_valid_after_pop s sl []
| state_valid_after_pop_cons:
forall st sq p pl, state_valid_after_pop s sq pl ->
state_valid_after_pop s (st::sq) (p::pl).

Fixpoint is_state_valid_after_pop (state:state) (to_pop:list symbol) annot :=
match annot, to_pop with
| [], _ => true
| p::_, [] => p state
| p::pl, s::sl => is_state_valid_after_pop state sl pl
end.

Instance impl_is_state_valid_after_pop_is_validator state sl pl P b :
IsValidator P b ->
IsValidator (state_valid_after_pop state sl pl -> P)
(if is_state_valid_after_pop state sl pl then b else true).
Proof. hammer_hook "Validator_safe" "Validator_safe.Make.impl_is_state_valid_after_pop_is_validator".
destruct (is_state_valid_after_pop _ sl pl) eqn:EQ.
- intros ???. by eapply is_validator.
- intros _ _ Hsvap. exfalso. induction Hsvap=>//; [simpl in EQ; congruence|].
by destruct sl.
Qed.


Definition valid_for_reduce (state:state) prod :=
prefix (prod_rhs_rev prod) (head_symbs_of_state state) /\
forall state_new,
state_valid_after_pop state_new
(prod_rhs_rev prod) (head_states_of_state state) ->
match goto_table state_new (prod_lhs prod) with
| None =>
match state_new with
| Init i => prod_lhs prod = start_nt i
| Ninit _ => False
end
| _ => True
end.


Definition reduce_ok :=
forall s,
match action_table s with
| Lookahead_act awp =>
forall t, match awp t with
| Reduce_act p => valid_for_reduce s p
| _ => True
end
| Default_reduce_act p => valid_for_reduce s p
end.


Definition safe :=
shift_head_symbs /\ goto_head_symbs /\ shift_past_state /\
goto_past_state /\ reduce_ok.

Derive is_safe
SuchThat (IsValidator safe (is_safe ()))
As safe_is_validator.
Proof. hammer_hook "Validator_safe" "Validator_safe.Make.safe". subst is_safe. instantiate (1:=fun _ => _). apply _. Qed.

End Make.
