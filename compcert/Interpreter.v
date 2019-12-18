From Hammer Require Import Hammer.














From Coq Require Import List Syntax.
From Coq.ssr Require Import ssreflect.
From compcert Require Automaton.
From compcert Require Import Alphabet.
From compcert Require Import Grammar.
From compcert Require Import Validator_safe.

Module Make(Import A:Automaton.T).
Module Import ValidSafe := Validator_safe.Make A.




Class Decidable (P : Prop) := decide : {P} + {~P}.
Arguments decide _ {_}.


Instance comparable_decidable_eq T `{ComparableLeibnizEq T} (x y : T) :
Decidable (x = y).
Proof. hammer_hook "Interpreter" "Interpreter.Make.comparable_decidable_eq".
unfold Decidable.
destruct (compare x y) eqn:EQ; [left; apply compare_eq; intuition | ..];
right; intros ->; by rewrite compare_refl in EQ.
Defined.

Instance list_decidable_eq T :
(forall x y : T, Decidable (x = y)) ->
(forall l1 l2 : list T, Decidable (l1 = l2)).
Proof. hammer_hook "Interpreter" "Interpreter.Make.list_decidable_eq". unfold Decidable. decide equality. Defined.

Ltac subst_existT :=
repeat
match goal with
| _ => progress subst
| H : @existT ?A ?P ?x ?y1 = @existT ?A ?P ?x ?y2 |- _ =>
let DEC := fresh in
assert (DEC : forall u1 u2 : A, Decidable (u1 = u2)) by apply _;
apply Eqdep_dec.inj_pair2_eq_dec in H; [|by apply DEC];
clear DEC
end.


Definition thunkP (P : Prop) : Prop := True -> P.


Definition reprove {P} `{Decidable P} (p : thunkP P) : P :=
match decide P with
| left p => p
| right np => False_ind _ (np (p I))
end.


Definition cast {T : Type} (F : T -> Type) {x y : T} (eq : thunkP (x = y))
{DEC : unit -> Decidable (x = y)}:
F x -> F y :=
fun a => eq_rect x F a y (@reprove _ (DEC ()) eq).

Lemma cast_eq T F (x : T) (eq : thunkP (x = x)) `{forall x y, Decidable (x = y)} a :
cast F eq a = a.
Proof. hammer_hook "Interpreter" "Interpreter.Make.cast_eq". by rewrite /cast -Eqdep_dec.eq_rect_eq_dec. Qed.


CoInductive buffer : Type :=
Buf_cons { buf_head : token; buf_tail : buffer }.

Delimit Scope buffer_scope with buf.
Bind Scope buffer_scope with buffer.

Infix "::" := Buf_cons (at level 60, right associativity) : buffer_scope.


Fixpoint app_buf (l:list token) (buf:buffer) :=
match l with
| nil => buf
| cons t q => (t :: app_buf q buf)%buf
end.
Infix "++" := app_buf (at level 60, right associativity) : buffer_scope.

Lemma app_buf_assoc (l1 l2:list token) (buf:buffer) :
(l1 ++ (l2 ++ buf) = (l1 ++ l2) ++ buf)%buf.
Proof. hammer_hook "Interpreter" "Interpreter.Make.app_buf_assoc". induction l1 as [|?? IH]=>//=. rewrite IH //. Qed.


Definition noninitstate_type state :=
symbol_semantic_type (last_symb_of_non_init_state state).


Definition stack := list (sigT noninitstate_type).

Section Interpreter.

Hypothesis safe: safe.


Proposition shift_head_symbs: shift_head_symbs.
Proof. hammer_hook "Interpreter" "Interpreter.Make.stack". pose proof safe; unfold ValidSafe.safe in H; intuition. Qed.
Proposition goto_head_symbs: goto_head_symbs.
Proof. pose proof safe; unfold ValidSafe.safe in H; intuition. Qed.
Proposition shift_past_state: shift_past_state.
Proof. pose proof safe; unfold ValidSafe.safe in H; intuition. Qed.
Proposition goto_past_state: goto_past_state.
Proof. pose proof safe; unfold ValidSafe.safe in H; intuition. Qed.
Proposition reduce_ok: reduce_ok.
Proof. pose proof safe; unfold ValidSafe.safe in H; intuition. Qed.

Variable init : initstate.


Definition state_of_stack (stack:stack): state :=
match stack with
| [] => init
| existT _ s _::_ => s
end.


Definition state_stack_of_stack (stack:stack) :=
(List.map
(fun cell:sigT noninitstate_type => singleton_state_pred (projT1 cell))
stack ++ [singleton_state_pred init])%list.


Definition symb_stack_of_stack (stack:stack) :=
List.map
(fun cell:sigT noninitstate_type => last_symb_of_non_init_state (projT1 cell))
stack.


Inductive stack_invariant: stack -> Prop :=
| stack_invariant_constr:
forall stack,
prefix      (head_symbs_of_state (state_of_stack stack))
(symb_stack_of_stack stack) ->
prefix_pred (head_states_of_state (state_of_stack stack))
(state_stack_of_stack stack) ->
stack_invariant_next stack ->
stack_invariant stack
with stack_invariant_next: stack -> Prop :=
| stack_invariant_next_nil:
stack_invariant_next []
| stack_invariant_next_cons:
forall state_cur st stack_rec,
stack_invariant stack_rec ->
stack_invariant_next (existT _ state_cur st::stack_rec).


Fixpoint pop (symbols_to_pop:list symbol) {A:Type} (stk:stack) :
thunkP (prefix symbols_to_pop (symb_stack_of_stack stk)) ->
forall (action:arrows_right A (map symbol_semantic_type symbols_to_pop)),
stack * A.
unshelve refine
(match symbols_to_pop
return
(thunkP (prefix symbols_to_pop (symb_stack_of_stack stk))) ->
forall (action:arrows_right A (map _ symbols_to_pop)), stack * A
with
| [] => fun _ action => (stk, action)
| t::q => fun Hp action =>
match stk
return thunkP (prefix (t::q) (symb_stack_of_stack stk)) -> stack * A
with
| existT _ state_cur sem::stack_rec => fun Hp =>
let sem_conv := cast symbol_semantic_type _ sem in
pop q _ stack_rec _ (action sem_conv)
| [] => fun Hp => False_rect _ _
end Hp
end).
Proof. hammer_hook "Interpreter" "Interpreter.Make.symb_stack_of_stack".
- simpl in Hp. clear -Hp. abstract (intros _ ; specialize (Hp I); now inversion Hp).
- clear -Hp. abstract (specialize (Hp I); now inversion Hp).
- simpl in Hp. clear -Hp. abstract (intros _ ; specialize (Hp I); now inversion Hp).
Defined.


Inductive pop_spec {A:Type} :
forall (symbols_to_pop:list symbol) (stk : stack)
(action : arrows_right A (map symbol_semantic_type symbols_to_pop))
(stk' : stack) (sem : A),
Prop :=
| Nil_pop_spec stk sem : pop_spec [] stk sem stk sem
| Cons_pop_spec symbols_to_pop st stk action sem stk' res :
pop_spec symbols_to_pop stk (action sem) stk' res ->
pop_spec (last_symb_of_non_init_state st::symbols_to_pop)
(existT _ st sem :: stk) action stk' res.

Lemma pop_spec_ok {A:Type} symbols_to_pop stk Hp action stk' res:
pop symbols_to_pop stk Hp action = (stk', res) <->
pop_spec (A:=A) symbols_to_pop stk action stk' res.
Proof. hammer_hook "Interpreter" "Interpreter.Make.pop_spec_ok".
revert stk Hp action.
induction symbols_to_pop as [|t symbols_to_pop IH]=>stk Hp action /=.
- split.
+ intros [= <- <-]. constructor.
+ intros H. inversion H. by subst_existT.
- destruct stk as [|[st sem]]=>/=; [by destruct pop_subproof0|].
remember (pop_subproof t symbols_to_pop stk st Hp) as EQ eqn:eq. clear eq.
generalize EQ. revert Hp action. rewrite <-(EQ I)=>Hp action ?.
rewrite cast_eq. rewrite IH. split.
+ intros. by constructor.
+ intros H. inversion H. by subst_existT.
Qed.


Lemma pop_preserves_invariant symbols_to_pop stk Hp A action :
stack_invariant stk ->
stack_invariant (fst (pop symbols_to_pop stk Hp (A:=A) action)).
Proof. hammer_hook "Interpreter" "Interpreter.Make.pop_preserves_invariant".
revert stk Hp A action. induction symbols_to_pop as [|t q IH]=>//=.
intros stk Hp A action Hi.
destruct Hi as [stack Hp' Hpp [|state st stk']].
- destruct pop_subproof0.
- now apply IH.
Qed.

Lemma pop_state_valid symbols_to_pop stk Hp A action lpred :
prefix_pred lpred (state_stack_of_stack stk) ->
let stk' := fst (pop symbols_to_pop stk Hp (A:=A) action) in
state_valid_after_pop (state_of_stack stk') symbols_to_pop lpred.
Proof. hammer_hook "Interpreter" "Interpreter.Make.pop_state_valid".
revert stk Hp A action lpred. induction symbols_to_pop as [|t q IH]=>/=.
- intros stk Hp A a lpred Hpp. destruct lpred as [|pred lpred]; constructor.
inversion Hpp as [|? lpred' ? pred' Himpl Hpp' eq1 eq2]; subst.
specialize (Himpl (state_of_stack stk)).
destruct (pred' (state_of_stack stk)) as [] eqn:Heqpred'=>//.
destruct stk as [|[]]; simpl in *.
+ inversion eq2; subst; clear eq2.
unfold singleton_state_pred in Heqpred'.
now rewrite compare_refl in Heqpred'; discriminate.
+ inversion eq2; subst; clear eq2.
unfold singleton_state_pred in Heqpred'.
now rewrite compare_refl in Heqpred'; discriminate.
- intros stk Hp A a lpred Hpp. destruct stk as [|[] stk]=>//=.
+ destruct pop_subproof0.
+ destruct lpred as [|pred lpred]; [by constructor|].
constructor. apply IH. by inversion Hpp.
Qed.


Inductive step_result :=
| Fail_sr: step_result
| Accept_sr: symbol_semantic_type (NT (start_nt init)) -> buffer -> step_result
| Progress_sr: stack -> buffer -> step_result.


Definition reduce_step stk prod (buffer : buffer)
(Hval : thunkP (valid_for_reduce (state_of_stack stk) prod))
(Hi : thunkP (stack_invariant stk))
: step_result.
refine
((let '(stk', sem) as ss := pop (prod_rhs_rev prod) stk _ (prod_action prod)
return thunkP (state_valid_after_pop (state_of_stack (fst ss)) _
(head_states_of_state (state_of_stack stk))) -> _
in fun Hval' =>
match goto_table (state_of_stack stk') (prod_lhs prod) as goto
return (thunkP (goto = None ->
match state_of_stack stk' with
| Init i => prod_lhs prod = start_nt i
| Ninit _ => False
end)) -> _
with
| Some (exist _ state_new e) => fun _ =>
let sem := eq_rect _ _ sem _ e in
Progress_sr (existT noninitstate_type state_new sem::stk') buffer
| None => fun Hval =>
let sem := cast symbol_semantic_type _ sem in
Accept_sr sem buffer
end (fun _ => _))
(fun _ => pop_state_valid _ _ _ _ _ _ _)).
Proof. hammer_hook "Interpreter" "Interpreter.Make.reduce_step".
- clear -Hi Hval.
abstract (intros _; destruct Hi=>//; eapply prefix_trans; [by apply Hval|eassumption]).
- clear -Hval.
abstract (intros _; f_equal; specialize (Hval I eq_refl); destruct stk' as [|[]]=>//).
- simpl in Hval'. clear -Hval Hval'.
abstract (move : Hval => /(_ I) [_ /(_ _ (Hval' I))] Hval2 Hgoto; by rewrite Hgoto in Hval2).
- clear -Hi. abstract by destruct Hi.
Defined.

Lemma reduce_step_stack_invariant_preserved stk prod buffer Hv Hi stk' buffer':
reduce_step stk prod buffer Hv Hi = Progress_sr stk' buffer' ->
stack_invariant stk'.
Proof. hammer_hook "Interpreter" "Interpreter.Make.reduce_step_stack_invariant_preserved".
unfold reduce_step.
match goal with
| |- context [pop ?symbols_to_pop stk ?Hp ?action] =>
assert (Hi':=pop_preserves_invariant symbols_to_pop stk Hp _ action (Hi I));
generalize (pop_state_valid symbols_to_pop stk Hp _ action)
end.
destruct pop as [stk0 sem]=>/=. simpl in Hi'. intros Hv'.
assert (Hgoto1:=goto_head_symbs (state_of_stack stk0) (prod_lhs prod)).
assert (Hgoto2:=goto_past_state (state_of_stack stk0) (prod_lhs prod)).
match goal with | |- context [fun _ : True => ?X] => generalize X end.
destruct goto_table as [[state_new e]|] eqn:EQgoto=>//.
intros _ [= <- <-]. constructor=>/=.
- constructor. eapply prefix_trans. apply Hgoto1. by destruct Hi'.
- unfold state_stack_of_stack; simpl; constructor.
+ intros ?. by destruct singleton_state_pred.
+ eapply prefix_pred_trans. apply Hgoto2. by destruct Hi'.
- by constructor.
Qed.


Definition step stk buffer (Hi : thunkP (stack_invariant stk)): step_result :=
match action_table (state_of_stack stk) as a return
thunkP
match a return Prop with
| Default_reduce_act prod => _
| Lookahead_act awt => forall t : terminal,
match awt t with
| Reduce_act p => _
| _ => True
end
end -> _
with
| Default_reduce_act prod => fun Hv =>
reduce_step stk prod buffer Hv Hi
| Lookahead_act awt => fun Hv =>
match buf_head buffer with
| tok =>
match awt (token_term tok) as a return
thunkP match a return Prop with Reduce_act p => _ | _ => _ end -> _
with
| Shift_act state_new e => fun _ =>
let sem_conv := eq_rect _ symbol_semantic_type (token_sem tok) _ e in
Progress_sr (existT noninitstate_type state_new sem_conv::stk)
(buf_tail buffer)
| Reduce_act prod => fun Hv =>
reduce_step stk prod buffer Hv Hi
| Fail_act => fun _ =>
Fail_sr
end (fun _ => Hv I (token_term tok))
end
end (fun _ => reduce_ok _).

Lemma step_stack_invariant_preserved stk buffer Hi stk' buffer':
step stk buffer Hi = Progress_sr stk' buffer' ->
stack_invariant stk'.
Proof. hammer_hook "Interpreter" "Interpreter.Make.step_stack_invariant_preserved".
unfold step.
generalize (reduce_ok (state_of_stack stk))=>Hred.
assert (Hshift1 := shift_head_symbs (state_of_stack stk)).
assert (Hshift2 := shift_past_state (state_of_stack stk)).
destruct action_table as [prod|awt]=>/=.
- eauto using reduce_step_stack_invariant_preserved.
- set (term := token_term (buf_head buffer)).
generalize (Hred term). clear Hred. intros Hred.
specialize (Hshift1 term). specialize (Hshift2 term).
destruct (awt term) as [state_new e|prod|]=>//.
+ intros [= <- <-]. constructor=>/=.
* constructor. eapply prefix_trans. apply Hshift1. by destruct Hi.
* unfold state_stack_of_stack; simpl; constructor.
-- intros ?. by destruct singleton_state_pred.
-- eapply prefix_pred_trans. apply Hshift2. by destruct Hi.
* constructor; by apply Hi.
+ eauto using reduce_step_stack_invariant_preserved.
Qed.


Fixpoint parse_fix stk buffer (log_n_steps : nat) (Hi : thunkP (stack_invariant stk)):
{ sr : step_result |
forall stk' buffer', sr = Progress_sr stk' buffer' -> stack_invariant stk' } :=
match log_n_steps with
| O => exist _ (step stk buffer Hi)
(step_stack_invariant_preserved _ _ Hi)
| S log_n_steps =>
match parse_fix stk buffer log_n_steps Hi with
| exist _ (Progress_sr stk buffer) Hi' =>
parse_fix stk buffer log_n_steps (fun _ => Hi' _ buffer eq_refl)
| sr => sr
end
end.


Inductive parse_result {A : Type} :=
| Fail_pr: parse_result
| Timeout_pr: parse_result
| Parsed_pr: A -> buffer -> parse_result.
Global Arguments parse_result _ : clear implicits.

Definition parse (buffer : buffer) (log_n_steps : nat):
parse_result (symbol_semantic_type (NT (start_nt init))).
refine (match proj1_sig (parse_fix [] buffer log_n_steps _) with
| Fail_sr => Fail_pr
| Accept_sr sem buffer' => Parsed_pr sem buffer'
| Progress_sr _ _ => Timeout_pr
end).
Proof. hammer_hook "Interpreter" "Interpreter.Make.parse".
abstract (repeat constructor; intros; by destruct singleton_state_pred).
Defined.

End Interpreter.

Arguments Fail_sr {init}.
Arguments Accept_sr {init} _ _.
Arguments Progress_sr {init} _ _.

End Make.

Module Type T(A:Automaton.T).
Include (Make A).
End T.
