From Hammer Require Import Hammer.







Inductive reflect (P Q : Prop) : bool -> Type :=
| reflect_true : P -> reflect P Q true
| reflect_false : Q -> reflect P Q false.

Inductive semi_reflect (P : Prop) : bool -> Type :=
| semi_reflect_true : P -> semi_reflect P true
| semi_reflect_false : semi_reflect P false.

Lemma iff_to_reflect {A B} (P : A -> B -> Prop) (T : A -> B -> bool)  :
(forall x y, T x y = true <-> P x y) ->
(forall x y, reflect (P x y) (~P x y) (T x y)).
Proof. hammer_hook "Consider" "Consider.iff_to_reflect".
intros. case_eq (T x y); intros Hxy; constructor.
apply H. assumption.
intros Hf. apply H in Hf. congruence.
Qed.

Lemma impl_to_semireflect {A B} (P : A -> B -> Prop) (T : A -> B -> bool)  :
(forall x y, T x y = true -> P x y) ->
(forall x y, semi_reflect (P x y) (T x y)).
Proof. hammer_hook "Consider" "Consider.impl_to_semireflect".
intros. case_eq (T x y); intros Hxy; constructor.
apply H; auto.
Qed.

Lemma reflect_true_inv P Q : reflect P Q true -> P.
Proof. hammer_hook "Consider" "Consider.reflect_true_inv".
exact (fun x => match x in reflect _ _ b
return if b then P else ID
with | reflect_true _ _ H => H | reflect_false _ _ H => (fun _ x => x) end).
Qed.

Lemma reflect_false_inv P Q : reflect P Q false -> Q.
Proof. hammer_hook "Consider" "Consider.reflect_false_inv".
exact (fun x => match x in reflect _ _ b
return if b then ID else Q
with | reflect_true _ _ H => fun _ x => x | reflect_false _ _ H => H end).
Qed.

Lemma semi_reflect_true_inv P : semi_reflect P true -> P.
Proof. hammer_hook "Consider" "Consider.semi_reflect_true_inv".
exact (fun x => match x in semi_reflect _ b
return if b then P else ID
with | semi_reflect_true _ H => H | semi_reflect_false _ => (fun _ x => x) end).
Qed.


Class Reflect (T : bool) (P Q : Prop) := _Reflect : reflect P Q T.
Class SemiReflect (T : bool) (P : Prop) := _SemiReflect : semi_reflect P T.

Section boolean_logic.
Ltac t :=
repeat match goal with
| H: Reflect true ?P ?Q |- _ => apply (reflect_true_inv P Q) in H
| H: Reflect false ?P ?Q |- _ => apply (reflect_false_inv P Q) in H
end.

Context {T1 T2 P1 Q1 P2 Q2} {R1 : Reflect T1 P1 Q1} {R2: Reflect T2 P2 Q2}.

Global Instance Reflect_andb : Reflect (T1 && T2)%bool (P1 /\ P2) (Q1 \/ Q2).
Proof. hammer_hook "Consider" "Consider.Reflect_andb".
destruct T1; destruct T2; t; constructor; tauto.
Qed.

Global Instance Reflect_orb : Reflect (T1 || T2)%bool (P1 \/ P2) (Q1 /\ Q2).
Proof. hammer_hook "Consider" "Consider.Reflect_orb".
destruct T1; destruct T2; t; constructor; tauto.
Qed.

Global Instance Reflect_negb : Reflect (negb T1)%bool Q1 P1.
Proof. hammer_hook "Consider" "Consider.Reflect_negb".
destruct T1; t; constructor; tauto.
Qed.

End boolean_logic.

Require Import ExtLib.Core.RelDec.

Section from_rel_dec.
Variable T : Type.
Variable eqt : T -> T -> Prop.
Variable rd : RelDec eqt.
Variable rdc : RelDec_Correct rd.

Global Instance Reflect_RelDecCorrect (a b : T)
: Reflect (rel_dec a b) (eqt a b) (~(eqt a b)).
Proof. hammer_hook "Consider" "Consider.Reflect_RelDecCorrect".
eapply iff_to_reflect.
eapply rel_dec_correct.
Qed.
End from_rel_dec.

Hint Extern 10 (@Reflect (?f ?a ?b) _ _) =>
eapply (@Reflect_RelDecCorrect _ _ (@Build_RelDec _ _ f) _) : typeclass_instances.



Ltac consider f :=
let rec clean :=
match goal with
| |- true = true -> _ => intros _ ; clean
| |- false = true -> _ => discriminate
| |- ?P1 -> ?P2 =>
let H := fresh in intros H ; clean; revert H
| |- _ => idtac
end
in
(repeat match goal with
| [ H : context [ f ] |- _ ] =>
revert H
end) ;
match type of f with
| sumbool _ _ =>
destruct f
| _ =>
match goal with
| _ =>
((let c := constr:(_ : Reflect f _ _) in
case c))
| _ =>
((let c := constr:(_ : SemiReflect f _) in
case c))
| _ =>

case_eq f
end
end ; clean.
