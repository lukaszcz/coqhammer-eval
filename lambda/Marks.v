From Hammer Require Import Hammer.







































Require Import Arith.
From Lambda Require Import Terms.
From Lambda Require Import Reduction.
From Lambda Require Import Redexes.
From Lambda Require Import Test.



Fixpoint mark (e : lambda) : redexes :=
match e with
| Ref n => Var n
| Abs M => Fun (mark M)
| App M N => Ap false (mark M) (mark N)
end.




Fixpoint unmark (e : redexes) : lambda :=
match e with
| Var n => Ref n
| Fun U => Abs (unmark U)
| Ap b U V => App (unmark U) (unmark V)
end.

Lemma inverse : forall M : lambda, M = unmark (mark M).
Proof. hammer_hook "Marks" "Marks.inverse".
simple induction M; simpl in |- *; trivial; simple induction 1; trivial.
simple induction 1; trivial.
Qed.

Lemma comp_unmark_eq : forall U V : redexes, comp U V -> unmark U = unmark V.
Proof. hammer_hook "Marks" "Marks.comp_unmark_eq".
simple induction 1; simpl in |- *; trivial.
simple induction 2; trivial.
simple induction 2; simple induction 2; trivial.
Qed.


