From Hammer Require Import Hammer.


















Require Import String.
From compcert Require Import Coqlib.

Close Scope string_scope.

Set Implicit Arguments.





Inductive errcode: Type :=
| MSG: string -> errcode
| CTX: positive -> errcode
| POS: positive -> errcode.

Definition errmsg: Type := list errcode.

Definition msg (s: string) : errmsg := MSG s :: nil.





Inductive res (A: Type) : Type :=
| OK: A -> res A
| Error: errmsg -> res A.

Arguments Error [A].



Definition bind (A B: Type) (f: res A) (g: A -> res B) : res B :=
match f with
| OK x => g x
| Error msg => Error msg
end.

Definition bind2 (A B C: Type) (f: res (A * B)) (g: A -> B -> res C) : res C :=
match f with
| OK (x, y) => g x y
| Error msg => Error msg
end.



Notation "'do' X <- A ; B" := (bind A (fun X => B))
(at level 200, X ident, A at level 100, B at level 200)
: error_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
(at level 200, X ident, Y ident, A at level 100, B at level 200)
: error_monad_scope.

Remark bind_inversion:
forall (A B: Type) (f: res A) (g: A -> res B) (y: B),
bind f g = OK y ->
exists x, f = OK x /\ g x = OK y.
Proof. hammer_hook "Errors" "Errors.bind_inversion".
intros until y. destruct f; simpl; intros.
exists a; auto.
discriminate.
Qed.

Remark bind2_inversion:
forall (A B C: Type) (f: res (A*B)) (g: A -> B -> res C) (z: C),
bind2 f g = OK z ->
exists x, exists y, f = OK (x, y) /\ g x y = OK z.
Proof. hammer_hook "Errors" "Errors.bind2_inversion".
intros until z. destruct f; simpl.
destruct p; simpl; intros. exists a; exists b; auto.
intros; discriminate.
Qed.



Definition assertion_failed {A: Type} : res A := Error(msg "Assertion failed").

Notation "'assertion' A ; B" := (if A then B else assertion_failed)
(at level 200, A at level 100, B at level 200)
: error_monad_scope.



Local Open Scope error_monad_scope.

Fixpoint mmap (A B: Type) (f: A -> res B) (l: list A) {struct l} : res (list B) :=
match l with
| nil => OK nil
| hd :: tl => do hd' <- f hd; do tl' <- mmap f tl; OK (hd' :: tl')
end.

Remark mmap_inversion:
forall (A B: Type) (f: A -> res B) (l: list A) (l': list B),
mmap f l = OK l' ->
list_forall2 (fun x y => f x = OK y) l l'.
Proof. hammer_hook "Errors" "Errors.mmap_inversion".
induction l; simpl; intros.
inversion_clear H. constructor.
destruct (bind_inversion _ _ H) as [hd' [P Q]].
destruct (bind_inversion _ _ Q) as [tl' [R S]].
inversion_clear S.
constructor. auto. auto.
Qed.





Ltac monadInv1 H :=
match type of H with
| (OK _ = OK _) =>
inversion H; clear H; try subst
| (Error _ = OK _) =>
discriminate
| (bind ?F ?G = OK ?X) =>
let x := fresh "x" in (
let EQ1 := fresh "EQ" in (
let EQ2 := fresh "EQ" in (
destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
clear H;
try (monadInv1 EQ2))))
| (bind2 ?F ?G = OK ?X) =>
let x1 := fresh "x" in (
let x2 := fresh "x" in (
let EQ1 := fresh "EQ" in (
let EQ2 := fresh "EQ" in (
destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
clear H;
try (monadInv1 EQ2)))))
| (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
destruct X; [try (monadInv1 H) | discriminate]
| (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
destruct X as [] eqn:?; simpl negb in H; [discriminate | try (monadInv1 H)]
| (match ?X with true => _ | false => assertion_failed end = OK _) =>
destruct X as [] eqn:?; [try (monadInv1 H) | discriminate]
| (mmap ?F ?L = OK ?M) =>
generalize (mmap_inversion F L H); intro
end.

Ltac monadInv H :=
monadInv1 H ||
match type of H with
| (?F _ _ _ _ _ _ _ _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
| (?F _ _ _ _ _ _ _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
| (?F _ _ _ _ _ _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
| (?F _ _ _ _ _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
| (?F _ _ _ _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
| (?F _ _ _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
| (?F _ _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
| (?F _ = OK _) =>
((progress simpl in H) || unfold F in H); monadInv1 H
end.
