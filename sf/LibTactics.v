From Hammer Require Import Hammer.











Set Implicit Arguments.

Require Import List.



Remove Hints Bool.trans_eq_bool.







Ltac idcont tt :=
idtac.






Inductive Boxer : Type :=
| boxer : forall (A:Type), A -> Boxer.






Inductive ltac_No_arg : Set :=
| ltac_no_arg : ltac_No_arg.






Inductive ltac_Wild : Set :=
| ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.



Inductive ltac_Wilds : Set :=
| ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.






Inductive ltac_Mark : Type :=
| ltac_mark : ltac_Mark.



Ltac gen_until_mark :=
match goal with H: ?T |- _ =>
match T with
| ltac_Mark => clear H
| _ => generalize H; clear H; gen_until_mark
end end.



Ltac gen_until_mark_with_processing cont :=
match goal with H: ?T |- _ =>
match T with
| ltac_Mark => clear H
| _ => cont H; generalize H; clear H;
gen_until_mark_with_processing cont
end end.



Ltac intro_until_mark :=
match goal with
| |- (ltac_Mark -> _) => intros _
| _ => intro; intro_until_mark
end.






Notation "'>>'" :=
(@nil Boxer)
(at level 0)
: ltac_scope.
Notation "'>>' v1" :=
((boxer v1)::nil)
(at level 0, v1 at level 0)
: ltac_scope.
Notation "'>>' v1 v2" :=
((boxer v1)::(boxer v2)::nil)
(at level 0, v1 at level 0, v2 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3" :=
((boxer v1)::(boxer v2)::(boxer v3)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::(boxer v7)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::(boxer v7)::(boxer v8)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
v8 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
v8 at level 0, v9 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
v8 at level 0, v9 at level 0, v10 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
::(boxer v11)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
::(boxer v11)::(boxer v12)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
v12 at level 0)
: ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
::(boxer v11)::(boxer v12)::(boxer v13)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
v12 at level 0, v13 at level 0)
: ltac_scope.



Ltac list_boxer_of E :=
match type of E with
| List.list Boxer => constr:(E)
| _ => constr:((boxer E)::nil)
end.






Inductive Ltac_database_token : Prop := ltac_database_token.

Definition ltac_database (D:Boxer) (T:Boxer) (A:Boxer) := Ltac_database_token.

Notation "'Register' D T" := (ltac_database (boxer D) (boxer T) _)
(at level 69, D at level 0, T at level 0).

Lemma ltac_database_provide : forall (A:Boxer) (D:Boxer) (T:Boxer),
ltac_database D T A.
Proof using. hammer_hook "LibTactics" "LibTactics.ltac_database_provide". split. Qed.

Ltac Provide T := apply (@ltac_database_provide (boxer T)).

Ltac ltac_database_get D T :=
let A := fresh "TEMP" in evar (A:Boxer);
let H := fresh "TEMP" in
assert (H : ltac_database (boxer D) (boxer T) A);
[ subst A; auto
| subst A; match type of H with ltac_database _ _ (boxer ?L) =>
generalize L end; clear H ].








Definition rm (A:Type) (X:A) := X.



Ltac rm_term E :=
let T := type of E in
match goal with H: T |- _ => try clear H end.



Ltac rm_inside E :=
let go E := rm_inside E in
match E with
| rm ?X => rm_term X
| ?X1 ?X2 =>
go X1; go X2
| ?X1 ?X2 ?X3 =>
go X1; go X2; go X3
| ?X1 ?X2 ?X3 ?X4 =>
go X1; go X2; go X3; go X4
| ?X1 ?X2 ?X3 ?X4 ?X5 =>
go X1; go X2; go X3; go X4; go X5
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 =>
go X1; go X2; go X3; go X4; go X5; go X6
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 =>
go X1; go X2; go X3; go X4; go X5; go X6; go X7
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 =>
go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 =>
go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 ?X10 =>
go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9; go X10
| _ => idtac
end.



Ltac fast_rm_inside E :=
rm_inside E.






Require BinPos Coq.ZArith.BinInt.

Require Coq.Numbers.BinNums Coq.ZArith.BinInt.

Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
match x with
| BinInt.Z0 => 0%nat
| BinInt.Zpos p => BinPos.nat_of_P p
| BinInt.Zneg p => 0%nat
end.

Ltac number_to_nat N :=
match type of N with
| nat => constr:(N)
| BinInt.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
end.



Tactic Notation "ltac_pattern" constr(E) "at" constr(K) :=
match number_to_nat K with
| 1 => pattern E at 1
| 2 => pattern E at 2
| 3 => pattern E at 3
| 4 => pattern E at 4
| 5 => pattern E at 5
| 6 => pattern E at 6
| 7 => pattern E at 7
| 8 => pattern E at 8
| _ => fail "ltac_pattern: arity not supported"
end.

Tactic Notation "ltac_pattern" constr(E) "at" constr(K) "in" hyp(H) :=
match number_to_nat K with
| 1 => pattern E at 1 in H
| 2 => pattern E at 2 in H
| 3 => pattern E at 3 in H
| 4 => pattern E at 4 in H
| 5 => pattern E at 5 in H
| 6 => pattern E at 6 in H
| 7 => pattern E at 7 in H
| 8 => pattern E at 8 in H
| _ => fail "ltac_pattern: arity not supported"
end.



Tactic Notation "ltac_set" "(" ident(X) ":=" constr(E) ")" "at" constr(K) :=
match number_to_nat K with
| 1%nat => set (X := E) at 1
| 2%nat => set (X := E) at 2
| 3%nat => set (X := E) at 3
| 4%nat => set (X := E) at 4
| 5%nat => set (X := E) at 5
| 6%nat => set (X := E) at 6
| 7%nat => set (X := E) at 7
| 8%nat => set (X := E) at 8
| 9%nat => set (X := E) at 9
| 10%nat => set (X := E) at 10
| 11%nat => set (X := E) at 11
| 12%nat => set (X := E) at 12
| 13%nat => set (X := E) at 13
| _ => fail "ltac_set: arity not supported"
end.






Tactic Notation "show" tactic(tac) :=
let R := tac in pose R.



Lemma dup_lemma : forall P, P -> P -> P.
Proof using. hammer_hook "LibTactics" "LibTactics.dup_lemma". auto. Qed.

Ltac dup_tactic N :=
match number_to_nat N with
| 0 => idtac
| S 0 => idtac
| S ?N' => apply dup_lemma; [ | dup_tactic N' ]
end.

Tactic Notation "dup" constr(N) :=
dup_tactic N.
Tactic Notation "dup" :=
dup 2.






Ltac is_not_evar E :=
first [ is_evar E; fail 1
| idtac ].



Ltac is_evar_as_bool E :=
constr:(ltac:(first
[ is_evar E; exact true
| exact false ])).




Ltac check_noevar M :=
first [ has_evar M; fail 2 | idtac ].

Ltac check_noevar_hyp H :=
let T := type of H in check_noevar T.

Ltac check_noevar_goal :=
match goal with |- ?G => check_noevar G end.






Ltac with_evar_base T cont :=
let x := fresh "TEMP" in evar (x:T); cont x; subst x.

Tactic Notation "with_evar" constr(T) tactic(cont) :=
with_evar_base T cont.






Ltac get_last_hyp tt :=
match goal with H: _ |- _ => constr:(H) end.






Definition ltac_tag_subst (A:Type) (x:A) := x.



Definition ltac_to_generalize (A:Type) (x:A) := x.

Ltac gen_to_generalize :=
repeat match goal with
H: ltac_to_generalize _ |- _ => generalize H; clear H end.

Ltac mark_to_generalize H :=
let T := type of H in
change T with (ltac_to_generalize T) in H.






Ltac get_head E :=
match E with
| ?P _ _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ _ _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ _ => constr:(P)
| ?P _ _ _ _ => constr:(P)
| ?P _ _ _ => constr:(P)
| ?P _ _ => constr:(P)
| ?P _ => constr:(P)
| ?P => constr:(P)
end.



Ltac get_fun_arg E :=
match E with
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X => constr:((X1 X2 X3 X4 X5 X6 X7,X))
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X => constr:((X1 X2 X3 X4 X5 X6,X))
| ?X1 ?X2 ?X3 ?X4 ?X5 ?X => constr:((X1 X2 X3 X4 X5,X))
| ?X1 ?X2 ?X3 ?X4 ?X => constr:((X1 X2 X3 X4,X))
| ?X1 ?X2 ?X3 ?X => constr:((X1 X2 X3,X))
| ?X1 ?X2 ?X => constr:((X1 X2,X))
| ?X1 ?X => constr:((X1,X))
end.






Tactic Notation "ltac_action_at" constr(K) "of" constr(E) "do" tactic(Tac) :=
let p := fresh "TEMP" in ltac_pattern E at K;
match goal with |- ?P _ => set (p:=P) end;
Tac; unfold p; clear p.

Tactic Notation "ltac_action_at" constr(K) "of" constr(E) "in" hyp(H) "do" tactic(Tac) :=
let p := fresh "TEMP" in ltac_pattern E at K in H;
match type of H with ?P _ => set (p:=P) in H end;
Tac; unfold p in H; clear p.



Tactic Notation "protects" constr(E) "do" tactic(Tac) :=

let x := fresh "TEMP" in let H := fresh "TEMP" in
set (X := E) in *; assert (H : X = E) by reflexivity;
clearbody X; Tac; subst x.

Tactic Notation "protects" constr(E) "do" tactic(Tac) "/" :=
protects E do Tac.






Definition eq' := @eq.

Hint Unfold eq'.

Notation "x '='' y" := (@eq' _ x y)
(at level 70, y at next level).




Ltac jauto_set_hyps :=
repeat match goal with H: ?T |- _ =>
match T with
| _ /\ _ => destruct H
| exists a, _ => destruct H
| _ => generalize H; clear H
end
end.

Ltac jauto_set_goal :=
repeat match goal with
| |- exists a, _ => esplit
| |- _ /\ _ => split
end.

Ltac jauto_set :=
intros; jauto_set_hyps;
intros; jauto_set_goal;
unfold not in *.








Ltac old_refine f :=
refine f.



Tactic Notation "rapply" constr(t) :=
first
[ eexact (@t)
| old_refine (@t)
| old_refine (@t _)
| old_refine (@t _ _)
| old_refine (@t _ _ _)
| old_refine (@t _ _ _ _)
| old_refine (@t _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _ _)
| old_refine (@t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
].



Tactic Notation "rapply_0" constr(t) :=
old_refine (@t).
Tactic Notation "rapply_1" constr(t) :=
old_refine (@t _).
Tactic Notation "rapply_2" constr(t) :=
old_refine (@t _ _).
Tactic Notation "rapply_3" constr(t) :=
old_refine (@t _ _ _).
Tactic Notation "rapply_4" constr(t) :=
old_refine (@t _ _ _ _).
Tactic Notation "rapply_5" constr(t) :=
old_refine (@t _ _ _ _ _).
Tactic Notation "rapply_6" constr(t) :=
old_refine (@t _ _ _ _ _ _).
Tactic Notation "rapply_7" constr(t) :=
old_refine (@t _ _ _ _ _ _ _).
Tactic Notation "rapply_8" constr(t) :=
old_refine (@t _ _ _ _ _ _ _ _).
Tactic Notation "rapply_9" constr(t) :=
old_refine (@t _ _ _ _ _ _ _ _ _).
Tactic Notation "rapply_10" constr(t) :=
old_refine (@t _ _ _ _ _ _ _ _ _ _).



Ltac lets_base I E := generalize E; intros I.



Tactic Notation "applys_to" hyp(H) constr(E) :=
let H' := fresh "TEMP" in rename H into H';
(first [ lets_base H (E H')
| lets_base H (E _ H')
| lets_base H (E _ _ H')
| lets_base H (E _ _ _ H')
| lets_base H (E _ _ _ _ H')
| lets_base H (E _ _ _ _ _ H')
| lets_base H (E _ _ _ _ _ _ H')
| lets_base H (E _ _ _ _ _ _ _ H')
| lets_base H (E _ _ _ _ _ _ _ _ H')
| lets_base H (E _ _ _ _ _ _ _ _ _ H') ]
); clear H'.



Tactic Notation "applys_to" hyp(H1) "," hyp(H2) constr(E) :=
applys_to H1 E; applys_to H2 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) constr(E) :=
applys_to H1 E; applys_to H2 E; applys_to H3 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) constr(E) :=
applys_to H1 E; applys_to H2 E; applys_to H3 E; applys_to H4 E.



Tactic Notation "constructors" :=
first [ constructor | econstructor ]; unfold eq'.






Tactic Notation "asserts" simple_intropattern(I) ":" constr(T) :=
let H := fresh "TEMP" in assert (H : T);
[ | generalize H; clear H; intros I ].



Tactic Notation "asserts" simple_intropattern(I1)
simple_intropattern(I2) ":" constr(T) :=
asserts [I1 I2]: T.
Tactic Notation "asserts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) ":" constr(T) :=
asserts [I1 [I2 I3]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3)
simple_intropattern(I4) ":" constr(T) :=
asserts [I1 [I2 [I3 I4]]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3)
simple_intropattern(I4) simple_intropattern(I5) ":" constr(T) :=
asserts [I1 [I2 [I3 [I4 I5]]]]: T.
Tactic Notation "asserts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3)
simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) ":" constr(T) :=
asserts [I1 [I2 [I3 [I4 [I5 I6]]]]]: T.



Tactic Notation "asserts" ":" constr(T) :=
let H := fresh "TEMP" in asserts H : T.



Tactic Notation "cuts" simple_intropattern(I) ":" constr(T) :=
cut (T); [ intros I | idtac ].



Tactic Notation "cuts" ":" constr(T) :=
let H := fresh "TEMP" in cuts H: T.



Tactic Notation "cuts" simple_intropattern(I1)
simple_intropattern(I2) ":" constr(T) :=
cuts [I1 I2]: T.
Tactic Notation "cuts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) ":" constr(T) :=
cuts [I1 [I2 I3]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3)
simple_intropattern(I4) ":" constr(T) :=
cuts [I1 [I2 [I3 I4]]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3)
simple_intropattern(I4) simple_intropattern(I5) ":" constr(T) :=
cuts [I1 [I2 [I3 [I4 I5]]]]: T.
Tactic Notation "cuts" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3)
simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) ":" constr(T) :=
cuts [I1 [I2 [I3 [I4 [I5 I6]]]]]: T.








Ltac app_assert t P cont :=
let H := fresh "TEMP" in
assert (H : P); [ | cont(t H); clear H ].

Ltac app_evar t A cont :=
let x := fresh "TEMP" in
evar (x:A);
let t' := constr:(t x) in
let t'' := (eval unfold x in t') in
subst x; cont t''.

Ltac app_arg t P v cont :=
let H := fresh "TEMP" in
assert (H : P); [ apply v | cont(t H); try clear H ].

Ltac build_app_alls t final :=
let rec go t :=
match type of t with
| ?P -> ?Q => app_assert t P go
| forall _:?A, _ => app_evar t A go
| _ => final t
end in
go t.

Ltac boxerlist_next_type vs :=
match vs with
| nil => constr:(ltac_wild)
| (boxer ltac_wild)::?vs' => boxerlist_next_type vs'
| (boxer ltac_wilds)::_ => constr:(ltac_wild)
| (@boxer ?T _)::_ => constr:(T)
end.



Ltac build_app_hnts t vs final :=
let rec go t vs :=
match vs with
| nil => first [ final t | fail 1 ]
| (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
| (boxer ?v)::?vs' =>
let cont t' := go t' vs in
let cont' t' := go t' vs' in
let T := type of t in
let T := eval hnf in T in
match v with
| ltac_wild =>
first [ let U := boxerlist_next_type vs' in
match U with
| ltac_wild =>
match T with
| ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
| forall _:?A, _ => first [ app_evar t A cont' | fail 3 ]
end
| _ =>
match T with
| U -> ?Q => first [ app_assert t U cont' | fail 3 ]
| forall _:U, _ => first [ app_evar t U cont' | fail 3 ]
| ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
| forall _:?A, _ => first [ app_evar t A cont | fail 3 ]
end
end
| fail 2 ]
| _ =>
match T with
| ?P -> ?Q => first [ app_arg t P v cont'
| app_assert t P cont
| fail 3 ]
| forall _:Type, _ =>
match type of v with
| Type => first [ cont' (t v)
| app_evar t Type cont
| fail 3 ]
| _ => first [ app_evar t Type cont
| fail 3 ]
end
| forall _:?A, _ =>
let V := type of v in
match type of V with
| Prop =>  first [ app_evar t A cont
| fail 3 ]
| _ => first [ cont' (t v)
| app_evar t A cont
| fail 3 ]
end
end
end
end in
go t vs.



Ltac app_typeclass t cont :=
let t' := constr:(t _) in
cont t'.

Ltac build_app_alls t final ::=
let rec go t :=
match type of t with
| ?P -> ?Q => app_assert t P go
| forall _:?A, _ =>
first [ app_evar t A go
| app_typeclass t go
| fail 3 ]
| _ => final t
end in
go t.

Ltac build_app_hnts t vs final ::=
let rec go t vs :=
match vs with
| nil => first [ final t | fail 1 ]
| (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
| (boxer ?v)::?vs' =>
let cont t' := go t' vs in
let cont' t' := go t' vs' in
let T := type of t in
let T := eval hnf in T in
match v with
| ltac_wild =>
first [ let U := boxerlist_next_type vs' in
match U with
| ltac_wild =>
match T with
| ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
| forall _:?A, _ => first [ app_typeclass t cont'
| app_evar t A cont'
| fail 3 ]
end
| _ =>
match T with
| U -> ?Q => first [ app_assert t U cont' | fail 3 ]
| forall _:U, _ => first
[ app_typeclass t cont'
| app_evar t U cont'
| fail 3 ]
| ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
| forall _:?A, _ => first
[ app_typeclass t cont
| app_evar t A cont
| fail 3 ]
end
end
| fail 2 ]
| _ =>
match T with
| ?P -> ?Q => first [ app_arg t P v cont'
| app_assert t P cont
| fail 3 ]
| forall _:Type, _ =>
match type of v with
| Type => first [ cont' (t v)
| app_evar t Type cont
| fail 3 ]
| _ => first [ app_evar t Type cont
| fail 3 ]
end
| forall _:?A, _ =>
let V := type of v in
match type of V with
| Prop => first [ app_typeclass t cont
| app_evar t A cont
| fail 3 ]
| _ => first [ cont' (t v)
| app_typeclass t cont
| app_evar t A cont
| fail 3 ]
end
end
end
end in
go t vs.




Ltac build_app args final :=
first [
match args with (@boxer ?T ?t)::?vs =>
let t := constr:(t:T) in
build_app_hnts t vs final;
fast_rm_inside args
end
| fail 1 "Instantiation fails for:" args].

Ltac unfold_head_until_product T :=
eval hnf in T.

Ltac args_unfold_head_if_not_product args :=
match args with (@boxer ?T ?t)::?vs =>
let T' := unfold_head_until_product T in
constr:((@boxer T' t)::vs)
end.

Ltac args_unfold_head_if_not_product_but_params args :=
match args with
| (boxer ?t)::(boxer ?v)::?vs =>
args_unfold_head_if_not_product args
| _ => constr:(args)
end.



Ltac lets_build I Ei :=
let args := list_boxer_of Ei in
let args := args_unfold_head_if_not_product_but_params args in

build_app args ltac:(fun R => lets_base I R).

Tactic Notation "lets" simple_intropattern(I) ":" constr(E) :=
lets_build I E.
Tactic Notation "lets" ":" constr(E) :=
let H := fresh in lets H: E.
Tactic Notation "lets" ":" constr(E0)
constr(A1) :=
lets: (>> E0 A1).
Tactic Notation "lets" ":" constr(E0)
constr(A1) constr(A2) :=
lets: (>> E0 A1 A2).
Tactic Notation "lets" ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
lets: (>> E0 A1 A2 A3).
Tactic Notation "lets" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
lets: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
lets: (>> E0 A1 A2 A3 A4 A5).


Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
":" constr(E) :=
lets [I1 I2]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) ":" constr(E) :=
lets [I1 [I2 I3]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
lets [I1 [I2 [I3 I4]]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
":" constr(E) :=
lets [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
constr(A1) :=
lets I: (>> E0 A1).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) :=
lets I: (>> E0 A1 A2).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
lets I: (>> E0 A1 A2 A3).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
lets I: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
lets I: (>> E0 A1 A2 A3 A4 A5).

Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
constr(A1) :=
lets [I1 I2]: E0 A1.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
constr(A1) constr(A2) :=
lets [I1 I2]: E0 A1 A2.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
lets [I1 I2]: E0 A1 A2 A3.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
lets [I1 I2]: E0 A1 A2 A3 A4.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
lets [I1 I2]: E0 A1 A2 A3 A4 A5.



Ltac forwards_build_app_arg Ei :=
let args := list_boxer_of Ei in
let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
let args := args_unfold_head_if_not_product args in
args.

Ltac forwards_then Ei cont :=
let args := forwards_build_app_arg Ei in
let args := args_unfold_head_if_not_product_but_params args in
build_app args cont.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(Ei) :=
let args := forwards_build_app_arg Ei in
lets I: args.

Tactic Notation "forwards" ":" constr(E) :=
let H := fresh in forwards H: E.
Tactic Notation "forwards" ":" constr(E0)
constr(A1) :=
forwards: (>> E0 A1).
Tactic Notation "forwards" ":" constr(E0)
constr(A1) constr(A2) :=
forwards: (>> E0 A1 A2).
Tactic Notation "forwards" ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
forwards: (>> E0 A1 A2 A3).
Tactic Notation "forwards" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
forwards: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
forwards: (>> E0 A1 A2 A3 A4 A5).


Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
":" constr(E) :=
forwards [I1 I2]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) ":" constr(E) :=
forwards [I1 [I2 I3]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
forwards [I1 [I2 [I3 I4]]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
":" constr(E) :=
forwards [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
constr(A1) :=
forwards I: (>> E0 A1).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) :=
forwards I: (>> E0 A1 A2).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
forwards I: (>> E0 A1 A2 A3).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
forwards I: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
forwards I: (>> E0 A1 A2 A3 A4 A5).



Tactic Notation "forwards_nounfold" simple_intropattern(I) ":" constr(Ei) :=
let args := list_boxer_of Ei in
let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
build_app args ltac:(fun R => lets_base I R).



Ltac forwards_nounfold_then Ei cont :=
let args := list_boxer_of Ei in
let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
build_app args cont.



Ltac applys_build Ei :=
let args := list_boxer_of Ei in
let args := args_unfold_head_if_not_product_but_params args in
build_app args ltac:(fun R =>
first [ apply R | eapply R | rapply R ]).

Ltac applys_base E :=
match type of E with
| list Boxer => applys_build E
| _ => first [ rapply E | applys_build E ]
end; fast_rm_inside E.

Tactic Notation "applys" constr(E) :=
applys_base E.
Tactic Notation "applys" constr(E0) constr(A1) :=
applys (>> E0 A1).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) :=
applys (>> E0 A1 A2).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) :=
applys (>> E0 A1 A2 A3).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
applys (>> E0 A1 A2 A3 A4).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
applys (>> E0 A1 A2 A3 A4 A5).



Ltac fapplys_build Ei :=
let args := list_boxer_of Ei in
let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
let args := args_unfold_head_if_not_product_but_params args in
build_app args ltac:(fun R => apply R).

Tactic Notation "fapplys" constr(E0) :=
match type of E0 with
| list Boxer => fapplys_build E0
| _ => fapplys_build (>> E0)
end.
Tactic Notation "fapplys" constr(E0) constr(A1) :=
fapplys (>> E0 A1).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) :=
fapplys (>> E0 A1 A2).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) :=
fapplys (>> E0 A1 A2 A3).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
fapplys (>> E0 A1 A2 A3 A4).
Tactic Notation "fapplys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
fapplys (>> E0 A1 A2 A3 A4 A5).



Ltac specializes_build H Ei :=
let H' := fresh "TEMP" in rename H into H';
let args := list_boxer_of Ei in
let args := constr:((boxer H')::args) in
let args := args_unfold_head_if_not_product args in
build_app args ltac:(fun R => lets H: R);
clear H'.

Ltac specializes_base H Ei :=
specializes_build H Ei; fast_rm_inside Ei.

Tactic Notation "specializes" hyp(H) :=
specializes_base H (___).
Tactic Notation "specializes" hyp(H) constr(A) :=
specializes_base H A.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
specializes H (>> A1 A2).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
specializes H (>> A1 A2 A3).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
specializes H (>> A1 A2 A3 A4).
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
specializes H (>> A1 A2 A3 A4 A5).



Ltac specializes_var_base H :=
match type of H with
| ?P -> ?Q => fail 1
| forall _:_, _ => specializes H __
end.

Ltac specializes_vars_base H :=
repeat (specializes_var_base H).

Tactic Notation "specializes_var" hyp(H) :=
specializes_var_base H.

Tactic Notation "specializes_vars" hyp(H) :=
specializes_vars_base H.






Tactic Notation "fapply" constr(E) :=
let H := fresh "TEMP" in forwards H: E;
first [ apply H | eapply H | rapply H | hnf; apply H
| hnf; eapply H | applys H ].




Tactic Notation "sapply" constr(H) :=
first [ apply H | eapply H | rapply H | applys H
| hnf; apply H | hnf; eapply H | hnf; applys H
| fapply H ].






Tactic Notation "lets_simpl" ident(H) ":" constr(E) :=
lets H: E; try simpl in H.

Tactic Notation "lets_simpl" ":" constr(T) :=
let H := fresh "TEMP" in lets_simpl H: T.



Tactic Notation "lets_hnf" ident(H) ":" constr(E) :=
lets H: E; hnf in H.

Tactic Notation "lets_hnf" ":" constr(T) :=
let H := fresh "TEMP" in lets_hnf H: T.



Tactic Notation "puts" ident(X) ":" constr(E) :=
pose (X := E).
Tactic Notation "puts" ":" constr(E) :=
let X := fresh "X" in pose (X := E).






Ltac logic_base E cont :=
assert (H:E); [ cont tt | eapply H; clear H ].

Tactic Notation "logic" constr(E) :=
logic_base E ltac:(fun _ => tauto).






Section equatesLemma.
Variables (A0 A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma equates_0 : forall (P Q:Prop),
P -> P = Q -> Q.
Proof. hammer_hook "LibTactics" "LibTactics.equates_0". intros. subst. auto. Qed.

Lemma equates_1 :
forall (P:A0->Prop) x1 y1,
P y1 -> x1 = y1 -> P x1.
Proof. hammer_hook "LibTactics" "LibTactics.equates_1". intros. subst. auto. Qed.

Lemma equates_2 :
forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
P y1 x2 -> x1 = y1 -> P x1 x2.
Proof. hammer_hook "LibTactics" "LibTactics.equates_2". intros. subst. auto. Qed.

Lemma equates_3 :
forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof. hammer_hook "LibTactics" "LibTactics.equates_3". intros. subst. auto. Qed.

Lemma equates_4 :
forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof. hammer_hook "LibTactics" "LibTactics.equates_4". intros. subst. auto. Qed.

Lemma equates_5 :
forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.
Proof. hammer_hook "LibTactics" "LibTactics.equates_5". intros. subst. auto. Qed.

Lemma equates_6 :
forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop)
x1 x2 x3 x4 x5 x6,
P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.
Proof. hammer_hook "LibTactics" "LibTactics.equates_6". intros. subst. auto. Qed.

End equatesLemma.

Ltac equates_lemma n :=
match number_to_nat n with
| 0 => constr:(equates_0)
| 1 => constr:(equates_1)
| 2 => constr:(equates_2)
| 3 => constr:(equates_3)
| 4 => constr:(equates_4)
| 5 => constr:(equates_5)
| 6 => constr:(equates_6)
end.

Ltac equates_one n :=
let L := equates_lemma n in
eapply L.

Ltac equates_several E cont :=
let all_pos := match type of E with
| List.list Boxer => constr:(E)
| _ => constr:((boxer E)::nil)
end in
let rec go pos :=
match pos with
| nil => cont tt
| (boxer ?n)::?pos' => equates_one n; [ instantiate; go pos' | ]
end in
go all_pos.

Tactic Notation "equates" constr(E) :=
equates_several E ltac:(fun _ => idtac).
Tactic Notation "equates" constr(n1) constr(n2) :=
equates (>> n1 n2).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) :=
equates (>> n1 n2 n3).
Tactic Notation "equates" constr(n1) constr(n2) constr(n3) constr(n4) :=
equates (>> n1 n2 n3 n4).



Tactic Notation "applys_eq" constr(H) constr(E) :=
equates_several E ltac:(fun _ => sapply H).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) :=
applys_eq H (>> n1 n2).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) :=
applys_eq H (>> n1 n2 n3).
Tactic Notation "applys_eq" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
applys_eq H (>> n1 n2 n3 n4).






Tactic Notation "false_goal" :=
elimtype False.



Ltac false_post :=
solve [ assumption | discriminate | congruence ].



Tactic Notation "false" :=
false_goal; try false_post.



Tactic Notation "tryfalse" :=
try solve [ false ].



Ltac false_then E cont :=
false_goal; first
[ applys E; instantiate
| forwards_then E ltac:(fun M =>
pose M; jauto_set_hyps; intros; false) ];
cont tt.


Tactic Notation "false" constr(E) :=
false_then E ltac:(fun _ => idtac).
Tactic Notation "false" constr(E) constr(E1) :=
false (>> E E1).
Tactic Notation "false" constr(E) constr(E1) constr(E2) :=
false (>> E E1 E2).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) :=
false (>> E E1 E2 E3).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) constr(E4) :=
false (>> E E1 E2 E3 E4).



Ltac false_invert_for H :=
let M := fresh "TEMP" in pose (M := H); inversion H; false.

Tactic Notation "false_invert" constr(H) :=
try solve [ false_invert_for H | false ].



Ltac false_invert_iter :=
match goal with H:_ |- _ =>
solve [ inversion H; false
| clear H; false_invert_iter
| fail 2 ] end.

Tactic Notation "false_invert" :=
intros; solve [ false_invert_iter | false ].



Tactic Notation "tryfalse_invert" constr(H) :=
try (false_invert H).

Tactic Notation "tryfalse_invert" :=
try false_invert.



Ltac false_neq_self_hyp :=
match goal with H: ?x <> ?x |- _ =>
false_goal; apply H; reflexivity end.












Ltac introv_rec :=
match goal with
| |- ?P -> ?Q => idtac
| |- forall _, _ => intro; introv_rec
| |- _ => idtac
end.



Ltac introv_noarg :=
match goal with
| |- ?P -> ?Q => idtac
| |- forall _, _ => introv_rec
| |- ?G => hnf;
match goal with
| |- ?P -> ?Q => idtac
| |- forall _, _ => introv_rec
end
| |- _ => idtac
end.


Ltac introv_noarg_not_optimized :=
intro; match goal with H:_|-_ => revert H end; introv_rec.




Ltac introv_arg H :=
hnf; match goal with
| |- ?P -> ?Q => intros H
| |- forall _, _ => intro; introv_arg H
end.



Tactic Notation "introv" :=
introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) :=
introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) :=
introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) :=
introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) :=
introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
simple_intropattern(I9) :=
introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
simple_intropattern(I9) simple_intropattern(I10) :=
introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.



Tactic Notation "intros_all" :=
repeat intro.



Tactic Notation "intro_hnf" :=
intro; match goal with H: _ |- _ => hnf in H end.






Ltac ltac_intros_post := idtac.

Tactic Notation "=>" :=
intros.
Tactic Notation "=>" simple_intropattern(I1) :=
intros I1.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2) :=
intros I1 I2.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) :=
intros I1 I2 I3.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) :=
intros I1 I2 I3 I4.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
intros I1 I2 I3 I4 I5.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) :=
intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) :=
intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
simple_intropattern(I9) :=
intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
simple_intropattern(I9) simple_intropattern(I10) :=
intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.




Ltac intro_nondeps_aux_special_intro G :=
fail.

Ltac intro_nondeps_aux is_already_hnf :=
match goal with
| |- (?P -> ?Q) => idtac
| |- ?G -> _ => intro_nondeps_aux_special_intro G;
intro; intro_nondeps_aux true
| |- (forall _,_) => intros ?; intro_nondeps_aux true
| |- _ =>
match is_already_hnf with
| true => idtac
| false => hnf; intro_nondeps_aux true
end
end.

Ltac intro_nondeps tt := intro_nondeps_aux false.

Tactic Notation "=>>" :=
intro_nondeps tt.
Tactic Notation "=>>" simple_intropattern(I1) :=
=>>; intros I1.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2) :=
=>>; intros I1 I2.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) :=
=>>; intros I1 I2 I3.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) :=
=>>; intros I1 I2 I3 I4.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
=>>; intros I1 I2 I3 I4 I5.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) :=
=>>; intros I1 I2 I3 I4 I5 I6.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) :=
=>>; intros I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
=>>; intros I1 I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
simple_intropattern(I9) :=
=>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
simple_intropattern(I9) simple_intropattern(I10) :=
=>>; intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.







Tactic Notation "gen" ident(X1) :=
generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4)  :=
gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
ident(X6) :=
gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
ident(X6) ident(X7) :=
gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
ident(X6) ident(X7) ident(X8) :=
gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
ident(X6) ident(X7) ident(X8) ident(X9) :=
gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5)
ident(X6) ident(X7) ident(X8) ident(X9) ident(X10) :=
gen X10; gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.



Tactic Notation "generalizes" hyp(X) :=
generalize X; clear X.
Tactic Notation "generalizes" hyp(X1) hyp(X2) :=
generalizes X1; generalizes X2.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) :=
generalizes X1 X2; generalizes X3.
Tactic Notation "generalizes" hyp(X1) hyp(X2) hyp(X3) hyp(X4) :=
generalizes X1 X2 X3; generalizes X4.






Tactic Notation "sets" ident(X) ":" constr(E) :=
set (X := E) in *.



Ltac def_to_eq X HX E :=
assert (HX : X = E) by reflexivity; clearbody X.
Ltac def_to_eq_sym X HX E :=
assert (HX : E = X) by reflexivity; clearbody X.



Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) :=
set (X := E); def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) :=
let HX := fresh "EQ" X in set_eq X HX: E.
Tactic Notation "set_eq" ":" constr(E) :=
let X := fresh "X" in set_eq X: E.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) :=
set (X := E); def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) :=
let HX := fresh "EQ" X in set_eq <- X HX: E.
Tactic Notation "set_eq" "<-" ":" constr(E) :=
let X := fresh "X" in set_eq <- X: E.

Tactic Notation "sets_eq" ident(X) ident(HX) ":" constr(E) :=
set (X := E) in *; def_to_eq X HX E.
Tactic Notation "sets_eq" ident(X) ":" constr(E) :=
let HX := fresh "EQ" X in sets_eq X HX: E.
Tactic Notation "sets_eq" ":" constr(E) :=
let X := fresh "X" in sets_eq X: E.

Tactic Notation "sets_eq" "<-" ident(X) ident(HX) ":" constr(E) :=
set (X := E) in *; def_to_eq_sym X HX E.
Tactic Notation "sets_eq" "<-" ident(X) ":" constr(E) :=
let HX := fresh "EQ" X in sets_eq <- X HX: E.
Tactic Notation "sets_eq" "<-" ":" constr(E) :=
let X := fresh "X" in sets_eq <- X: E.

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) "in" hyp(H) :=
set (X := E) in H; def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) "in" hyp(H) :=
let HX := fresh "EQ" X in set_eq X HX: E in H.
Tactic Notation "set_eq" ":" constr(E) "in" hyp(H) :=
let X := fresh "X" in set_eq X: E in H.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) "in" hyp(H) :=
set (X := E) in H; def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) "in" hyp(H) :=
let HX := fresh "EQ" X in set_eq <- X HX: E in H.
Tactic Notation "set_eq" "<-" ":" constr(E) "in" hyp(H) :=
let X := fresh "X" in set_eq <- X: E in H.

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) "in" "|-" :=
set (X := E) in |-; def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) "in" "|-" :=
let HX := fresh "EQ" X in set_eq X HX: E in |-.
Tactic Notation "set_eq" ":" constr(E) "in" "|-" :=
let X := fresh "X" in set_eq X: E in |-.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) "in" "|-" :=
set (X := E) in |-; def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) "in" "|-" :=
let HX := fresh "EQ" X in set_eq <- X HX: E in |-.
Tactic Notation "set_eq" "<-" ":" constr(E) "in" "|-" :=
let X := fresh "X" in set_eq <- X: E in |-.



Tactic Notation "gen_eq" ident(X) ":" constr(E) :=
let EQ := fresh "EQ" X in sets_eq X EQ: E; revert EQ.
Tactic Notation "gen_eq" ":" constr(E) :=
let X := fresh "X" in gen_eq X: E.
Tactic Notation "gen_eq" ":" constr(E) "as" ident(X) :=
gen_eq X: E.
Tactic Notation "gen_eq" ident(X1) ":" constr(E1) ","
ident(X2) ":" constr(E2) :=
gen_eq X2: E2; gen_eq X1: E1.
Tactic Notation "gen_eq" ident(X1) ":" constr(E1) ","
ident(X2) ":" constr(E2) "," ident(X3) ":" constr(E3) :=
gen_eq X3: E3; gen_eq X2: E2; gen_eq X1: E1.



Ltac sets_let_base tac :=
match goal with
| |- context[let _ := ?E in _] => tac E; cbv zeta
| H: context[let _ := ?E in _] |- _ => tac E; cbv zeta in H
end.

Ltac sets_let_in_base H tac :=
match type of H with context[let _ := ?E in _] =>
tac E; cbv zeta in H end.

Tactic Notation "sets_let" ident(X) :=
sets_let_base ltac:(fun E => sets X: E).
Tactic Notation "sets_let" ident(X) "in" hyp(H) :=
sets_let_in_base H ltac:(fun E => sets X: E).
Tactic Notation "sets_eq_let" ident(X) :=
sets_let_base ltac:(fun E => sets_eq X: E).
Tactic Notation "sets_eq_let" ident(X) "in" hyp(H) :=
sets_let_in_base H ltac:(fun E => sets_eq X: E).






Ltac rewrites_base E cont :=
match type of E with
| List.list Boxer => forwards_then E cont
| _ => cont E; fast_rm_inside E
end.

Tactic Notation "rewrites" constr(E) :=
rewrites_base E ltac:(fun M => rewrite M ).
Tactic Notation "rewrites" constr(E) "in" hyp(H) :=
rewrites_base E ltac:(fun M => rewrite M in H).
Tactic Notation "rewrites" constr(E) "in" "*" :=
rewrites_base E ltac:(fun M => rewrite M in *).
Tactic Notation "rewrites" "<-" constr(E) :=
rewrites_base E ltac:(fun M => rewrite <- M ).
Tactic Notation "rewrites" "<-" constr(E) "in" hyp(H) :=
rewrites_base E ltac:(fun M => rewrite <- M in H).
Tactic Notation "rewrites" "<-" constr(E) "in" "*" :=
rewrites_base E ltac:(fun M => rewrite <- M in *).





Tactic Notation "rewrite_all" constr(E) :=
repeat rewrite E.
Tactic Notation "rewrite_all" "<-" constr(E) :=
repeat rewrite <- E.
Tactic Notation "rewrite_all" constr(E) "in" ident(H) :=
repeat rewrite E in H.
Tactic Notation "rewrite_all" "<-" constr(E) "in" ident(H) :=
repeat rewrite <- E in H.
Tactic Notation "rewrite_all" constr(E) "in" "*" :=
repeat rewrite E in *.
Tactic Notation "rewrite_all" "<-" constr(E) "in" "*" :=
repeat rewrite <- E in *.



Ltac asserts_rewrite_tactic E action :=
let EQ := fresh "TEMP" in (assert (EQ : E);
[ idtac | action EQ; clear EQ ]).

Tactic Notation "asserts_rewrite" constr(E) :=
asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ).
Tactic Notation "asserts_rewrite" "<-" constr(E) :=
asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ).
Tactic Notation "asserts_rewrite" constr(E) "in" hyp(H) :=
asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in H).
Tactic Notation "asserts_rewrite" "<-" constr(E) "in" hyp(H) :=
asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in H).
Tactic Notation "asserts_rewrite" constr(E) "in" "*" :=
asserts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in *).
Tactic Notation "asserts_rewrite" "<-" constr(E) "in" "*" :=
asserts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in *).



Ltac cuts_rewrite_tactic E action :=
let EQ := fresh "TEMP" in (cuts EQ: E;
[ action EQ; clear EQ | idtac ]).

Tactic Notation "cuts_rewrite" constr(E) :=
cuts_rewrite_tactic E ltac:(fun EQ => rewrite EQ).
Tactic Notation "cuts_rewrite" "<-" constr(E) :=
cuts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ).
Tactic Notation "cuts_rewrite" constr(E) "in" hyp(H) :=
cuts_rewrite_tactic E ltac:(fun EQ => rewrite EQ in H).
Tactic Notation "cuts_rewrite" "<-" constr(E) "in" hyp(H) :=
cuts_rewrite_tactic E ltac:(fun EQ => rewrite <- EQ in H).



Ltac rewrite_except H EQ :=
let K := fresh "TEMP" in let T := type of H in
set (K := T) in H;
rewrite EQ in *; unfold K in H; clear K.



Tactic Notation "rewrites" constr(E) "at" constr(K) :=
match type of E with ?T1 = ?T2 =>
ltac_action_at K of T1 do (rewrites E) end.
Tactic Notation "rewrites" "<-" constr(E) "at" constr(K) :=
match type of E with ?T1 = ?T2 =>
ltac_action_at K of T2 do (rewrites <- E) end.
Tactic Notation "rewrites" constr(E) "at" constr(K) "in" hyp(H) :=
match type of E with ?T1 = ?T2 =>
ltac_action_at K of T1 in H do (rewrites E in H) end.
Tactic Notation "rewrites" "<-" constr(E) "at" constr(K) "in" hyp(H) :=
match type of E with ?T1 = ?T2 =>
ltac_action_at K of T2 in H do (rewrites <- E in H) end.





Tactic Notation "replaces" constr(E) "with" constr(F) :=
let T := fresh "TEMP" in assert (T: E = F); [ | replace E with F; clear T ].

Tactic Notation "replaces" constr(E) "with" constr(F) "in" hyp(H) :=
let T := fresh "TEMP" in assert (T: E = F); [ | replace E with F in H; clear T ].



Tactic Notation "replaces" constr(E) "at" constr(K) "with" constr(F) :=
let T := fresh "TEMP" in assert (T: E = F); [ | rewrites T at K; clear T ].

Tactic Notation "replaces" constr(E) "at" constr(K) "with" constr(F) "in" hyp(H) :=
let T := fresh "TEMP" in assert (T: E = F); [ | rewrites T at K in H; clear T ].






Tactic Notation "changes" constr(E1) "with" constr(E2) "in" hyp(H) :=
asserts_rewrite (E1 = E2) in H; [ reflexivity | ].

Tactic Notation "changes" constr(E1) "with" constr(E2) :=
asserts_rewrite (E1 = E2); [ reflexivity | ].

Tactic Notation "changes" constr(E1) "with" constr(E2) "in" "*" :=
asserts_rewrite (E1 = E2) in *; [ reflexivity | ].







Tactic Notation "renames" ident(X1) "to" ident(Y1) :=
rename X1 into Y1.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
ident(X2) "to" ident(Y2) :=
renames X1 to Y1; renames X2 to Y2.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) :=
renames X1 to Y1; renames X2 to Y2, X3 to Y3.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
ident(X4) "to" ident(Y4) :=
renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) :=
renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5.
Tactic Notation "renames" ident(X1) "to" ident(Y1) ","
ident(X2) "to" ident(Y2) "," ident(X3) "to" ident(Y3) ","
ident(X4) "to" ident(Y4) "," ident(X5) "to" ident(Y5) ","
ident(X6) "to" ident(Y6) :=
renames X1 to Y1; renames X2 to Y2, X3 to Y3, X4 to Y4, X5 to Y5, X6 to Y6.






Ltac apply_to_head_of E cont :=
let go E :=
let P := get_head E in cont P in
match E with
| forall _,_ => intros; apply_to_head_of E cont
| ?A = ?B => first [ go A | go B ]
| ?A => go A
end.

Ltac unfolds_base :=
match goal with |- ?G =>
apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
unfolds_base.



Ltac unfolds_in_base H :=
match type of H with ?G =>
apply_to_head_of G ltac:(fun P => unfold P in H) end.

Tactic Notation "unfolds" "in" hyp(H) :=
unfolds_in_base H.



Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) :=
unfolds in H1; unfolds in H2.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) :=
unfolds in H1; unfolds in H2 H3.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
unfolds in H1; unfolds in H2 H3 H4.
Tactic Notation "unfolds" "in" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) :=
unfolds in H1; unfolds in H2 H3 H4 H5.



Tactic Notation "unfolds" constr(F1) :=
unfold F1 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2) :=
unfold F1,F2 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
"," constr(F3) :=
unfold F1,F2,F3 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
"," constr(F3) "," constr(F4) :=
unfold F1,F2,F3,F4 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
"," constr(F3) "," constr(F4) "," constr(F5) :=
unfold F1,F2,F3,F4,F5 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
"," constr(F3) "," constr(F4) "," constr(F5) "," constr(F6) :=
unfold F1,F2,F3,F4,F5,F6 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
"," constr(F3) "," constr(F4) "," constr(F5)
"," constr(F6) "," constr(F7) :=
unfold F1,F2,F3,F4,F5,F6,F7 in *.
Tactic Notation "unfolds" constr(F1) "," constr(F2)
"," constr(F3) "," constr(F4) "," constr(F5)
"," constr(F6) "," constr(F7) "," constr(F8) :=
unfold F1,F2,F3,F4,F5,F6,F7,F8 in *.



Tactic Notation "folds" constr(H) :=
fold H in *.
Tactic Notation "folds" constr(H1) "," constr(H2) :=
folds H1; folds H2.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3) :=
folds H1; folds H2; folds H3.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
"," constr(H4) :=
folds H1; folds H2; folds H3; folds H4.
Tactic Notation "folds" constr(H1) "," constr(H2) "," constr(H3)
"," constr(H4) "," constr(H5) :=
folds H1; folds H2; folds H3; folds H4; folds H5.






Tactic Notation "simpls" :=
simpl in *.



Tactic Notation "simpls" constr(F1) :=
simpl F1 in *.
Tactic Notation "simpls" constr(F1) "," constr(F2) :=
simpls F1; simpls F2.
Tactic Notation "simpls" constr(F1) "," constr(F2)
"," constr(F3) :=
simpls F1; simpls F2; simpls F3.
Tactic Notation "simpls" constr(F1) "," constr(F2)
"," constr(F3) "," constr(F4) :=
simpls F1; simpls F2; simpls F3; simpls F4.



Tactic Notation "unsimpl" constr(E) :=
let F := (eval simpl in E) in change F with E.



Tactic Notation "unsimpl" constr(E) "in" hyp(H) :=
let F := (eval simpl in E) in change F with E in H.



Tactic Notation "unsimpl" constr(E) "in" "*" :=
let F := (eval simpl in E) in change F with E in *.
Tactic Notation "unsimpls" constr(E) :=
unsimpl E in *.



Notation "'nosimpl' t" := (match tt with tt => t end)
(at level 10).




Tactic Notation "hnfs" := hnf in *.






Tactic Notation "substs" :=
repeat (match goal with H: ?x = ?y |- _ =>
first [ subst x | subst y ] end).



Ltac substs_below limit :=
match goal with H: ?T |- _ =>
match T with
| limit => idtac
| ?x = ?y =>
first [ subst x; substs_below limit
| subst y; substs_below limit
| generalizes H; substs_below limit; intro ]
end end.



Tactic Notation "substs" "below" "body" constr(M) :=
substs_below M.



Tactic Notation "substs" "below" hyp(H) :=
match type of H with ?M => substs below body M end.



Ltac intro_subst_hyp := fail.



Ltac subst_hyp_base H :=
match type of H with
| (_,_,_,_,_) = (_,_,_,_,_) => injection H; clear H; do 4 intro_subst_hyp
| (_,_,_,_) = (_,_,_,_) => injection H; clear H; do 4 intro_subst_hyp
| (_,_,_) = (_,_,_) => injection H; clear H; do 3 intro_subst_hyp
| (_,_) = (_,_) => injection H; clear H; do 2 intro_subst_hyp
| ?x = ?x => clear H
| ?x = ?y => first [ subst x | subst y ]
end.

Tactic Notation "subst_hyp" hyp(H) := subst_hyp_base H.

Ltac intro_subst_hyp ::=
let H := fresh "TEMP" in intros H; subst_hyp H.



Tactic Notation "intro_subst" :=
let H := fresh "TEMP" in intros H; subst_hyp H.



Ltac subst_local :=
repeat match goal with H:=_ |- _ => subst H end.



Ltac subst_eq_base E :=
let H := fresh "TEMP" in lets H: E; subst_hyp H.

Tactic Notation "subst_eq" constr(E) :=
subst_eq_base E.




Require Import ProofIrrelevance.



Ltac pi_rewrite_base E rewrite_tac :=
let E' := fresh "TEMP" in let T := type of E in evar (E':T);
rewrite_tac (@proof_irrelevance _ E E'); subst E'.

Tactic Notation "pi_rewrite" constr(E) :=
pi_rewrite_base E ltac:(fun X => rewrite X).
Tactic Notation "pi_rewrite" constr(E) "in" hyp(H) :=
pi_rewrite_base E ltac:(fun X => rewrite X in H).








Ltac fequal_base :=
let go := f_equal; [ fequal_base | ] in
match goal with
| |- (_,_,_) = (_,_,_) => go
| |- (_,_,_,_) = (_,_,_,_) => go
| |- (_,_,_,_,_) = (_,_,_,_,_) => go
| |- (_,_,_,_,_,_) = (_,_,_,_,_,_) => go
| |- _ => f_equal
end.

Tactic Notation "fequal" :=
fequal_base.



Ltac fequal_post :=
first [ reflexivity | congruence | apply proof_irrelevance | idtac ].

Tactic Notation "fequals" :=
fequal; fequal_post.



Tactic Notation "fequals_rec" :=
repeat (progress fequals).










Tactic Notation "invert" "keep" hyp(H) :=
pose ltac_mark; inversion H; gen_until_mark.



Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1) :=
invert keep H; introv I1.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) :=
invert keep H; introv I1 I2.
Tactic Notation "invert" "keep" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) :=
invert keep H; introv I1 I2 I3.



Tactic Notation "invert" hyp(H) :=
invert keep H; clear H.



Tactic Notation "invert_tactic" hyp(H) tactic(tac) :=
let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1) :=
invert_tactic H (fun H => invert keep H as I1).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) :=
invert_tactic H (fun H => invert keep H as I1 I2).
Tactic Notation "invert" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) :=
invert_tactic H (fun H => invert keep H as I1 I2 I3).








Axiom inj_pair2 :
forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
existT P p x = existT P p y -> x = y.


Ltac inverts_tactic H i1 i2 i3 i4 i5 i6 :=
let rec go i1 i2 i3 i4 i5 i6 :=
match goal with
| |- (ltac_Mark -> _) => intros _
| |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
first [ subst x | subst y ];
go i1 i2 i3 i4 i5 i6
| |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
let H := fresh "TEMP" in intro H;
generalize (@inj_pair2 _ P p x y H);
clear H; go i1 i2 i3 i4 i5 i6
| |- (?P -> ?Q) => i1; go i2 i3 i4 i5 i6 ltac:(intro)
| |- (forall _, _) => intro; go i1 i2 i3 i4 i5 i6
end in
generalize ltac_mark; invert keep H; go i1 i2 i3 i4 i5 i6;
unfold eq' in *.



Tactic Notation "inverts" "keep" hyp(H) :=
inverts_tactic H ltac:(intro) ltac:(intro) ltac:(intro)
ltac:(intro) ltac:(intro) ltac:(intro).



Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1) :=
inverts_tactic H ltac:(intros I1)
ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) :=
inverts_tactic H ltac:(intros I1) ltac:(intros I2)
ltac:(intro) ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) :=
inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
ltac:(intro) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
ltac:(intros I4) ltac:(intro) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
simple_intropattern(I5) :=
inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
ltac:(intros I4) ltac:(intros I5) ltac:(intro).
Tactic Notation "inverts" "keep" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
simple_intropattern(I5) simple_intropattern(I6) :=
inverts_tactic H ltac:(intros I1) ltac:(intros I2) ltac:(intros I3)
ltac:(intros I4) ltac:(intros I5) ltac:(intros I6).



Tactic Notation "inverts" hyp(H) :=
inverts keep H; try clear H.



Tactic Notation "inverts_tactic" hyp(H) tactic(tac) :=
let H' := fresh "TEMP" in rename H into H'; tac H'; clear H'.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1) :=
invert_tactic H (fun H => inverts keep H as I1).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) :=
invert_tactic H (fun H => inverts keep H as I1 I2).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) :=
invert_tactic H (fun H => inverts keep H as I1 I2 I3).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
simple_intropattern(I5) :=
invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5).
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
simple_intropattern(I5) simple_intropattern(I6) :=
invert_tactic H (fun H => inverts keep H as I1 I2 I3 I4 I5 I6).



Ltac inverts_as_tactic H :=
let rec go tt :=
match goal with
| |- (ltac_Mark -> _) => intros _
| |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
first [ subst x | subst y ];
go tt
| |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
let H := fresh "TEMP" in intro H;
generalize (@inj_pair2 _ P p x y H);
clear H; go tt
| |- (forall _, _) =>
intro; let H := get_last_hyp tt in mark_to_generalize H; go tt
end in
pose ltac_mark; inversion H;
generalize ltac_mark; gen_until_mark;
go tt; gen_to_generalize; unfolds ltac_to_generalize;
unfold eq' in *.

Tactic Notation "inverts" "keep" hyp(H) "as" :=
inverts_as_tactic H.

Tactic Notation "inverts" hyp(H) "as" :=
inverts_as_tactic H; clear H.

Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7) :=
inverts H as; introv I1 I2 I3 I4 I5 I6 I7.
Tactic Notation "inverts" hyp(H) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4)
simple_intropattern(I5) simple_intropattern(I6) simple_intropattern(I7)
simple_intropattern(I8) :=
inverts H as; introv I1 I2 I3 I4 I5 I6 I7 I8.



Ltac lets_inverts_base E cont :=
let H := fresh "TEMP" in lets H: E; try cont H.

Tactic Notation "lets_inverts" constr(E) :=
lets_inverts_base E ltac:(fun H => inverts H).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1) :=
lets_inverts_base E ltac:(fun H => inverts H as I1).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
simple_intropattern(I2) :=
lets_inverts_base E ltac:(fun H => inverts H as I1 I2).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) :=
lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3).
Tactic Notation "lets_inverts" constr(E) "as" simple_intropattern(I1)
simple_intropattern(I2) simple_intropattern(I3) simple_intropattern(I4) :=
lets_inverts_base E ltac:(fun H => inverts H as I1 I2 I3 I4).







Ltac injects_tactic H :=
let rec go _ :=
match goal with
| |- (ltac_Mark -> _) => intros _
| |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
first [ subst x | subst y | idtac ];
go tt
end in
generalize ltac_mark; injection H; go tt.



Tactic Notation "injects" "keep" hyp(H) :=
injects_tactic H.



Tactic Notation "injects" hyp(H) :=
injects_tactic H; clear H.



Tactic Notation "inject" hyp(H) :=
injection H.
Tactic Notation "inject" hyp(H) "as" ident(X1) :=
injection H; intros X1.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) :=
injection H; intros X1 X2.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3) :=
injection H; intros X1 X2 X3.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
ident(X4) :=
injection H; intros X1 X2 X3 X4.
Tactic Notation "inject" hyp(H) "as" ident(X1) ident(X2) ident(X3)
ident(X4) ident(X5) :=
injection H; intros X1 X2 X3 X4 X5.








Tactic Notation "inversions" "keep" hyp(H) :=
inversion H; subst.



Tactic Notation "inversions" hyp(H) :=
inversion H; subst; try clear H.



Tactic Notation "injections" "keep" hyp(H) :=
injection H; intros; subst.



Tactic Notation "injections" "keep" hyp(H) :=
injection H; clear H; intros; subst.






Tactic Notation "cases" constr(E) "as" ident(H) :=
let X := fresh "TEMP" in
set (X := E) in *; def_to_eq_sym X H E;
destruct X.

Tactic Notation "cases" constr(E) :=
let H := fresh "Eq" in cases E as H.



Ltac case_if_post H :=
tryfalse.



Ltac case_if_on_tactic_core E Eq :=
match type of E with
| {_}+{_} => destruct E as [Eq | Eq]
| _ => let X := fresh "TEMP" in
sets_eq <- X Eq: E;
destruct X
end.

Ltac case_if_on_tactic E Eq :=
case_if_on_tactic_core E Eq; case_if_post Eq.

Tactic Notation "case_if_on" constr(E) "as" simple_intropattern(Eq) :=
case_if_on_tactic E Eq.

Tactic Notation "case_if" "as" simple_intropattern(Eq) :=
match goal with
| |- context [if ?B then _ else _] => case_if_on B as Eq
| K: context [if ?B then _ else _] |- _ => case_if_on B as Eq
end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
match type of H with context [if ?B then _ else _] =>
case_if_on B as Eq end.

Tactic Notation "case_if" :=
let Eq := fresh "C" in case_if as Eq.

Tactic Notation "case_if" "in" hyp(H) :=
let Eq := fresh "C" in case_if in H as Eq.



Ltac cases_if_on_tactic_core E Eq :=
match type of E with
| {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
| _ => let X := fresh "TEMP" in
sets_eq <- X Eq: E;
destruct X
end.

Ltac cases_if_on_tactic E Eq :=
cases_if_on_tactic_core E Eq; tryfalse; case_if_post Eq.

Tactic Notation "cases_if_on" constr(E) "as" simple_intropattern(Eq) :=
cases_if_on_tactic E Eq.

Tactic Notation "cases_if" "as" simple_intropattern(Eq) :=
match goal with
| |- context [if ?B then _ else _] => cases_if_on B as Eq
| K: context [if ?B then _ else _] |- _ => cases_if_on B as Eq
end.

Tactic Notation "cases_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
match type of H with context [if ?B then _ else _] =>
cases_if_on B as Eq end.

Tactic Notation "cases_if" :=
let Eq := fresh "C" in cases_if as Eq.

Tactic Notation "cases_if" "in" hyp(H) :=
let Eq := fresh "C" in cases_if in H as Eq.



Ltac case_ifs_core :=
repeat case_if.

Tactic Notation "case_ifs" :=
case_ifs_core.



Ltac destruct_if_post := tryfalse.

Tactic Notation "destruct_if"
"as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
match goal with
| |- context [if ?B then _ else _] => destruct B as [Eq1|Eq2]
| K: context [if ?B then _ else _] |- _ => destruct B as [Eq1|Eq2]
end;
destruct_if_post.

Tactic Notation "destruct_if" "in" hyp(H)
"as" simple_intropattern(Eq1) simple_intropattern(Eq2) :=
match type of H with context [if ?B then _ else _] =>
destruct B as [Eq1|Eq2] end;
destruct_if_post.

Tactic Notation "destruct_if" "as" simple_intropattern(Eq) :=
destruct_if as Eq Eq.
Tactic Notation "destruct_if" "in" hyp(H) "as" simple_intropattern(Eq) :=
destruct_if in H as Eq Eq.

Tactic Notation "destruct_if" :=
let Eq := fresh "C" in destruct_if as Eq Eq.
Tactic Notation "destruct_if" "in" hyp(H) :=
let Eq := fresh "C" in destruct_if in H as Eq Eq.



Ltac find_head_match T :=
match T with context [?E] =>
match T with
| E => fail 1
| _ => constr:(E)
end
end.

Ltac destruct_head_match_core cont :=
match goal with
| |- ?T1 = ?T2 => first [ let E := find_head_match T1 in cont E
| let E := find_head_match T2 in cont E ]
| |- ?T1 => let E := find_head_match T1 in cont E
end;
destruct_if_post.

Tactic Notation "destruct_head_match" "as" simple_intropattern(I) :=
destruct_head_match_core ltac:(fun E => destruct E as I).

Tactic Notation "destruct_head_match" :=
destruct_head_match_core ltac:(fun E => destruct E).





Tactic Notation "cases'" constr(E) "as" ident(H) :=
let X := fresh "TEMP" in
set (X := E) in *; def_to_eq X H E;
destruct X.

Tactic Notation "cases'" constr(E) :=
let x := fresh "Eq" in cases' E as H.



Ltac cases_if_on' E Eq :=
match type of E with
| {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
| _ => let X := fresh "TEMP" in
sets_eq X Eq: E;
destruct X
end; case_if_post Eq.

Tactic Notation "cases_if'" "as" simple_intropattern(Eq) :=
match goal with
| |- context [if ?B then _ else _] => cases_if_on' B Eq
| K: context [if ?B then _ else _] |- _ => cases_if_on' B Eq
end.

Tactic Notation "cases_if'" :=
let Eq := fresh "C" in cases_if' as Eq.






From Coq Require Import Program.Equality.

Ltac inductions_post :=
unfold eq' in *.

Tactic Notation "inductions" ident(E) :=
dependent induction E; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) :=
dependent induction E generalizing X1; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2) :=
dependent induction E generalizing X1 X2; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
ident(X3) :=
dependent induction E generalizing X1 X2 X3; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
ident(X3) ident(X4) :=
dependent induction E generalizing X1 X2 X3 X4; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
ident(X3) ident(X4) ident(X5) :=
dependent induction E generalizing X1 X2 X3 X4 X5; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
ident(X3) ident(X4) ident(X5) ident(X6) :=
dependent induction E generalizing X1 X2 X3 X4 X5 X6; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) :=
dependent induction E generalizing X1 X2 X3 X4 X5 X6 X7; inductions_post.
Tactic Notation "inductions" ident(E) "gen" ident(X1) ident(X2)
ident(X3) ident(X4) ident(X5) ident(X6) ident(X7) ident(X8) :=
dependent induction E generalizing X1 X2 X3 X4 X5 X6 X7 X8; inductions_post.






Ltac induction_wf_core_then IH E X cont :=
let T := type of E in
let T := eval hnf in T in
let clearX tt :=
first [ clear X | fail 3 "the variable on which the induction is done appears in the hypotheses" ] in
match T with

| ?A -> ?A -> Prop =>
pattern X;
first [
applys well_founded_ind E;
clearX tt;
[
| intros X IH; cont tt ]
| fail 2 ]
| _ =>
pattern X;
applys well_founded_ind E;
clearX tt;
intros X IH;
cont tt
end.

Ltac induction_wf_core IH E X :=
induction_wf_core_then IH E X ltac:(fun _ => idtac).

Tactic Notation "induction_wf" ident(IH) ":" constr(E) ident(X) :=
induction_wf_core IH E X.
Tactic Notation "induction_wf" ":" constr(E) ident(X) :=
let IH := fresh "IH" in induction_wf IH: E X.
Tactic Notation "induction_wf" ":" constr(E) ident(X) :=
induction_wf: E X.



From Coq Require Import Arith.Compare_dec.
From Coq Require Import omega.Omega.

Lemma induct_height_max2 : forall n1 n2 : nat,
exists n, n1 < n /\ n2 < n.
Proof using. hammer_hook "LibTactics" "LibTactics.induct_height_max2".
intros. destruct (lt_dec n1 n2).
exists (S n2). omega.
exists (S n1). omega.
Qed.

Ltac induct_height_step x :=
match goal with
| H: exists _, _ |- _ =>
let n := fresh "n" in let y := fresh "x" in
destruct H as [n ?];
forwards (y&?&?): induct_height_max2 n x;
induct_height_step y
| _ => exists (S x); eauto
end.

Ltac induct_height := induct_height_step O.






Definition COIND (P:Prop) := P.

Tactic Notation "cofixs" ident(IH) :=
cofix IH;
match type of IH with ?P => change P with (COIND P) in IH end.



Ltac clear_coind :=
repeat match goal with H: COIND _ |- _ => clear H end.



Tactic Notation "abstracts" tactic(tac) :=
clear_coind; tac.







Ltac decides_equality_tactic :=
first [ decide equality | progress(unfolds); decides_equality_tactic ].

Tactic Notation "decides_equality" :=
decides_equality_tactic.






Lemma iff_intro_swap : forall (P Q : Prop),
(Q -> P) -> (P -> Q) -> (P <-> Q).
Proof using. hammer_hook "LibTactics" "LibTactics.iff_intro_swap". intuition. Qed.

Tactic Notation "iff" simple_intropattern(H1) simple_intropattern(H2) :=
split; [ intros H1 | intros H2 ].
Tactic Notation "iff" simple_intropattern(H) :=
iff H H.
Tactic Notation "iff" :=
let H := fresh "H" in iff H.

Tactic Notation "iff" "<-" simple_intropattern(H1) simple_intropattern(H2) :=
apply iff_intro_swap; [ intros H1 | intros H2 ].
Tactic Notation "iff" "<-" simple_intropattern(H) :=
iff <- H H.
Tactic Notation "iff" "<-" :=
let H := fresh "H" in iff <- H.








Ltac splits_tactic N :=
match N with
| O => fail
| S O => idtac
| S ?N' => split; [| splits_tactic N']
end.

Ltac unfold_goal_until_conjunction :=
match goal with
| |- _ /\ _ => idtac
| _ => progress(unfolds); unfold_goal_until_conjunction
end.

Ltac get_term_conjunction_arity T :=
match T with
| _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(8)
| _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(7)
| _ /\ _ /\ _ /\ _ /\ _ /\ _ => constr:(6)
| _ /\ _ /\ _ /\ _ /\ _ => constr:(5)
| _ /\ _ /\ _ /\ _ => constr:(4)
| _ /\ _ /\ _ => constr:(3)
| _ /\ _ => constr:(2)
| _ -> ?T' => get_term_conjunction_arity T'
| _ => let P := get_head T in
let T' := eval unfold P in T in
match T' with
| T => fail 1
| _ => get_term_conjunction_arity T'
end

end.

Ltac get_goal_conjunction_arity :=
match goal with |- ?T => get_term_conjunction_arity T end.



Tactic Notation "splits" :=
unfold_goal_until_conjunction;
let N := get_goal_conjunction_arity in
splits_tactic N.



Tactic Notation "splits" constr(N) :=
let N := number_to_nat N in
splits_tactic N.





Ltac destructs_conjunction_tactic N T :=
match N with
| 2 => destruct T as [? ?]
| 3 => destruct T as [? [? ?]]
| 4 => destruct T as [? [? [? ?]]]
| 5 => destruct T as [? [? [? [? ?]]]]
| 6 => destruct T as [? [? [? [? [? ?]]]]]
| 7 => destruct T as [? [? [? [? [? [? ?]]]]]]
end.



Tactic Notation "destructs" constr(T) :=
let TT := type of T in
let N := get_term_conjunction_arity TT in
destructs_conjunction_tactic N T.



Tactic Notation "destructs" constr(N) constr(T) :=
let N := number_to_nat N in
destructs_conjunction_tactic N T.





Ltac branch_tactic K N :=
match constr:((K,N)) with
| (_,0) => fail 1
| (0,_) => fail 1
| (1,1) => idtac
| (1,_) => left
| (S ?K', S ?N') => right; branch_tactic K' N'
end.

Ltac unfold_goal_until_disjunction :=
match goal with
| |- _ \/ _ => idtac
| _ => progress(unfolds); unfold_goal_until_disjunction
end.

Ltac get_term_disjunction_arity T :=
match T with
| _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(8)
| _ \/ _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(7)
| _ \/ _ \/ _ \/ _ \/ _ \/ _ => constr:(6)
| _ \/ _ \/ _ \/ _ \/ _ => constr:(5)
| _ \/ _ \/ _ \/ _ => constr:(4)
| _ \/ _ \/ _ => constr:(3)
| _ \/ _ => constr:(2)
| _ -> ?T' => get_term_disjunction_arity T'
| _ => let P := get_head T in
let T' := eval unfold P in T in
match T' with
| T => fail 1
| _ => get_term_disjunction_arity T'
end
end.

Ltac get_goal_disjunction_arity :=
match goal with |- ?T => get_term_disjunction_arity T end.



Tactic Notation "branch" constr(K) :=
let K := number_to_nat K in
unfold_goal_until_disjunction;
let N := get_goal_disjunction_arity in
branch_tactic K N.



Tactic Notation "branch" constr(K) "of" constr(N) :=
let N := number_to_nat N in
let K := number_to_nat K in
branch_tactic K N.





Ltac destructs_disjunction_tactic N T :=
match N with
| 2 => destruct T as [? | ?]
| 3 => destruct T as [? | [? | ?]]
| 4 => destruct T as [? | [? | [? | ?]]]
| 5 => destruct T as [? | [? | [? | [? | ?]]]]
end.



Tactic Notation "branches" constr(T) :=
let TT := type of T in
let N := get_term_disjunction_arity TT in
destructs_disjunction_tactic N T.



Tactic Notation "branches" constr(N) constr(T) :=
let N := number_to_nat N in
destructs_disjunction_tactic N T.



Tactic Notation "branches" :=
match goal with h: _ \/ _ |- _ => branches h end.





Ltac get_term_existential_arity T :=
match T with
| exists x1 x2 x3 x4 x5 x6 x7 x8, _ => constr:(8)
| exists x1 x2 x3 x4 x5 x6 x7, _ => constr:(7)
| exists x1 x2 x3 x4 x5 x6, _ => constr:(6)
| exists x1 x2 x3 x4 x5, _ => constr:(5)
| exists x1 x2 x3 x4, _ => constr:(4)
| exists x1 x2 x3, _ => constr:(3)
| exists x1 x2, _ => constr:(2)
| exists x1, _ => constr:(1)
| _ -> ?T' => get_term_existential_arity T'
| _ => let P := get_head T in
let T' := eval unfold P in T in
match T' with
| T => fail 1
| _ => get_term_existential_arity T'
end
end.

Ltac get_goal_existential_arity :=
match goal with |- ?T => get_term_existential_arity T end.



Tactic Notation "exists_original" constr(T1) :=
exists T1.
Tactic Notation "exists" constr(T1) :=
match T1 with
| ltac_wild => esplit
| ltac_wilds => repeat esplit
| _ => exists T1
end.
Tactic Notation "exists" constr(T1) constr(T2) :=
exists T1; exists T2.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) :=
exists T1; exists T2; exists T3.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4) :=
exists T1; exists T2; exists T3; exists T4.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
constr(T5) :=
exists T1; exists T2; exists T3; exists T4; exists T5.
Tactic Notation "exists" constr(T1) constr(T2) constr(T3) constr(T4)
constr(T5) constr(T6) :=
exists T1; exists T2; exists T3; exists T4; exists T5; exists T6.



Tactic Notation "exists" constr(T1) "," constr(T2) :=
exists T1 T2.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) :=
exists T1 T2 T3.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) :=
exists T1 T2 T3 T4.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
constr(T5) :=
exists T1 T2 T3 T4 T5.
Tactic Notation "exists" constr(T1) "," constr(T2) "," constr(T3) "," constr(T4) ","
constr(T5) "," constr(T6) :=
exists T1 T2 T3 T4 T5 T6.



Tactic Notation "exists___" constr(N) :=
let rec aux N :=
match N with
| 0 => idtac
| S ?N' => esplit; aux N'
end in
let N := number_to_nat N in aux N.


Tactic Notation "exists___" :=
let N := get_goal_existential_arity in
exists___ N.


Tactic Notation "exists" :=
exists___.


Tactic Notation "exists_all" := exists___.





Ltac unpack_core :=
repeat match goal with
| H: _ /\ _ |- _ => destruct H
| H: exists (varname: _), _ |- _ =>

let name := fresh varname in
destruct H as [name ?]
end.

Ltac unpack_hypothesis H :=
try match type of H with
| _ /\ _ =>
let h1 := fresh "TEMP" in
let h2 := fresh "TEMP" in
destruct H as [ h1 h2 ];
unpack_hypothesis h1;
unpack_hypothesis h2
| exists (varname: _), _ =>

let name := fresh varname in
let body := fresh "TEMP" in
destruct H as [name body];
unpack_hypothesis body
end.

Tactic Notation "unpack" :=
unpack_core.
Tactic Notation "unpack" constr(H) :=
unpack_hypothesis H.






Tactic Notation "typeclass" :=
let go _ := eauto with typeclass_instances in
solve [ go tt | constructor; go tt ].



Tactic Notation "solve_typeclass" :=
solve [ eauto with typeclass_instances ].







Tactic Notation "f_equal" :=
f_equal.
Tactic Notation "constructor" :=
constructor.
Tactic Notation "simple" :=
simpl.

Tactic Notation "split" :=
split.

Tactic Notation "right" :=
right.
Tactic Notation "left" :=
left.






Tactic Notation "hint" constr(E) :=
let H := fresh "Hint" in lets H: E.
Tactic Notation "hint" constr(E1) "," constr(E2) :=
hint E1; hint E2.
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) :=
hint E1; hint E2; hint(E3).
Tactic Notation "hint" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
hint E1; hint E2; hint(E3); hint(E4 ).






Tactic Notation "jauto" :=
try solve [ jauto_set; eauto ].

Tactic Notation "jauto_fast" :=
try solve [ auto | eauto | jauto ].



Tactic Notation "iauto" := try solve [intuition eauto].








Ltac auto_tilde_default := auto.
Ltac auto_tilde := auto_tilde_default.




Ltac auto_star_default := try solve [ jauto ].
Ltac auto_star := auto_star_default.



Tactic Notation "autos" :=
auto_tilde.
Tactic Notation "autos" "~" :=
auto_tilde.
Tactic Notation "autos" "~" constr(E1) :=
lets: E1; auto_tilde.
Tactic Notation "autos" "~" constr(E1) constr(E2) :=
lets: E1; lets: E2; auto_tilde.
Tactic Notation "autos" "~" constr(E1) constr(E2) constr(E3) :=
lets: E1; lets: E2; lets: E3; auto_tilde.



Tactic Notation "autos" "*" :=
auto_star.
Tactic Notation "autos" "*" constr(E1) :=
lets: E1; auto_star.
Tactic Notation "autos" "*" constr(E1) constr(E2) :=
lets: E1; lets: E2; auto_star.
Tactic Notation "autos" "*" constr(E1) constr(E2) constr(E3) :=
lets: E1; lets: E2; lets: E3; auto_star.



Ltac auto_false_base cont :=
try solve [
intros_all; try match goal with |- _ <-> _ => split end;
solve [ cont tt | intros_all; false; cont tt ] ].

Tactic Notation "auto_false" :=
auto_false_base ltac:(fun tt => auto).
Tactic Notation "auto_false" "~" :=
auto_false_base ltac:(fun tt => auto_tilde).
Tactic Notation "auto_false" "*" :=
auto_false_base ltac:(fun tt => auto_star).

Tactic Notation "dauto" :=
dintuition eauto.






Tactic Notation "equates" "~" constr(E) :=
equates E; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) :=
equates n1 n2; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) constr(n3) :=
equates n1 n2 n3; auto_tilde.
Tactic Notation "equates" "~" constr(n1) constr(n2) constr(n3) constr(n4) :=
equates n1 n2 n3 n4; auto_tilde.

Tactic Notation "applys_eq" "~" constr(H) constr(E) :=
applys_eq H E; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) :=
applys_eq H n1 n2; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) constr(n3) :=
applys_eq H n1 n2 n3; auto_tilde.
Tactic Notation "applys_eq" "~" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
applys_eq H n1 n2 n3 n4; auto_tilde.

Tactic Notation "apply" "~" constr(H) :=
sapply H; auto_tilde.

Tactic Notation "destruct" "~" constr(H) :=
destruct H; auto_tilde.
Tactic Notation "destruct" "~" constr(H) "as" simple_intropattern(I) :=
destruct H as I; auto_tilde.
Tactic Notation "f_equal" "~" :=
f_equal; auto_tilde.
Tactic Notation "induction" "~" constr(H) :=
induction H; auto_tilde.
Tactic Notation "inversion" "~" constr(H) :=
inversion H; auto_tilde.
Tactic Notation "split" "~" :=
split; auto_tilde.
Tactic Notation "subst" "~" :=
subst; auto_tilde.
Tactic Notation "right" "~" :=
right; auto_tilde.
Tactic Notation "left" "~" :=
left; auto_tilde.
Tactic Notation "constructor" "~" :=
constructor; auto_tilde.
Tactic Notation "constructors" "~" :=
constructors; auto_tilde.

Tactic Notation "false" "~" :=
false; auto_tilde.
Tactic Notation "false" "~" constr(E) :=
false_then E ltac:(fun _ => auto_tilde).
Tactic Notation "false" "~" constr(E0) constr(E1) :=
false~ (>> E0 E1).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) :=
false~ (>> E0 E1 E2).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) constr(E3) :=
false~ (>> E0 E1 E2 E3).
Tactic Notation "false" "~" constr(E0) constr(E1) constr(E2) constr(E3) constr(E4) :=
false~ (>> E0 E1 E2 E3 E4).
Tactic Notation "tryfalse" "~" :=
try solve [ false~ ].

Tactic Notation "asserts" "~" simple_intropattern(H) ":" constr(E) :=
asserts H: E; [ auto_tilde | idtac ].
Tactic Notation "asserts" "~" ":" constr(E) :=
let H := fresh "H" in asserts~ H: E.
Tactic Notation "cuts" "~" simple_intropattern(H) ":" constr(E) :=
cuts H: E; [ auto_tilde | idtac ].
Tactic Notation "cuts" "~" ":" constr(E) :=
cuts: E; [ auto_tilde | idtac ].

Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E) :=
lets I: E; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) :=
lets I: E0 A1; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) :=
lets I: E0 A1 A2; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
lets I: E0 A1 A2 A3; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
lets I: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "lets" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
lets I: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "lets" "~" ":" constr(E) :=
lets: E; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
constr(A1) :=
lets: E0 A1; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
constr(A1) constr(A2) :=
lets: E0 A1 A2; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
lets: E0 A1 A2 A3; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
lets: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "lets" "~" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
lets: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E) :=
forwards I: E; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) :=
forwards I: E0 A1; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) :=
forwards I: E0 A1 A2; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
forwards I: E0 A1 A2 A3; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
forwards I: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "forwards" "~" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
forwards I: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "forwards" "~" ":" constr(E) :=
forwards: E; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
constr(A1) :=
forwards: E0 A1; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
constr(A1) constr(A2) :=
forwards: E0 A1 A2; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
forwards: E0 A1 A2 A3; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
forwards: E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "forwards" "~" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
forwards: E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "applys" "~" constr(H) :=
sapply H; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) :=
applys E0 A1; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) :=
applys E0 A1; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) :=
applys E0 A1 A2; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) :=
applys E0 A1 A2 A3; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
applys E0 A1 A2 A3 A4; auto_tilde.
Tactic Notation "applys" "~" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
applys E0 A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "specializes" "~" hyp(H) :=
specializes H; auto_tilde.
Tactic Notation "specializes" "~" hyp(H) constr(A1) :=
specializes H A1; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
specializes H A1 A2; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
specializes H A1 A2 A3; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
specializes H A1 A2 A3 A4; auto_tilde.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
specializes H A1 A2 A3 A4 A5; auto_tilde.

Tactic Notation "fapply" "~" constr(E) :=
fapply E; auto_tilde.
Tactic Notation "sapply" "~" constr(E) :=
sapply E; auto_tilde.

Tactic Notation "logic" "~" constr(E) :=
logic_base E ltac:(fun _ => auto_tilde).

Tactic Notation "intros_all" "~" :=
intros_all; auto_tilde.

Tactic Notation "unfolds" "~" :=
unfolds; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) :=
unfolds F1; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) :=
unfolds F1, F2; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) "," constr(F3) :=
unfolds F1, F2, F3; auto_tilde.
Tactic Notation "unfolds" "~" constr(F1) "," constr(F2) "," constr(F3) ","
constr(F4) :=
unfolds F1, F2, F3, F4; auto_tilde.

Tactic Notation "simple" "~" :=
simpl; auto_tilde.
Tactic Notation "simple" "~" "in" hyp(H) :=
simpl in H; auto_tilde.
Tactic Notation "simpls" "~" :=
simpls; auto_tilde.
Tactic Notation "hnfs" "~" :=
hnfs; auto_tilde.
Tactic Notation "hnfs" "~" "in" hyp(H) :=
hnf in H; auto_tilde.
Tactic Notation "substs" "~" :=
substs; auto_tilde.
Tactic Notation "intro_hyp" "~" hyp(H) :=
subst_hyp H; auto_tilde.
Tactic Notation "intro_subst" "~" :=
intro_subst; auto_tilde.
Tactic Notation "subst_eq" "~" constr(E) :=
subst_eq E; auto_tilde.

Tactic Notation "rewrite" "~" constr(E) :=
rewrite E; auto_tilde.
Tactic Notation "rewrite" "~" "<-" constr(E) :=
rewrite <- E; auto_tilde.
Tactic Notation "rewrite" "~" constr(E) "in" hyp(H) :=
rewrite E in H; auto_tilde.
Tactic Notation "rewrite" "~" "<-" constr(E) "in" hyp(H) :=
rewrite <- E in H; auto_tilde.

Tactic Notation "rewrites" "~" constr(E) :=
rewrites E; auto_tilde.
Tactic Notation "rewrites" "~" constr(E) "in" hyp(H) :=
rewrites E in H; auto_tilde.
Tactic Notation "rewrites" "~" constr(E) "in" "*" :=
rewrites E in *; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) :=
rewrites <- E; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) "in" hyp(H) :=
rewrites <- E in H; auto_tilde.
Tactic Notation "rewrites" "~" "<-" constr(E) "in" "*" :=
rewrites <- E in *; auto_tilde.

Tactic Notation "rewrite_all" "~" constr(E) :=
rewrite_all E; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) :=
rewrite_all <- E; auto_tilde.
Tactic Notation "rewrite_all" "~" constr(E) "in" ident(H) :=
rewrite_all E in H; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) "in" ident(H) :=
rewrite_all <- E in H; auto_tilde.
Tactic Notation "rewrite_all" "~" constr(E) "in" "*" :=
rewrite_all E in *; auto_tilde.
Tactic Notation "rewrite_all" "~" "<-" constr(E) "in" "*" :=
rewrite_all <- E in *; auto_tilde.

Tactic Notation "asserts_rewrite" "~" constr(E) :=
asserts_rewrite E; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) :=
asserts_rewrite <- E; auto_tilde.
Tactic Notation "asserts_rewrite" "~" constr(E) "in" hyp(H) :=
asserts_rewrite E in H; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) "in" hyp(H) :=
asserts_rewrite <- E in H; auto_tilde.
Tactic Notation "asserts_rewrite" "~" constr(E) "in" "*" :=
asserts_rewrite E in *; auto_tilde.
Tactic Notation "asserts_rewrite" "~" "<-" constr(E) "in" "*" :=
asserts_rewrite <- E in *; auto_tilde.

Tactic Notation "cuts_rewrite" "~" constr(E) :=
cuts_rewrite E; auto_tilde.
Tactic Notation "cuts_rewrite" "~" "<-" constr(E) :=
cuts_rewrite <- E; auto_tilde.
Tactic Notation "cuts_rewrite" "~" constr(E) "in" hyp(H) :=
cuts_rewrite E in H; auto_tilde.
Tactic Notation "cuts_rewrite" "~" "<-" constr(E) "in" hyp(H) :=
cuts_rewrite <- E in H; auto_tilde.

Tactic Notation "erewrite" "~" constr(E) :=
erewrite E; auto_tilde.

Tactic Notation "fequal" "~" :=
fequal; auto_tilde.
Tactic Notation "fequals" "~" :=
fequals; auto_tilde.
Tactic Notation "pi_rewrite" "~" constr(E) :=
pi_rewrite E; auto_tilde.
Tactic Notation "pi_rewrite" "~" constr(E) "in" hyp(H) :=
pi_rewrite E in H; auto_tilde.

Tactic Notation "invert" "~" hyp(H) :=
invert H; auto_tilde.
Tactic Notation "inverts" "~" hyp(H) :=
inverts H; auto_tilde.
Tactic Notation "inverts" "~" hyp(E) "as" :=
inverts E as; auto_tilde.
Tactic Notation "injects" "~" hyp(H) :=
injects H; auto_tilde.
Tactic Notation "inversions" "~" hyp(H) :=
inversions H; auto_tilde.

Tactic Notation "cases" "~" constr(E) "as" ident(H) :=
cases E as H; auto_tilde.
Tactic Notation "cases" "~" constr(E) :=
cases E; auto_tilde.
Tactic Notation "case_if" "~" :=
case_if; auto_tilde.
Tactic Notation "case_ifs" "~" :=
case_ifs; auto_tilde.
Tactic Notation "case_if" "~" "in" hyp(H) :=
case_if in H; auto_tilde.
Tactic Notation "cases_if" "~" :=
cases_if; auto_tilde.
Tactic Notation "cases_if" "~" "in" hyp(H) :=
cases_if in H; auto_tilde.
Tactic Notation "destruct_if" "~" :=
destruct_if; auto_tilde.
Tactic Notation "destruct_if" "~" "in" hyp(H) :=
destruct_if in H; auto_tilde.
Tactic Notation "destruct_head_match" "~" :=
destruct_head_match; auto_tilde.

Tactic Notation "cases'" "~" constr(E) "as" ident(H) :=
cases' E as H; auto_tilde.
Tactic Notation "cases'" "~" constr(E) :=
cases' E; auto_tilde.
Tactic Notation "cases_if'" "~" "as" ident(H) :=
cases_if' as H; auto_tilde.
Tactic Notation "cases_if'" "~" :=
cases_if'; auto_tilde.

Tactic Notation "decides_equality" "~" :=
decides_equality; auto_tilde.

Tactic Notation "iff" "~" :=
iff; auto_tilde.
Tactic Notation "iff" "~" simple_intropattern(I) :=
iff I; auto_tilde.
Tactic Notation "splits" "~" :=
splits; auto_tilde.
Tactic Notation "splits" "~" constr(N) :=
splits N; auto_tilde.

Tactic Notation "destructs" "~" constr(T) :=
destructs T; auto_tilde.
Tactic Notation "destructs" "~" constr(N) constr(T) :=
destructs N T; auto_tilde.

Tactic Notation "branch" "~" constr(N) :=
branch N; auto_tilde.
Tactic Notation "branch" "~" constr(K) "of" constr(N) :=
branch K of N; auto_tilde.

Tactic Notation "branches" "~" :=
branches; auto_tilde.
Tactic Notation "branches" "~" constr(T) :=
branches T; auto_tilde.
Tactic Notation "branches" "~" constr(N) constr(T) :=
branches N T; auto_tilde.

Tactic Notation "exists" "~" :=
exists; auto_tilde.
Tactic Notation "exists___" "~" :=
exists___; auto_tilde.
Tactic Notation "exists" "~" constr(T1) :=
exists T1; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) :=
exists T1 T2; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) :=
exists T1 T2 T3; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4) :=
exists T1 T2 T3 T4; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4)
constr(T5) :=
exists T1 T2 T3 T4 T5; auto_tilde.
Tactic Notation "exists" "~" constr(T1) constr(T2) constr(T3) constr(T4)
constr(T5) constr(T6) :=
exists T1 T2 T3 T4 T5 T6; auto_tilde.

Tactic Notation "exists" "~" constr(T1) "," constr(T2) :=
exists T1 T2; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) :=
exists T1 T2 T3; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
constr(T4) :=
exists T1 T2 T3 T4; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
constr(T4) "," constr(T5) :=
exists T1 T2 T3 T4 T5; auto_tilde.
Tactic Notation "exists" "~" constr(T1) "," constr(T2) "," constr(T3) ","
constr(T4) "," constr(T5) "," constr(T6) :=
exists T1 T2 T3 T4 T5 T6; auto_tilde.






Tactic Notation "equates" "*" constr(E) :=
equates E; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) :=
equates n1 n2; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) constr(n3) :=
equates n1 n2 n3; auto_star.
Tactic Notation "equates" "*" constr(n1) constr(n2) constr(n3) constr(n4) :=
equates n1 n2 n3 n4; auto_star.

Tactic Notation "applys_eq" "*" constr(H) constr(E) :=
applys_eq H E; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) :=
applys_eq H n1 n2; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) constr(n3) :=
applys_eq H n1 n2 n3; auto_star.
Tactic Notation "applys_eq" "*" constr(H) constr(n1) constr(n2) constr(n3) constr(n4) :=
applys_eq H n1 n2 n3 n4; auto_star.

Tactic Notation "apply" "*" constr(H) :=
sapply H; auto_star.

Tactic Notation "destruct" "*" constr(H) :=
destruct H; auto_star.
Tactic Notation "destruct" "*" constr(H) "as" simple_intropattern(I) :=
destruct H as I; auto_star.
Tactic Notation "f_equal" "*" :=
f_equal; auto_star.
Tactic Notation "induction" "*" constr(H) :=
induction H; auto_star.
Tactic Notation "inversion" "*" constr(H) :=
inversion H; auto_star.
Tactic Notation "split" "*" :=
split; auto_star.
Tactic Notation "subs" "*" :=
subst; auto_star.
Tactic Notation "subst" "*" :=
subst; auto_star.
Tactic Notation "right" "*" :=
right; auto_star.
Tactic Notation "left" "*" :=
left; auto_star.
Tactic Notation "constructor" "*" :=
constructor; auto_star.
Tactic Notation "constructors" "*" :=
constructors; auto_star.

Tactic Notation "false" "*" :=
false; auto_star.
Tactic Notation "false" "*" constr(E) :=
false_then E ltac:(fun _ => auto_star).
Tactic Notation "false" "*" constr(E0) constr(E1) :=
false* (>> E0 E1).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) :=
false* (>> E0 E1 E2).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) constr(E3) :=
false* (>> E0 E1 E2 E3).
Tactic Notation "false" "*" constr(E0) constr(E1) constr(E2) constr(E3) constr(E4) :=
false* (>> E0 E1 E2 E3 E4).
Tactic Notation "tryfalse" "*" :=
try solve [ false* ].

Tactic Notation "asserts" "*" simple_intropattern(H) ":" constr(E) :=
asserts H: E; [ auto_star | idtac ].
Tactic Notation "asserts" "*" ":" constr(E) :=
let H := fresh "H" in asserts* H: E.
Tactic Notation "cuts" "*" simple_intropattern(H) ":" constr(E) :=
cuts H: E; [ auto_star | idtac ].
Tactic Notation "cuts" "*" ":" constr(E) :=
cuts: E; [ auto_star | idtac ].

Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E) :=
lets I: E; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) :=
lets I: E0 A1; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) :=
lets I: E0 A1 A2; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
lets I: E0 A1 A2 A3; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
lets I: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "lets" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
lets I: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "lets" "*" ":" constr(E) :=
lets: E; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
constr(A1) :=
lets: E0 A1; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
constr(A1) constr(A2) :=
lets: E0 A1 A2; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
lets: E0 A1 A2 A3; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
lets: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "lets" "*" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
lets: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E) :=
forwards I: E; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) :=
forwards I: E0 A1; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) :=
forwards I: E0 A1 A2; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
forwards I: E0 A1 A2 A3; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
forwards I: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "forwards" "*" simple_intropattern(I) ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
forwards I: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "forwards" "*" ":" constr(E) :=
forwards: E; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
constr(A1) :=
forwards: E0 A1; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
constr(A1) constr(A2) :=
forwards: E0 A1 A2; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
constr(A1) constr(A2) constr(A3) :=
forwards: E0 A1 A2 A3; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) :=
forwards: E0 A1 A2 A3 A4; auto_star.
Tactic Notation "forwards" "*" ":" constr(E0)
constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
forwards: E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "applys" "*" constr(H) :=
sapply H; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) :=
applys E0 A1; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) :=
applys E0 A1; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) :=
applys E0 A1 A2; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) :=
applys E0 A1 A2 A3; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
applys E0 A1 A2 A3 A4; auto_star.
Tactic Notation "applys" "*" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
applys E0 A1 A2 A3 A4 A5; auto_star.

Tactic Notation "specializes" "*" hyp(H) :=
specializes H; auto_star.
Tactic Notation "specializes" "~" hyp(H) constr(A1) :=
specializes H A1; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) :=
specializes H A1 A2; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) :=
specializes H A1 A2 A3; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) :=
specializes H A1 A2 A3 A4; auto_star.
Tactic Notation "specializes" hyp(H) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
specializes H A1 A2 A3 A4 A5; auto_star.

Tactic Notation "fapply" "*" constr(E) :=
fapply E; auto_star.
Tactic Notation "sapply" "*" constr(E) :=
sapply E; auto_star.

Tactic Notation "logic" constr(E) :=
logic_base E ltac:(fun _ => auto_star).

Tactic Notation "intros_all" "*" :=
intros_all; auto_star.

Tactic Notation "unfolds" "*" :=
unfolds; auto_star.
Tactic Notation "unfolds" "*" constr(F1) :=
unfolds F1; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) :=
unfolds F1, F2; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) "," constr(F3) :=
unfolds F1, F2, F3; auto_star.
Tactic Notation "unfolds" "*" constr(F1) "," constr(F2) "," constr(F3) ","
constr(F4) :=
unfolds F1, F2, F3, F4; auto_star.

Tactic Notation "simple" "*" :=
simpl; auto_star.
Tactic Notation "simple" "*" "in" hyp(H) :=
simpl in H; auto_star.
Tactic Notation "simpls" "*" :=
simpls; auto_star.
Tactic Notation "hnfs" "*" :=
hnfs; auto_star.
Tactic Notation "hnfs" "*" "in" hyp(H) :=
hnf in H; auto_star.
Tactic Notation "substs" "*" :=
substs; auto_star.
Tactic Notation "intro_hyp" "*" hyp(H) :=
subst_hyp H; auto_star.
Tactic Notation "intro_subst" "*" :=
intro_subst; auto_star.
Tactic Notation "subst_eq" "*" constr(E) :=
subst_eq E; auto_star.

Tactic Notation "rewrite" "*" constr(E) :=
rewrite E; auto_star.
Tactic Notation "rewrite" "*" "<-" constr(E) :=
rewrite <- E; auto_star.
Tactic Notation "rewrite" "*" constr(E) "in" hyp(H) :=
rewrite E in H; auto_star.
Tactic Notation "rewrite" "*" "<-" constr(E) "in" hyp(H) :=
rewrite <- E in H; auto_star.

Tactic Notation "rewrites" "*" constr(E) :=
rewrites E; auto_star.
Tactic Notation "rewrites" "*" constr(E) "in" hyp(H):=
rewrites E in H; auto_star.
Tactic Notation "rewrites" "*" constr(E) "in" "*":=
rewrites E in *; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) :=
rewrites <- E; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) "in" hyp(H):=
rewrites <- E in H; auto_star.
Tactic Notation "rewrites" "*" "<-" constr(E) "in" "*":=
rewrites <- E in *; auto_star.

Tactic Notation "rewrite_all" "*" constr(E) :=
rewrite_all E; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) :=
rewrite_all <- E; auto_star.
Tactic Notation "rewrite_all" "*" constr(E) "in" ident(H) :=
rewrite_all E in H; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) "in" ident(H) :=
rewrite_all <- E in H; auto_star.
Tactic Notation "rewrite_all" "*" constr(E) "in" "*" :=
rewrite_all E in *; auto_star.
Tactic Notation "rewrite_all" "*" "<-" constr(E) "in" "*" :=
rewrite_all <- E in *; auto_star.

Tactic Notation "asserts_rewrite" "*" constr(E) :=
asserts_rewrite E; auto_star.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) :=
asserts_rewrite <- E; auto_star.
Tactic Notation "asserts_rewrite" "*" constr(E) "in" hyp(H) :=
asserts_rewrite E; auto_star.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) "in" hyp(H) :=
asserts_rewrite <- E; auto_star.
Tactic Notation "asserts_rewrite" "*" constr(E) "in" "*" :=
asserts_rewrite E in *; auto_tilde.
Tactic Notation "asserts_rewrite" "*" "<-" constr(E) "in" "*" :=
asserts_rewrite <- E in *; auto_tilde.

Tactic Notation "cuts_rewrite" "*" constr(E) :=
cuts_rewrite E; auto_star.
Tactic Notation "cuts_rewrite" "*" "<-" constr(E) :=
cuts_rewrite <- E; auto_star.
Tactic Notation "cuts_rewrite" "*" constr(E) "in" hyp(H) :=
cuts_rewrite E in H; auto_star.
Tactic Notation "cuts_rewrite" "*" "<-" constr(E) "in" hyp(H) :=
cuts_rewrite <- E in H; auto_star.

Tactic Notation "erewrite" "*" constr(E) :=
erewrite E; auto_star.

Tactic Notation "fequal" "*" :=
fequal; auto_star.
Tactic Notation "fequals" "*" :=
fequals; auto_star.
Tactic Notation "pi_rewrite" "*" constr(E) :=
pi_rewrite E; auto_star.
Tactic Notation "pi_rewrite" "*" constr(E) "in" hyp(H) :=
pi_rewrite E in H; auto_star.

Tactic Notation "invert" "*" hyp(H) :=
invert H; auto_star.
Tactic Notation "inverts" "*" hyp(H) :=
inverts H; auto_star.
Tactic Notation "inverts" "*" hyp(E) "as" :=
inverts E as; auto_star.
Tactic Notation "injects" "*" hyp(H) :=
injects H; auto_star.
Tactic Notation "inversions" "*" hyp(H) :=
inversions H; auto_star.

Tactic Notation "cases" "*" constr(E) "as" ident(H) :=
cases E as H; auto_star.
Tactic Notation "cases" "*" constr(E) :=
cases E; auto_star.
Tactic Notation "case_if" "*" :=
case_if; auto_star.
Tactic Notation "case_ifs" "*" :=
case_ifs; auto_star.
Tactic Notation "case_if" "*" "in" hyp(H) :=
case_if in H; auto_star.
Tactic Notation "cases_if" "*" :=
cases_if; auto_star.
Tactic Notation "cases_if" "*" "in" hyp(H) :=
cases_if in H; auto_star.
Tactic Notation "destruct_if" "*" :=
destruct_if; auto_star.
Tactic Notation "destruct_if" "*" "in" hyp(H) :=
destruct_if in H; auto_star.
Tactic Notation "destruct_head_match" "*" :=
destruct_head_match; auto_star.

Tactic Notation "cases'" "*" constr(E) "as" ident(H) :=
cases' E as H; auto_star.
Tactic Notation "cases'" "*" constr(E) :=
cases' E; auto_star.
Tactic Notation "cases_if'" "*" "as" ident(H) :=
cases_if' as H; auto_star.
Tactic Notation "cases_if'" "*" :=
cases_if'; auto_star.

Tactic Notation "decides_equality" "*" :=
decides_equality; auto_star.

Tactic Notation "iff" "*" :=
iff; auto_star.
Tactic Notation "iff" "*" simple_intropattern(I) :=
iff I; auto_star.
Tactic Notation "splits" "*" :=
splits; auto_star.
Tactic Notation "splits" "*" constr(N) :=
splits N; auto_star.

Tactic Notation "destructs" "*" constr(T) :=
destructs T; auto_star.
Tactic Notation "destructs" "*" constr(N) constr(T) :=
destructs N T; auto_star.

Tactic Notation "branch" "*" constr(N) :=
branch N; auto_star.
Tactic Notation "branch" "*" constr(K) "of" constr(N) :=
branch K of N; auto_star.

Tactic Notation "branches" "*" constr(T) :=
branches T; auto_star.
Tactic Notation "branches" "*" constr(N) constr(T) :=
branches N T; auto_star.

Tactic Notation "exists" "*" :=
exists; auto_star.
Tactic Notation "exists___" "*" :=
exists___; auto_star.
Tactic Notation "exists" "*" constr(T1) :=
exists T1; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) :=
exists T1 T2; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) :=
exists T1 T2 T3; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4) :=
exists T1 T2 T3 T4; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4)
constr(T5) :=
exists T1 T2 T3 T4 T5; auto_star.
Tactic Notation "exists" "*" constr(T1) constr(T2) constr(T3) constr(T4)
constr(T5) constr(T6) :=
exists T1 T2 T3 T4 T5 T6; auto_star.

Tactic Notation "exists" "*" constr(T1) "," constr(T2) :=
exists T1 T2; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) :=
exists T1 T2 T3; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
constr(T4) :=
exists T1 T2 T3 T4; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
constr(T4) "," constr(T5) :=
exists T1 T2 T3 T4 T5; auto_star.
Tactic Notation "exists" "*" constr(T1) "," constr(T2) "," constr(T3) ","
constr(T4) "," constr(T5) ","  constr(T6) :=
exists T1 T2 T3 T4 T5 T6; auto_star.









Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" :=
(@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
e = (@ltac_something _ e).
Proof using. hammer_hook "LibTactics" "LibTactics.ltac_something_eq". auto. Qed.

Lemma ltac_something_hide : forall (e:Type),
e -> (@ltac_something _ e).
Proof using. hammer_hook "LibTactics" "LibTactics.ltac_something_hide". auto. Qed.

Lemma ltac_something_show : forall (e:Type),
(@ltac_something _ e) -> e.
Proof using. hammer_hook "LibTactics" "LibTactics.ltac_something_show". auto. Qed.



Tactic Notation "hide_def" hyp(x) :=
let x' := constr:(x) in
let T := eval unfold x in x' in
change T with (@ltac_something _ T) in x.

Tactic Notation "show_def" hyp(x) :=
let x' := constr:(x) in
let U := eval unfold x in x' in
match U with @ltac_something _ ?T =>
change U with T in x end.



Tactic Notation "show_def" :=
unfold ltac_something.
Tactic Notation "show_def" "in" hyp(H) :=
unfold ltac_something in H.
Tactic Notation "show_def" "in" "*" :=
unfold ltac_something in *.



Tactic Notation "hide_defs" :=
repeat match goal with H := ?T |- _ =>
match T with
| @ltac_something _ _ => fail 1
| _ => change T with (@ltac_something _ T) in H
end
end.

Tactic Notation "show_defs" :=
repeat match goal with H := (@ltac_something _ ?T) |- _ =>
change (@ltac_something _ T) with T in H end.



Tactic Notation "show_hyp" hyp(H) :=
apply ltac_something_show in H.

Tactic Notation "hide_hyp" hyp(H) :=
apply ltac_something_hide in H.



Tactic Notation "show_hyps" :=
repeat match goal with
H: @ltac_something _ _ |- _ => show_hyp H end.

Tactic Notation "hide_hyps" :=
repeat match goal with H: ?T |- _ =>
match type of T with
| Prop =>
match T with
| @ltac_something _ _ => fail 2
| _ => hide_hyp H
end
| _ => fail 1
end
end.



Tactic Notation "hide" hyp(H) :=
first [hide_def H | hide_hyp H].

Tactic Notation "show" hyp(H) :=
first [show_def H | show_hyp H].

Tactic Notation "hide_all" :=
hide_hyps; hide_defs.

Tactic Notation "show_all" :=
unfold ltac_something in *.



Tactic Notation "hide_term" constr(E) :=
change E with (@ltac_something _ E).
Tactic Notation "show_term" constr(E) :=
change (@ltac_something _ E) with E.
Tactic Notation "show_term" :=
unfold ltac_something.

Tactic Notation "hide_term" constr(E) "in" hyp(H) :=
change E with (@ltac_something _ E) in H.
Tactic Notation "show_term" constr(E) "in" hyp(H) :=
change (@ltac_something _ E) with E in H.
Tactic Notation "show_term" "in" hyp(H) :=
unfold ltac_something in H.




Tactic Notation "show_unfold" constr(R1) :=
unfold R1; show_def.
Tactic Notation "show_unfold" constr(R1) "," constr(R2) :=
unfold R1, R2; show_def.






Ltac sort_tactic :=
try match goal with H: ?T |- _ =>
match type of T with Prop =>
generalizes H; (try sort_tactic); intro
end end.

Tactic Notation "sort" :=
sort_tactic.






Tactic Notation "clears" ident(X1) :=
let rec doit _ :=
match goal with
| H:context[X1] |- _ => clear H; try (doit tt)
| _ => clear X1
end in doit tt.
Tactic Notation "clears" ident(X1) ident(X2) :=
clears X1; clears X2.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) :=
clears X1; clears X2; clears X3.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) :=
clears X1; clears X2; clears X3; clears X4.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
ident(X5) :=
clears X1; clears X2; clears X3; clears X4; clears X5.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
ident(X5) ident(X6) :=
clears X1; clears X2; clears X3; clears X4; clears X5; clears X6.




Ltac clears_tactic :=
match goal with H: ?T |- _ =>
match type of T with
| Prop => generalizes H; (try clears_tactic); intro
| ?TT => clear H; (try clears_tactic)
| ?TT => generalizes H; (try clears_tactic); intro
end end.

Tactic Notation "clears" :=
clears_tactic.



Ltac clears_or_generalizes_all_core :=
repeat match goal with H: _ |- _ =>
first [ clear H | generalizes H] end.

Tactic Notation "clears_all" :=
generalize ltac_mark;
clears_or_generalizes_all_core;
intro_until_mark.



Ltac clears_but_core cont :=
generalize ltac_mark;
cont tt;
clears_or_generalizes_all_core;
intro_until_mark.

Tactic Notation "clears_but" :=
clears_but_core ltac:(fun _ => idtac).
Tactic Notation "clears_but" ident(H1) :=
clears_but_core ltac:(fun _ => gen H1).
Tactic Notation "clears_but" ident(H1) ident(H2) :=
clears_but_core ltac:(fun _ => gen H1 H2).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) :=
clears_but_core ltac:(fun _ => gen H1 H2 H3).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) ident(H4) :=
clears_but_core ltac:(fun _ => gen H1 H2 H3 H4).
Tactic Notation "clears_but" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5) :=
clears_but_core ltac:(fun _ => gen H1 H2 H3 H4 H5).

Lemma demo_clears_all_and_clears_but :
forall x y:nat, y < 2 -> x = x -> x >= 2 -> x < 3 -> True.
Proof using. hammer_hook "LibTactics" "LibTactics.demo_clears_all_and_clears_but".
introv M1 M2 M3. dup 6.

clears_all. auto.

clears_but M3. auto.
clears_but y. auto.
clears_but x. auto.
clears_but M2 M3. auto.
clears_but x y. auto.
Qed.



Tactic Notation "clears_last" :=
match goal with H: ?T |- _ => clear H end.

Ltac clears_last_base N :=
match number_to_nat N with
| 0 => idtac
| S ?p => clears_last; clears_last_base p
end.

Tactic Notation "clears_last" constr(N) :=
clears_last_base N.









Tactic Notation "skip" :=
admit.



Tactic Notation "demo" :=
skip.



Tactic Notation "admits" simple_intropattern(I) ":" constr(T) :=
asserts I: T; [ skip | ].
Tactic Notation "admits" ":" constr(T) :=
let H := fresh "TEMP" in admits H: T.
Tactic Notation "admits" "~" ":" constr(T) :=
admits: T; auto_tilde.
Tactic Notation "admits" "*" ":" constr(T) :=
admits: T; auto_star.



Tactic Notation "admit_cuts" constr(T) :=
cuts: T; [ skip | ].



Tactic Notation "admit_goal" ident(H) :=
match goal with |- ?G => admits H: G end.

Tactic Notation "admit_goal" :=
let IH := fresh "IH" in admit_goal IH.



Tactic Notation "admit_rewrite" constr(T) :=
let M := fresh "TEMP" in admits M: T; rewrite M; clear M.



Tactic Notation "admit_rewrite" constr(T) "in" hyp(H) :=
let M := fresh "TEMP" in admits M: T; rewrite M in H; clear M.



Tactic Notation "admit_rewrite_all" constr(T) :=
let M := fresh "TEMP" in admits M: T; rewrite_all M; clear M.



Inductive ltac_goal_to_discard := ltac_goal_to_discard_intro.

Ltac forwards_nounfold_admit_sides_then S cont :=
let MARK := fresh "TEMP" in
generalize ltac_goal_to_discard_intro;
intro MARK;
forwards_nounfold_then S ltac:(fun K =>
clear MARK;
cont K);
match goal with
| MARK: ltac_goal_to_discard |- _ => skip
| _ => idtac
end.








Module LibTacticsCompatibility.
Tactic Notation "apply" "*" constr(H) :=
sapply H; auto_star.
Tactic Notation "subst" "*" :=
subst; auto_star.
End LibTacticsCompatibility.

Open Scope nat_scope.



