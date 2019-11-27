From Hammer Require Import Hammer.

Require Import ExtLib.Core.Type.

Global Instance type_Prop : type Prop :=
{ equal := iff
; proper := fun _ => True
}.

Global Instance typeOk_Prop : typeOk type_Prop.
Proof. hammer_hook "Prop" "Prop.typeOk_Prop".
constructor; compute; firstorder.
Qed.



Lemma and_True_iff : forall P, (P /\ True) <-> P.
Proof. hammer_hook "Prop" "Prop.and_True_iff". intuition. Qed.

Lemma and_and_iff : forall P, (P /\ P) <-> P.
Proof. hammer_hook "Prop" "Prop.and_and_iff". intuition. Qed.

Lemma and_assoc : forall P Q R, (P /\ Q /\ R) <-> ((P /\ Q) /\ R).
Proof. hammer_hook "Prop" "Prop.and_assoc". intuition. Qed.

Lemma and_comm : forall P Q, (P /\ Q) <-> (Q /\ P).
Proof. hammer_hook "Prop" "Prop.and_comm". intuition. Qed.

Lemma and_False_iff : forall P, (P /\ False) <-> False.
Proof. hammer_hook "Prop" "Prop.and_False_iff". intuition. Qed.

Lemma and_cancel
: forall P Q R : Prop, (P -> (Q <-> R)) -> ((P /\ Q) <-> (P /\ R)).
Proof. hammer_hook "Prop" "Prop.and_cancel". intuition. Qed.

Lemma and_iff
: forall P Q R S : Prop,
(P <-> R) ->
(P -> (Q <-> S)) ->
((P /\ Q) <-> (R /\ S)).
Proof. hammer_hook "Prop" "Prop.and_iff". clear; intuition. Qed.


Lemma or_False_iff : forall P, (P \/ False) <-> P.
Proof. hammer_hook "Prop" "Prop.or_False_iff". intuition. Qed.

Lemma or_or_iff : forall P, (P \/ P) <-> P.
Proof. hammer_hook "Prop" "Prop.or_or_iff". intuition. Qed.

Lemma or_assoc : forall P Q R, (P \/ Q \/ R) <-> ((P \/ Q) \/ R).
Proof. hammer_hook "Prop" "Prop.or_assoc". intuition. Qed.

Lemma or_comm : forall P Q, (P \/ Q) <-> (Q \/ P).
Proof. hammer_hook "Prop" "Prop.or_comm". intuition. Qed.

Lemma or_True_iff : forall P, (P \/ True) <-> True.
Proof. hammer_hook "Prop" "Prop.or_True_iff". intuition. Qed.


Lemma impl_True_iff : forall (P : Prop), (True -> P) <-> P.
Proof. hammer_hook "Prop" "Prop.impl_True_iff".
clear; intros; tauto.
Qed.

Lemma impl_iff
: forall P Q R S : Prop,
(P <-> R) ->
(P -> (Q <-> S)) ->
((P -> Q) <-> (R -> S)).
Proof. hammer_hook "Prop" "Prop.impl_iff". clear. intuition. Qed.

Lemma impl_eq : forall (P Q : Prop), P = Q -> (P -> Q).
Proof. hammer_hook "Prop" "Prop.impl_eq". clear. intros; subst; auto. Qed.

Lemma uncurry : forall (P Q R : Prop),
(P /\ Q -> R) <-> (P -> Q -> R).
Proof. hammer_hook "Prop" "Prop.uncurry". clear. tauto. Qed.



Lemma forall_iff : forall T P Q,
(forall x,
P x <-> Q x) ->
((forall x : T, P x) <-> (forall x : T, Q x)).
Proof. hammer_hook "Prop" "Prop.forall_iff".
intros. setoid_rewrite H. reflexivity.
Qed.

Lemma forall_impl : forall {T} (P Q : T -> Prop),
(forall x, P x -> Q x) ->
(forall x, P x) -> (forall x, Q x).
Proof. hammer_hook "Prop" "Prop.forall_impl".
clear. intuition.
Qed.



Lemma exists_iff : forall T P Q,
(forall x,
P x <-> Q x) ->
((exists x : T, P x) <-> (exists x : T, Q x)).
Proof. hammer_hook "Prop" "Prop.exists_iff".
intros. setoid_rewrite H. reflexivity.
Qed.

Lemma exists_impl : forall {T} (P Q : T -> Prop),
(forall x, P x -> Q x) ->
(exists x, P x) -> (exists x, Q x).
Proof. hammer_hook "Prop" "Prop.exists_impl".
clear. intuition.
destruct H0; eauto.
Qed.

Lemma iff_eq : forall (P Q : Prop), P = Q -> (P <-> Q).
Proof. hammer_hook "Prop" "Prop.iff_eq". clear. intros; subst; reflexivity. Qed.
