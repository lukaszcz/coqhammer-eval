From Hammer Require Import Hammer.










From VFA Require Import Perm.

Module Type PRIQUEUE.
Parameter priqueue: Type.
Definition key := nat.

Parameter empty: priqueue.
Parameter insert: key -> priqueue -> priqueue.
Parameter delete_max: priqueue -> option (key * priqueue).
Parameter merge: priqueue -> priqueue -> priqueue.

Parameter priq: priqueue -> Prop.
Parameter Abs: priqueue -> list key -> Prop.
Axiom can_relate:  forall p, priq p -> exists al, Abs p al.
Axiom abs_perm: forall p al bl,
priq p -> Abs p al -> Abs p bl -> Permutation al bl.
Axiom  empty_priq: priq empty.
Axiom empty_relate:  Abs empty nil.
Axiom insert_priq: forall k p, priq p -> priq (insert k p).
Axiom insert_relate:
forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
Axiom delete_max_None_relate:
forall p, priq p -> (Abs p nil <-> delete_max p = None).
Axiom delete_max_Some_priq:
forall p q k, priq p -> delete_max p = Some(k,q) -> priq q.
Axiom delete_max_Some_relate:
forall (p q: priqueue) k (pl ql: list key), priq p ->
Abs p pl ->
delete_max p = Some (k,q) ->
Abs q ql ->
Permutation pl (k::ql) /\ Forall (ge k) ql.
Axiom merge_priq: forall p q, priq p -> priq q -> priq (merge p q).
Axiom merge_relate:
forall p q pl ql al,
priq p -> priq q ->
Abs p pl -> Abs q ql -> Abs (merge p q) al ->
Permutation al (pl++ql).
End PRIQUEUE.






Module List_Priqueue <: PRIQUEUE.










Fixpoint select (i: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (i, nil)
|  h::t => if i >=? h
then let (j, l') := select i t in (j, h::l')
else let (j,l') := select h t in (j, i::l')
end.



Lemma select_perm: forall i l,
let (j,r) := select i l in
Permutation (i::l) (j::r).
Proof. hammer_hook "Priqueue" "Priqueue.List_Priqueue.select_perm".
intros i l; revert i.
induction l; intros; simpl in *.
Admitted.

Lemma select_biggest_aux:
forall i al j bl,
Forall (fun x => j >= x) bl ->
select i al = (j,bl) ->
j >= i.
Proof. hammer_hook "Priqueue" "Priqueue.List_Priqueue.select_biggest_aux".
Admitted.

Theorem select_biggest:
forall i al j bl, select i al = (j,bl) ->
Forall (fun x => j >= x) bl.
Proof. hammer_hook "Priqueue" "Priqueue.List_Priqueue.select_biggest".
intros i al; revert i; induction al; intros; simpl in *.
admit.
bdestruct (i >=? a).
*
destruct (select i al) eqn:?H.
Admitted.





Definition key := nat.

Definition priqueue := list key.

Definition empty : priqueue := nil.
Definition insert  (k: key)(p: priqueue) := k::p.
Definition delete_max (p: priqueue) :=
match p with
| i::p' => Some (select i p')
| nil => None
end.
Definition merge (p q: priqueue) : priqueue := p++q.









Definition priq (p: priqueue) := True.



Inductive Abs':  priqueue -> list key -> Prop :=
Abs_intro: forall p, Abs' p p.

Definition Abs := Abs'.




Lemma can_relate : forall p, priq p -> exists al, Abs p al.
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.can_relate".
intros. exists p; constructor.
Qed.



Lemma abs_perm: forall p al bl,
priq p -> Abs p al -> Abs p bl -> Permutation al bl.
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.abs_perm".
intros.
inv H0. inv H1. apply Permutation_refl.
Qed.




Lemma empty_priq: priq empty.
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.empty_priq". constructor. Qed.

Lemma empty_relate:  Abs empty nil.
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.empty_relate". constructor. Qed.

Lemma insert_priq: forall k p, priq p -> priq (insert k p).
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.insert_priq". intros; constructor. Qed.

Lemma insert_relate:
forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.insert_relate". intros. unfold insert. inv H0. constructor. Qed.

Lemma delete_max_Some_priq:
forall p q k, priq p -> delete_max p = Some(k,q) -> priq q.
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.delete_max_Some_priq". constructor. Qed.



Lemma delete_max_None_relate:
forall p, priq p ->
(Abs p nil <-> delete_max p = None).
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.delete_max_None_relate".
Admitted.

Lemma delete_max_Some_relate:
forall (p q: priqueue) k (pl ql: list key), priq p ->
Abs p pl ->
delete_max p = Some (k,q) ->
Abs q ql ->
Permutation pl (k::ql) /\ Forall (ge k) ql.
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.delete_max_Some_relate".
Admitted.

Lemma merge_priq:
forall p q, priq p -> priq q -> priq (merge p q).
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.merge_priq". intros. constructor. Qed.

Lemma merge_relate:
forall p q pl ql al,
priq p -> priq q ->
Abs p pl -> Abs q ql -> Abs (merge p q) al ->
Permutation al (pl++ql).
Proof. hammer_hook "Priqueue" "Priqueue.PRIQUEUE.merge_relate".
Admitted.


End List_Priqueue.

