From Hammer Require Import Hammer.










Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.









Definition total_map (A:Type) := nat -> A.



Definition t_empty {A:Type} (v : A) : total_map A :=
(fun _ => v).



Definition t_update {A:Type} (m : total_map A)
(x : nat) (v : A) :=
fun x' => if beq_nat x x' then v else m x'.



Definition examplemap :=
t_update (t_update (t_empty false) 1 false) 3 true.



Example update_example1 : examplemap 0 = false.
Proof. hammer_hook "Maps" "Maps.update_example1". reflexivity. Qed.

Example update_example2 : examplemap 1 = false.
Proof. hammer_hook "Maps" "Maps.update_example2". reflexivity. Qed.

Example update_example3 : examplemap 2 = false.
Proof. hammer_hook "Maps" "Maps.update_example3". reflexivity. Qed.

Example update_example4 : examplemap 3 = true.
Proof. hammer_hook "Maps" "Maps.update_example4". reflexivity. Qed.





Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof. hammer_hook "Maps" "Maps.t_apply_empty".
Admitted.





Lemma t_update_eq : forall A (m: total_map A) x v,
(t_update m x v) x = v.
Proof. hammer_hook "Maps" "Maps.t_update_eq".
Admitted.





Theorem t_update_neq : forall (X:Type) v x1 x2
(m : total_map X),
x1 <> x2 ->
(t_update m x1 v) x2 = m x2.
Proof. hammer_hook "Maps" "Maps.t_update_neq".
Admitted.





Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
t_update (t_update m x v1) x v2
= t_update m x v2.
Proof. hammer_hook "Maps" "Maps.t_update_shadow".
Admitted.







Lemma beq_idP : forall x y, reflect (x = y) (beq_nat x y).
Proof. hammer_hook "Maps" "Maps.beq_idP".
Admitted.







Theorem t_update_same : forall X x (m : total_map X),
t_update m x (m x) = m.
Proof. hammer_hook "Maps" "Maps.t_update_same".
Admitted.





Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
(m : total_map X),
x2 <> x1 ->
(t_update (t_update m x2 v2) x1 v1)
= (t_update (t_update m x1 v1) x2 v2).
Proof. hammer_hook "Maps" "Maps.t_update_permute".
Admitted.







Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
t_empty None.

Definition update {A:Type} (m : partial_map A)
(x : nat) (v : A) :=
t_update m x (Some v).



Lemma apply_empty : forall A x, @empty A x = None.
Proof. hammer_hook "Maps" "Maps.apply_empty".
intros. unfold empty. rewrite t_apply_empty.
reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
(update m x v) x = Some v.
Proof. hammer_hook "Maps" "Maps.update_eq".
intros. unfold update. rewrite t_update_eq.
reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
(m : partial_map X),
x2 <> x1 ->
(update m x2 v) x1 = m x1.
Proof. hammer_hook "Maps" "Maps.update_neq".
intros X v x1 x2 m H.
unfold update. rewrite t_update_neq. reflexivity.
apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
update (update m x v1) x v2 = update m x v2.
Proof. hammer_hook "Maps" "Maps.update_shadow".
intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
m x = Some v ->
update m x v = m.
Proof. hammer_hook "Maps" "Maps.update_same".
intros X v x m H. unfold update. rewrite <- H.
apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
(m : partial_map X),
x2 <> x1 ->
(update (update m x2 v2) x1 v1)
= (update (update m x1 v1) x2 v2).
Proof. hammer_hook "Maps" "Maps.update_permute".
intros X v1 v2 x1 x2 m. unfold update.
apply t_update_permute.
Qed.



