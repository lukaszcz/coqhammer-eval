From Hammer Require Import Hammer.









Require Import Orders OrdersTac OrdersFacts Setoid Morphisms Basics.





Module Type HasMax (Import E:EqLe').
Parameter Inline max : t -> t -> t.
Parameter max_l : forall x y, y<=x -> max x y == x.
Parameter max_r : forall x y, x<=y -> max x y == y.
End HasMax.

Module Type HasMin (Import E:EqLe').
Parameter Inline min : t -> t -> t.
Parameter min_l : forall x y, x<=y -> min x y == x.
Parameter min_r : forall x y, y<=x -> min x y == y.
End HasMin.

Module Type HasMinMax (E:EqLe) := HasMax E <+ HasMin E.




Definition gmax {A} (cmp : A->A->comparison) x y :=
match cmp x y with Lt => y | _ => x end.
Definition gmin {A} (cmp : A->A->comparison) x y :=
match cmp x y with Gt => y | _ => x end.

Module GenericMinMax (Import O:OrderedTypeFull') <: HasMinMax O.

Definition max := gmax O.compare.
Definition min := gmin O.compare.

Lemma ge_not_lt x y : y<=x -> x<y -> False.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.GenericMinMax.ge_not_lt".  
intros H H'.
apply (StrictOrder_Irreflexive x).
rewrite le_lteq in *; destruct H as [H|H].
transitivity y; auto.
rewrite H in H'; auto.
Qed.

Lemma max_l x y : y<=x -> max x y == x.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.HasMax.max_l".  
intros. unfold max, gmax. case compare_spec; auto with relations.
intros; elim (ge_not_lt x y); auto.
Qed.

Lemma max_r x y : x<=y -> max x y == y.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.HasMax.max_r".  
intros. unfold max, gmax. case compare_spec; auto with relations.
intros; elim (ge_not_lt y x); auto.
Qed.

Lemma min_l x y : x<=y -> min x y == x.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.HasMin.min_l".  
intros. unfold min, gmin. case compare_spec; auto with relations.
intros; elim (ge_not_lt y x); auto.
Qed.

Lemma min_r x y : y<=x -> min x y == y.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.HasMin.min_r".  
intros. unfold min, gmin. case compare_spec; auto with relations.
intros; elim (ge_not_lt x y); auto.
Qed.

End GenericMinMax.




Module MinMaxLogicalProperties (Import O:TotalOrder')(Import M:HasMinMax O).
Module Import Private_Tac := !MakeOrderTac O O.



Lemma max_spec n m :
(n < m /\ max n m == m) \/ (m <= n /\ max n m == n).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_spec".  
destruct (lt_total n m); [left|right].
- split; auto. apply max_r. rewrite le_lteq; auto.
- assert (m <= n) by (rewrite le_lteq; intuition).
split; auto. now apply max_l.
Qed.



Lemma max_spec_le n m :
(n <= m /\ max n m == m) \/ (m <= n /\ max n m == n).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_spec_le".  
destruct (max_spec n m); [left|right]; intuition; order.
Qed.

Instance : Proper (eq==>eq==>iff) le.
Proof. repeat red. intuition order. Qed.

Instance max_compat : Proper (eq==>eq==>eq) max.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_compat".  
intros x x' Hx y y' Hy.
assert (H1 := max_spec x y). assert (H2 := max_spec x' y').
set (m := max x y) in *; set (m' := max x' y') in *; clearbody m m'.
rewrite <- Hx, <- Hy in *.
destruct (lt_total x y); intuition order.
Qed.



Lemma max_unicity n m p :
((n < m /\ p == m) \/ (m <= n /\ p == n)) -> p == max n m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_unicity".  
assert (Hm := max_spec n m).
destruct (lt_total n m); intuition; order.
Qed.

Lemma max_unicity_ext f :
(forall n m, (n < m /\ f n m == m) \/ (m <= n /\ f n m == n)) ->
(forall n m, f n m == max n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_unicity_ext".  
intros. apply max_unicity; auto.
Qed.



Lemma max_mono f :
(Proper (eq ==> eq) f) ->
(Proper (le ==> le) f) ->
forall x y, max (f x) (f y) == f (max x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_mono".  
intros Eqf Lef x y.
destruct (max_spec x y) as [(H,E)|(H,E)]; rewrite E;
destruct (max_spec (f x) (f y)) as [(H',E')|(H',E')]; auto.
assert (f x <= f y) by (apply Lef; order). order.
assert (f y <= f x) by (apply Lef; order). order.
Qed.



Lemma max_id n : max n n == n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_id".  
apply max_l; order.
Qed.

Notation max_idempotent := max_id (only parsing).

Lemma max_assoc m n p : max m (max n p) == max (max m n) p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_assoc".  
destruct (max_spec n p) as [(H,E)|(H,E)]; rewrite E;
destruct (max_spec m n) as [(H',E')|(H',E')]; rewrite E', ?E; try easy.
- apply max_r; order.
- symmetry. apply max_l; order.
Qed.

Lemma max_comm n m : max n m == max m n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_comm".  
destruct (max_spec m n) as [(H,E)|(H,E)]; rewrite E;
(apply max_r || apply max_l); order.
Qed.

Ltac solve_max :=
match goal with |- context [max ?n ?m] =>
destruct (max_spec n m); intuition; order
end.



Lemma le_max_l n m : n <= max n m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.le_max_l".   solve_max. Qed.

Lemma le_max_r n m : m <= max n m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.le_max_r".   solve_max. Qed.

Lemma max_l_iff n m : max n m == n <-> m <= n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_l_iff".   solve_max. Qed.

Lemma max_r_iff n m : max n m == m <-> n <= m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_r_iff".   solve_max. Qed.

Lemma max_le n m p : p <= max n m -> p <= n \/ p <= m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_le".  
destruct (max_spec n m); [right|left]; intuition; order.
Qed.

Lemma max_le_iff n m p : p <= max n m <-> p <= n \/ p <= m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_le_iff".   split. apply max_le. solve_max. Qed.

Lemma max_lt_iff n m p : p < max n m <-> p < n \/ p < m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_lt_iff".  
destruct (max_spec n m); intuition;
order || (right; order) || (left; order).
Qed.

Lemma max_lub_l n m p : max n m <= p -> n <= p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_lub_l".   solve_max. Qed.

Lemma max_lub_r n m p : max n m <= p -> m <= p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_lub_r".   solve_max. Qed.

Lemma max_lub n m p : n <= p -> m <= p -> max n m <= p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_lub".   solve_max. Qed.

Lemma max_lub_iff n m p : max n m <= p <-> n <= p /\ m <= p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_lub_iff".   solve_max. Qed.

Lemma max_lub_lt n m p : n < p -> m < p -> max n m < p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_lub_lt".   solve_max. Qed.

Lemma max_lub_lt_iff n m p : max n m < p <-> n < p /\ m < p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_lub_lt_iff".   solve_max. Qed.

Lemma max_le_compat_l n m p : n <= m -> max p n <= max p m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_le_compat_l".   intros. apply max_lub_iff. solve_max. Qed.

Lemma max_le_compat_r n m p : n <= m -> max n p <= max m p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_le_compat_r".   intros. apply max_lub_iff. solve_max. Qed.

Lemma max_le_compat n m p q : n <= m -> p <= q -> max n p <= max m q.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_le_compat".  
intros Hnm Hpq.
assert (LE := max_le_compat_l _ _ m Hpq).
assert (LE' := max_le_compat_r _ _ p Hnm).
order.
Qed.



Lemma min_spec n m :
(n < m /\ min n m == n) \/ (m <= n /\ min n m == m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_spec".  
destruct (lt_total n m); [left|right].
- split; auto. apply min_l. rewrite le_lteq; auto.
- assert (m <= n) by (rewrite le_lteq; intuition).
split; auto. now apply min_r.
Qed.

Lemma min_spec_le n m :
(n <= m /\ min n m == n) \/ (m <= n /\ min n m == m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_spec_le".  
destruct (min_spec n m); [left|right]; intuition; order.
Qed.

Instance min_compat : Proper (eq==>eq==>eq) min.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_compat".  
intros x x' Hx y y' Hy.
assert (H1 := min_spec x y). assert (H2 := min_spec x' y').
set (m := min x y) in *; set (m' := min x' y') in *; clearbody m m'.
rewrite <- Hx, <- Hy in *.
destruct (lt_total x y); intuition order.
Qed.

Lemma min_unicity n m p :
((n < m /\ p == n) \/ (m <= n /\ p == m)) ->  p == min n m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_unicity".  
assert (Hm := min_spec n m).
destruct (lt_total n m); intuition; order.
Qed.

Lemma min_unicity_ext f :
(forall n m, (n < m /\ f n m == n)  \/ (m <= n /\ f n m == m)) ->
(forall n m, f n m == min n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_unicity_ext".  
intros. apply min_unicity; auto.
Qed.

Lemma min_mono f :
(Proper (eq ==> eq) f) ->
(Proper (le ==> le) f) ->
forall x y, min (f x) (f y) == f (min x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_mono".  
intros Eqf Lef x y.
destruct (min_spec x y) as [(H,E)|(H,E)]; rewrite E;
destruct (min_spec (f x) (f y)) as [(H',E')|(H',E')]; auto.
assert (f x <= f y) by (apply Lef; order). order.
assert (f y <= f x) by (apply Lef; order). order.
Qed.

Lemma min_id n : min n n == n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_id".  
apply min_l; order.
Qed.

Notation min_idempotent := min_id (only parsing).

Lemma min_assoc m n p : min m (min n p) == min (min m n) p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_assoc".  
destruct (min_spec n p) as [(H,E)|(H,E)]; rewrite E;
destruct (min_spec m n) as [(H',E')|(H',E')]; rewrite E', ?E; try easy.
- symmetry. apply min_l; order.
- apply min_r; order.
Qed.

Lemma min_comm n m : min n m == min m n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_comm".  
destruct (min_spec m n) as [(H,E)|(H,E)]; rewrite E;
(apply min_r || apply min_l); order.
Qed.

Ltac solve_min :=
match goal with |- context [min ?n ?m] =>
destruct (min_spec n m); intuition; order
end.

Lemma le_min_r n m : min n m <= m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.le_min_r".   solve_min. Qed.

Lemma le_min_l n m : min n m <= n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.le_min_l".   solve_min. Qed.

Lemma min_l_iff n m : min n m == n <-> n <= m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_l_iff".   solve_min. Qed.

Lemma min_r_iff n m : min n m == m <-> m <= n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_r_iff".   solve_min. Qed.

Lemma min_le n m p : min n m <= p -> n <= p \/ m <= p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_le".  
destruct (min_spec n m); [left|right]; intuition; order.
Qed.

Lemma min_le_iff n m p : min n m <= p <-> n <= p \/ m <= p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_le_iff".   split. apply min_le. solve_min. Qed.

Lemma min_lt_iff n m p : min n m < p <-> n < p \/ m < p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_lt_iff".  
destruct (min_spec n m); intuition;
order || (right; order) || (left; order).
Qed.

Lemma min_glb_l n m p : p <= min n m -> p <= n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_glb_l".   solve_min. Qed.

Lemma min_glb_r n m p : p <= min n m -> p <= m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_glb_r".   solve_min. Qed.

Lemma min_glb n m p : p <= n -> p <= m -> p <= min n m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_glb".   solve_min. Qed.

Lemma min_glb_iff n m p : p <= min n m <-> p <= n /\ p <= m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_glb_iff".   solve_min. Qed.

Lemma min_glb_lt n m p : p < n -> p < m -> p < min n m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_glb_lt".   solve_min. Qed.

Lemma min_glb_lt_iff n m p : p < min n m <-> p < n /\ p < m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_glb_lt_iff".   solve_min. Qed.

Lemma min_le_compat_l n m p : n <= m -> min p n <= min p m.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_le_compat_l".   intros. apply min_glb_iff. solve_min. Qed.

Lemma min_le_compat_r n m p : n <= m -> min n p <= min m p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_le_compat_r".   intros. apply min_glb_iff. solve_min. Qed.

Lemma min_le_compat n m p q : n <= m -> p <= q ->
min n p <= min m q.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_le_compat".  
intros Hnm Hpq.
assert (LE := min_le_compat_l _ _ m Hpq).
assert (LE' := min_le_compat_r _ _ p Hnm).
order.
Qed.



Lemma min_max_absorption n m : max n (min n m) == n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_max_absorption".  
intros.
destruct (min_spec n m) as [(C,E)|(C,E)]; rewrite E.
apply max_l. order.
destruct (max_spec n m); intuition; order.
Qed.

Lemma max_min_absorption n m : min n (max n m) == n.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_min_absorption".  
intros.
destruct (max_spec n m) as [(C,E)|(C,E)]; rewrite E.
destruct (min_spec n m) as [(C',E')|(C',E')]; auto. order.
apply min_l; auto. order.
Qed.



Lemma max_min_distr n m p :
max n (min m p) == min (max n m) (max n p).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_min_distr".  
symmetry. apply min_mono.
eauto with *.
repeat red; intros. apply max_le_compat_l; auto.
Qed.

Lemma min_max_distr n m p :
min n (max m p) == max (min n m) (min n p).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_max_distr".  
symmetry. apply max_mono.
eauto with *.
repeat red; intros. apply min_le_compat_l; auto.
Qed.



Lemma max_min_modular n m p :
max n (min m (max n p)) == min (max n m) (max n p).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_min_modular".  
rewrite <- max_min_distr.
destruct (max_spec n p) as [(C,E)|(C,E)]; rewrite E; auto with *.
destruct (min_spec m n) as [(C',E')|(C',E')]; rewrite E'.
rewrite 2 max_l; try order. rewrite min_le_iff; auto.
rewrite 2 max_l; try order. rewrite min_le_iff; auto.
Qed.

Lemma min_max_modular n m p :
min n (max m (min n p)) == max (min n m) (min n p).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_max_modular".  
intros. rewrite <- min_max_distr.
destruct (min_spec n p) as [(C,E)|(C,E)]; rewrite E; auto with *.
destruct (max_spec m n) as [(C',E')|(C',E')]; rewrite E'.
rewrite 2 min_l; try order. rewrite max_le_iff; right; order.
rewrite 2 min_l; try order. rewrite max_le_iff; auto.
Qed.



Lemma max_min_disassoc n m p :
min n (max m p) <= max (min n m) p.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_min_disassoc".  
intros. rewrite min_max_distr.
auto using max_le_compat_l, le_min_r.
Qed.



Lemma max_min_antimono f :
Proper (eq==>eq) f ->
Proper (le==>flip le) f ->
forall x y, max (f x) (f y) == f (min x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.max_min_antimono".  
intros Eqf Lef x y.
destruct (min_spec x y) as [(H,E)|(H,E)]; rewrite E;
destruct (max_spec (f x) (f y)) as [(H',E')|(H',E')]; auto.
assert (f y <= f x) by (apply Lef; order). order.
assert (f x <= f y) by (apply Lef; order). order.
Qed.

Lemma min_max_antimono f :
Proper (eq==>eq) f ->
Proper (le==>flip le) f ->
forall x y, min (f x) (f y) == f (max x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxLogicalProperties.min_max_antimono".  
intros Eqf Lef x y.
destruct (max_spec x y) as [(H,E)|(H,E)]; rewrite E;
destruct (min_spec (f x) (f y)) as [(H',E')|(H',E')]; auto.
assert (f y <= f x) by (apply Lef; order). order.
assert (f x <= f y) by (apply Lef; order). order.
Qed.

End MinMaxLogicalProperties.




Module MinMaxDecProperties (Import O:OrderedTypeFull')(Import M:HasMinMax O).



Lemma max_case_strong n m (P:t -> Type) :
(forall x y, x==y -> P x -> P y) ->
(m<=n -> P n) -> (n<=m -> P m) -> P (max n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxDecProperties.max_case_strong".  
intros Compat Hl Hr.
destruct (CompSpec2Type (compare_spec n m)) as [EQ|LT|GT].
assert (n<=m) by (rewrite le_lteq; auto).
apply (Compat m), Hr; auto. symmetry; apply max_r; auto.
assert (n<=m) by (rewrite le_lteq; auto).
apply (Compat m), Hr; auto. symmetry; apply max_r; auto.
assert (m<=n) by (rewrite le_lteq; auto).
apply (Compat n), Hl; auto. symmetry; apply max_l; auto.
Defined.

Lemma max_case n m (P:t -> Type) :
(forall x y, x == y -> P x -> P y) ->
P n -> P m -> P (max n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxDecProperties.max_case".   intros. apply max_case_strong; auto. Defined.



Lemma max_dec n m : {max n m == n} + {max n m == m}.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxDecProperties.max_dec".  
apply max_case; auto with relations.
intros x y H [E|E]; [left|right]; rewrite <-H; auto.
Defined.



Lemma min_case_strong n m (P:O.t -> Type) :
(forall x y, x == y -> P x -> P y) ->
(n<=m -> P n) -> (m<=n -> P m) -> P (min n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxDecProperties.min_case_strong".  
intros Compat Hl Hr.
destruct (CompSpec2Type (compare_spec n m)) as [EQ|LT|GT].
assert (n<=m) by (rewrite le_lteq; auto).
apply (Compat n), Hl; auto. symmetry; apply min_l; auto.
assert (n<=m) by (rewrite le_lteq; auto).
apply (Compat n), Hl; auto. symmetry; apply min_l; auto.
assert (m<=n) by (rewrite le_lteq; auto).
apply (Compat m), Hr; auto. symmetry; apply min_r; auto.
Defined.

Lemma min_case n m (P:O.t -> Type) :
(forall x y, x == y -> P x -> P y) ->
P n -> P m -> P (min n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxDecProperties.min_case".   intros. apply min_case_strong; auto. Defined.

Lemma min_dec n m : {min n m == n} + {min n m == m}.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxDecProperties.min_dec".  
intros. apply min_case; auto with relations.
intros x y H [E|E]; [left|right]; rewrite <- E; auto with relations.
Defined.

End MinMaxDecProperties.

Module MinMaxProperties (Import O:OrderedTypeFull')(Import M:HasMinMax O).
Module OT := OTF_to_TotalOrder O.
Include MinMaxLogicalProperties OT M.
Include MinMaxDecProperties O M.
Definition max_l := max_l.
Definition max_r := max_r.
Definition min_l := min_l.
Definition min_r := min_r.
Notation max_monotone := max_mono.
Notation min_monotone := min_mono.
Notation max_min_antimonotone := max_min_antimono.
Notation min_max_antimonotone := min_max_antimono.
End MinMaxProperties.




Module UsualMinMaxLogicalProperties
(Import O:UsualTotalOrder')(Import M:HasMinMax O).

Include MinMaxLogicalProperties O M.

Lemma max_monotone f : Proper (le ==> le) f ->
forall x y, max (f x) (f y) = f (max x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxProperties.max_monotone".   intros; apply max_mono; auto. congruence. Qed.

Lemma min_monotone f : Proper (le ==> le) f ->
forall x y, min (f x) (f y) = f (min x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxProperties.min_monotone".   intros; apply min_mono; auto. congruence. Qed.

Lemma min_max_antimonotone f : Proper (le ==> flip le) f ->
forall x y, min (f x) (f y) = f (max x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxProperties.min_max_antimonotone".   intros; apply min_max_antimono; auto. congruence. Qed.

Lemma max_min_antimonotone f : Proper (le ==> flip le) f ->
forall x y, max (f x) (f y) = f (min x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.MinMaxProperties.max_min_antimonotone".   intros; apply max_min_antimono; auto. congruence. Qed.

End UsualMinMaxLogicalProperties.


Module UsualMinMaxDecProperties
(Import O:UsualOrderedTypeFull')(Import M:HasMinMax O).

Module Import Private_Dec := MinMaxDecProperties O M.

Lemma max_case_strong : forall n m (P:t -> Type),
(m<=n -> P n) -> (n<=m -> P m) -> P (max n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.UsualMinMaxDecProperties.max_case_strong".   intros; apply max_case_strong; auto. congruence. Defined.

Lemma max_case : forall n m (P:t -> Type),
P n -> P m -> P (max n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.UsualMinMaxDecProperties.max_case".   intros; apply max_case_strong; auto. Defined.

Lemma max_dec : forall n m, {max n m = n} + {max n m = m}.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.UsualMinMaxDecProperties.max_dec".   exact max_dec. Defined.

Lemma min_case_strong : forall n m (P:O.t -> Type),
(n<=m -> P n) -> (m<=n -> P m) -> P (min n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.UsualMinMaxDecProperties.min_case_strong".   intros; apply min_case_strong; auto. congruence. Defined.

Lemma min_case : forall n m (P:O.t -> Type),
P n -> P m -> P (min n m).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.UsualMinMaxDecProperties.min_case".   intros. apply min_case_strong; auto. Defined.

Lemma min_dec : forall n m, {min n m = n} + {min n m = m}.
Proof. hammer_hook "GenericMinMax" "GenericMinMax.UsualMinMaxDecProperties.min_dec".   exact min_dec. Defined.

End UsualMinMaxDecProperties.

Module UsualMinMaxProperties
(Import O:UsualOrderedTypeFull')(Import M:HasMinMax O).
Module OT := OTF_to_TotalOrder O.
Include UsualMinMaxLogicalProperties OT M.
Include UsualMinMaxDecProperties O M.
Definition max_l := max_l.
Definition max_r := max_r.
Definition min_l := min_l.
Definition min_r := min_r.
End UsualMinMaxProperties.




Module TOMaxEqDec_to_Compare
(Import O:TotalOrder')(Import M:HasMax O)(Import E:HasEqDec O) <: HasCompare O.

Definition compare x y :=
if eq_dec x y then Eq
else if eq_dec (M.max x y) y then Lt else Gt.

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof. hammer_hook "GenericMinMax" "GenericMinMax.TOMaxEqDec_to_Compare.compare_spec".  
intros; unfold compare; repeat destruct eq_dec; auto; constructor.
destruct (lt_total x y); auto.
absurd (x==y); auto. transitivity (max x y); auto.
symmetry. apply max_l. rewrite le_lteq; intuition.
destruct (lt_total y x); auto.
absurd (max x y == y); auto. apply max_r; rewrite le_lteq; intuition.
Qed.

End TOMaxEqDec_to_Compare.

Module TOMaxEqDec_to_OTF (O:TotalOrder)(M:HasMax O)(E:HasEqDec O)
<: OrderedTypeFull
:= O <+ E <+ TOMaxEqDec_to_Compare O M E.




