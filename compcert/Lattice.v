From Hammer Require Import Hammer.


















From compcert Require Import Coqlib.
From compcert Require Import Maps.
Require Import FSets.


Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.





Module Type SEMILATTICE.

Parameter t: Type.
Parameter eq: t -> t -> Prop.
Axiom eq_refl: forall x, eq x x.
Axiom eq_sym: forall x y, eq x y -> eq y x.
Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Parameter beq: t -> t -> bool.
Axiom beq_correct: forall x y, beq x y = true -> eq x y.
Parameter ge: t -> t -> Prop.
Axiom ge_refl: forall x y, eq x y -> ge x y.
Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Parameter bot: t.
Axiom ge_bot: forall x, ge x bot.
Parameter lub: t -> t -> t.
Axiom ge_lub_left: forall x y, ge (lub x y) x.
Axiom ge_lub_right: forall x y, ge (lub x y) y.

End SEMILATTICE.



Module Type SEMILATTICE_WITH_TOP.

Include SEMILATTICE.
Parameter top: t.
Axiom ge_top: forall x, ge top x.

End SEMILATTICE_WITH_TOP.



Set Implicit Arguments.



Module LPMap1(L: SEMILATTICE) <: SEMILATTICE.

Definition t := PTree.t L.t.

Definition get (p: positive) (x: t) : L.t :=
match x!p with None => L.bot | Some x => x end.

Definition set (p: positive) (v: L.t) (x: t) : t :=
if L.beq v L.bot
then PTree.remove p x
else PTree.set p v x.

Lemma gsspec:
forall p v x q,
L.eq (get q (set p v x)) (if peq q p then v else get q x).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.gsspec".
intros. unfold set, get.
destruct (L.beq v L.bot) eqn:EBOT.
rewrite PTree.grspec. unfold PTree.elt_eq. destruct (peq q p).
apply L.eq_sym. apply L.beq_correct; auto.
apply L.eq_refl.
rewrite PTree.gsspec. destruct (peq q p); apply L.eq_refl.
Qed.

Definition eq (x y: t) : Prop :=
forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.eq_refl".
unfold eq; intros. apply L.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.eq_sym".
unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.eq_trans".
unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool := PTree.beq L.beq x y.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.beq_correct".
unfold beq; intros; red; intros. unfold get.
rewrite PTree.beq_correct in H. specialize (H p).
destruct (x!p); destruct (y!p); intuition.
apply L.beq_correct; auto.
apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.ge_refl".
unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.ge_trans".
unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot : t := PTree.empty _.

Lemma get_bot: forall p, get p bot = L.bot.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.get_bot".
unfold bot, get; intros; simpl. rewrite PTree.gempty. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.ge_bot".
unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.



Section COMBINE.

Variable f: option L.t -> option L.t -> option L.t.
Hypothesis f_none_none: f None None = None.

Definition opt_eq (ox oy: option L.t) : Prop :=
match ox, oy with
| None, None => True
| Some x, Some y => L.eq x y
| _, _ => False
end.

Lemma opt_eq_refl: forall ox, opt_eq ox ox.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.opt_eq_refl".
intros. unfold opt_eq. destruct ox. apply L.eq_refl. auto.
Qed.

Lemma opt_eq_sym: forall ox oy, opt_eq ox oy -> opt_eq oy ox.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.opt_eq_sym".
unfold opt_eq. destruct ox; destruct oy; auto. apply L.eq_sym.
Qed.

Lemma opt_eq_trans: forall ox oy oz, opt_eq ox oy -> opt_eq oy oz -> opt_eq ox oz.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.opt_eq_trans".
unfold opt_eq. destruct ox; destruct oy; destruct oz; intuition.
eapply L.eq_trans; eauto.
Qed.

Definition opt_beq (ox oy: option L.t) : bool :=
match ox, oy with
| None, None => true
| Some x, Some y => L.beq x y
| _, _ => false
end.

Lemma opt_beq_correct:
forall ox oy, opt_beq ox oy = true -> opt_eq ox oy.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.opt_beq_correct".
unfold opt_beq, opt_eq. destruct ox; destruct oy; try congruence.
intros. apply L.beq_correct; auto.
auto.
Qed.

Definition tree_eq (m1 m2: PTree.t L.t) : Prop :=
forall i, opt_eq (PTree.get i m1) (PTree.get i m2).

Lemma tree_eq_refl: forall m, tree_eq m m.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.tree_eq_refl". intros; red; intros; apply opt_eq_refl. Qed.

Lemma tree_eq_sym: forall m1 m2, tree_eq m1 m2 -> tree_eq m2 m1.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.tree_eq_sym". intros; red; intros; apply opt_eq_sym; auto. Qed.

Lemma tree_eq_trans: forall m1 m2 m3, tree_eq m1 m2 -> tree_eq m2 m3 -> tree_eq m1 m3.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.tree_eq_trans". intros; red; intros; apply opt_eq_trans with (PTree.get i m2); auto. Qed.

Lemma tree_eq_node:
forall l1 o1 r1 l2 o2 r2,
tree_eq l1 l2 -> tree_eq r1 r2 -> opt_eq o1 o2 ->
tree_eq (PTree.Node l1 o1 r1) (PTree.Node l2 o2 r2).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.tree_eq_node".
intros; red; intros. destruct i; simpl; auto.
Qed.

Lemma tree_eq_node':
forall l1 o1 r1 l2 o2 r2,
tree_eq l1 l2 -> tree_eq r1 r2 -> opt_eq o1 o2 ->
tree_eq (PTree.Node l1 o1 r1) (PTree.Node' l2 o2 r2).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.tree_eq_node'".
intros; red; intros. rewrite PTree.gnode'. apply tree_eq_node; auto.
Qed.

Lemma tree_eq_node'':
forall l1 o1 r1 l2 o2 r2,
tree_eq l1 l2 -> tree_eq r1 r2 -> opt_eq o1 o2 ->
tree_eq (PTree.Node' l1 o1 r1) (PTree.Node' l2 o2 r2).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.tree_eq_node''".
intros; red; intros. repeat rewrite PTree.gnode'. apply tree_eq_node; auto.
Qed.

Hint Resolve opt_beq_correct opt_eq_refl opt_eq_sym
tree_eq_refl tree_eq_sym
tree_eq_node tree_eq_node' tree_eq_node'' : combine.

Inductive changed: Type := Unchanged | Changed (m: PTree.t L.t).

Fixpoint combine_l (m : PTree.t L.t) {struct m} : changed :=
match m with
| PTree.Leaf =>
Unchanged
| PTree.Node l o r =>
let o' := f o None in
match combine_l l, combine_l r with
| Unchanged, Unchanged => if opt_beq o' o then Unchanged else Changed (PTree.Node' l o' r)
| Unchanged, Changed r' => Changed (PTree.Node' l o' r')
| Changed l', Unchanged => Changed (PTree.Node' l' o' r)
| Changed l', Changed r' => Changed (PTree.Node' l' o' r')
end
end.

Lemma combine_l_eq:
forall m,
tree_eq (match combine_l m with Unchanged => m | Changed m' => m' end)
(PTree.xcombine_l f m).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.combine_l_eq".
induction m; simpl.
auto with combine.
destruct (combine_l m1) as [ | l']; destruct (combine_l m2) as [ | r'];
auto with combine.
case_eq (opt_beq (f o None) o); auto with combine.
Qed.

Fixpoint combine_r (m : PTree.t L.t) {struct m} : changed :=
match m with
| PTree.Leaf =>
Unchanged
| PTree.Node l o r =>
let o' := f None o in
match combine_r l, combine_r r with
| Unchanged, Unchanged => if opt_beq o' o then Unchanged else Changed (PTree.Node' l o' r)
| Unchanged, Changed r' => Changed (PTree.Node' l o' r')
| Changed l', Unchanged => Changed (PTree.Node' l' o' r)
| Changed l', Changed r' => Changed (PTree.Node' l' o' r')
end
end.

Lemma combine_r_eq:
forall m,
tree_eq (match combine_r m with Unchanged => m | Changed m' => m' end)
(PTree.xcombine_r f m).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.combine_r_eq".
induction m; simpl.
auto with combine.
destruct (combine_r m1) as [ | l']; destruct (combine_r m2) as [ | r'];
auto with combine.
case_eq (opt_beq (f None o) o); auto with combine.
Qed.

Inductive changed2 : Type :=
| Same
| Same1
| Same2
| CC(m: PTree.t L.t).

Fixpoint xcombine (m1 m2 : PTree.t L.t) {struct m1} : changed2 :=
match m1, m2 with
| PTree.Leaf, PTree.Leaf =>
Same
| PTree.Leaf, _ =>
match combine_r m2 with
| Unchanged => Same2
| Changed m => CC m
end
| _, PTree.Leaf =>
match combine_l m1 with
| Unchanged => Same1
| Changed m => CC m
end
| PTree.Node l1 o1 r1, PTree.Node l2 o2 r2 =>
let o := f o1 o2 in
match xcombine l1 l2, xcombine r1 r2 with
| Same, Same =>
match opt_beq o o1, opt_beq o o2 with
| true, true => Same
| true, false => Same1
| false, true => Same2
| false, false => CC(PTree.Node' l1 o r1)
end
| Same1, Same | Same, Same1 | Same1, Same1 =>
if opt_beq o o1 then Same1 else CC(PTree.Node' l1 o r1)
| Same2, Same | Same, Same2 | Same2, Same2 =>
if opt_beq o o2 then Same2 else CC(PTree.Node' l2 o r2)
| Same1, Same2 => CC(PTree.Node' l1 o r2)
| (Same|Same1), CC r => CC(PTree.Node' l1 o r)
| Same2, Same1 => CC(PTree.Node' l2 o r1)
| Same2, CC r => CC(PTree.Node' l2 o r)
| CC l, (Same|Same1) => CC(PTree.Node' l o r1)
| CC l, Same2 => CC(PTree.Node' l o r2)
| CC l, CC r => CC(PTree.Node' l o r)
end
end.

Lemma xcombine_eq:
forall m1 m2,
match xcombine m1 m2 with
| Same => tree_eq m1 (PTree.combine f m1 m2) /\ tree_eq m2 (PTree.combine f m1 m2)
| Same1 => tree_eq m1 (PTree.combine f m1 m2)
| Same2 => tree_eq m2 (PTree.combine f m1 m2)
| CC m => tree_eq m (PTree.combine f m1 m2)
end.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.xcombine_eq".
Opaque combine_l combine_r PTree.xcombine_l PTree.xcombine_r.
induction m1; destruct m2; simpl.
split; apply tree_eq_refl.
generalize (combine_r_eq (PTree.Node m2_1 o m2_2)).
destruct (combine_r (PTree.Node m2_1 o m2_2)); auto.
generalize (combine_l_eq (PTree.Node m1_1 o m1_2)).
destruct (combine_l (PTree.Node m1_1 o m1_2)); auto.
generalize (IHm1_1 m2_1) (IHm1_2 m2_2).
destruct (xcombine m1_1 m2_1);
destruct (xcombine m1_2 m2_2); auto with combine;
intuition; case_eq (opt_beq (f o o0) o); case_eq (opt_beq (f o o0) o0); auto with combine.
Qed.

Definition combine (m1 m2: PTree.t L.t) : PTree.t L.t :=
match xcombine m1 m2 with
| Same|Same1 => m1
| Same2 => m2
| CC m => m
end.

Lemma gcombine:
forall m1 m2 i, opt_eq (PTree.get i (combine m1 m2)) (f (PTree.get i m1) (PTree.get i m2)).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.gcombine".
intros.
assert (tree_eq (combine m1 m2) (PTree.combine f m1 m2)).
unfold combine.
generalize (xcombine_eq m1 m2).
destruct (xcombine m1 m2); tauto.
eapply opt_eq_trans. apply H. rewrite PTree.gcombine; auto. apply opt_eq_refl.
Qed.

End COMBINE.

Definition lub (x y: t) : t :=
combine
(fun a b =>
match a, b with
| Some u, Some v => Some (L.lub u v)
| None, _ => b
| _, None => a
end)
x y.

Lemma gcombine_bot:
forall f t1 t2 p,
f None None = None ->
L.eq (get p (combine f t1 t2))
(match f t1!p t2!p with Some x => x | None => L.bot end).
Proof. hammer_hook "Lattice" "Lattice.LPMap1.gcombine_bot".
intros. unfold get. generalize (gcombine f H t1 t2 p). unfold opt_eq.
destruct ((combine f t1 t2)!p); destruct (f t1!p t2!p).
auto. contradiction. contradiction. intros; apply L.eq_refl.
Qed.

Lemma ge_lub_left:
forall x y, ge (lub x y) x.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.ge_lub_left".
unfold ge, lub; intros.
eapply L.ge_trans. apply L.ge_refl. apply gcombine_bot; auto.
unfold get. destruct x!p. destruct y!p.
apply L.ge_lub_left.
apply L.ge_refl. apply L.eq_refl.
apply L.ge_bot.
Qed.

Lemma ge_lub_right:
forall x y, ge (lub x y) y.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE.ge_lub_right".
unfold ge, lub; intros.
eapply L.ge_trans. apply L.ge_refl. apply gcombine_bot; auto.
unfold get. destruct y!p. destruct x!p.
apply L.ge_lub_right.
apply L.ge_refl. apply L.eq_refl.
apply L.ge_bot.
Qed.

End LPMap1.



Module LPMap(L: SEMILATTICE_WITH_TOP) <: SEMILATTICE_WITH_TOP.

Inductive t' : Type :=
| Bot: t'
| Top_except: PTree.t L.t -> t'.

Definition t: Type := t'.

Definition get (p: positive) (x: t) : L.t :=
match x with
| Bot => L.bot
| Top_except m => match m!p with None => L.top | Some x => x end
end.

Definition set (p: positive) (v: L.t) (x: t) : t :=
match x with
| Bot => Bot
| Top_except m =>
if L.beq v L.bot
then Bot
else Top_except (if L.beq v L.top then PTree.remove p m else PTree.set p v m)
end.

Lemma gsspec:
forall p v x q,
x <> Bot -> ~L.eq v L.bot ->
L.eq (get q (set p v x)) (if peq q p then v else get q x).
Proof. hammer_hook "Lattice" "Lattice.LPMap.gsspec".
intros. unfold set. destruct x. congruence.
destruct (L.beq v L.bot) eqn:EBOT.
elim H0. apply L.beq_correct; auto.
destruct (L.beq v L.top) eqn:ETOP; simpl.
rewrite PTree.grspec. unfold PTree.elt_eq. destruct (peq q p).
apply L.eq_sym. apply L.beq_correct; auto.
apply L.eq_refl.
rewrite PTree.gsspec. destruct (peq q p); apply L.eq_refl.
Qed.

Definition eq (x y: t) : Prop :=
forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.eq_refl".
unfold eq; intros. apply L.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.eq_sym".
unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.eq_trans".
unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool :=
match x, y with
| Bot, Bot => true
| Top_except m, Top_except n => PTree.beq L.beq m n
| _, _ => false
end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.beq_correct".
destruct x; destruct y; simpl; intro; try congruence.
apply eq_refl.
red; intro; simpl.
rewrite PTree.beq_correct in H. generalize (H p).
destruct (t0!p); destruct (t1!p); intuition.
apply L.beq_correct; auto.
apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.ge_refl".
unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.ge_trans".
unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot := Bot.

Lemma get_bot: forall p, get p bot = L.bot.
Proof. hammer_hook "Lattice" "Lattice.LPMap.get_bot".
unfold bot; intros; simpl. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.ge_bot".
unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.

Definition top := Top_except (PTree.empty L.t).

Lemma get_top: forall p, get p top = L.top.
Proof. hammer_hook "Lattice" "Lattice.LPMap.get_top".
unfold top; intros; simpl. rewrite PTree.gempty. auto.
Qed.

Lemma ge_top: forall x, ge top x.
Proof. hammer_hook "Lattice" "Lattice.SEMILATTICE_WITH_TOP.ge_top".
unfold ge; intros. rewrite get_top. apply L.ge_top.
Qed.

Module LM := LPMap1(L).

Definition opt_lub (x y: L.t) : option L.t :=
let z := L.lub x y in
if L.beq z L.top then None else Some z.

Definition lub (x y: t) : t :=
match x, y with
| Bot, _ => y
| _, Bot => x
| Top_except m, Top_except n =>
Top_except
(LM.combine
(fun a b =>
match a, b with
| Some u, Some v => opt_lub u v
| _, _ => None
end)
m n)
end.

Lemma gcombine_top:
forall f t1 t2 p,
f None None = None ->
L.eq (get p (Top_except (LM.combine f t1 t2)))
(match f t1!p t2!p with Some x => x | None => L.top end).
Proof. hammer_hook "Lattice" "Lattice.LPMap.gcombine_top".
intros. simpl. generalize (LM.gcombine f H t1 t2 p). unfold LM.opt_eq.
destruct ((LM.combine f t1 t2)!p); destruct (f t1!p t2!p).
auto. contradiction. contradiction. intros; apply L.eq_refl.
Qed.

Lemma ge_lub_left:
forall x y, ge (lub x y) x.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.ge_lub_left".
unfold ge, lub; intros. destruct x; destruct y.
rewrite get_bot. apply L.ge_bot.
rewrite get_bot. apply L.ge_bot.
apply L.ge_refl. apply L.eq_refl.
eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
unfold get. destruct t0!p. destruct t1!p.
unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
apply L.ge_top. apply L.ge_lub_left.
apply L.ge_top.
apply L.ge_top.
Qed.

Lemma ge_lub_right:
forall x y, ge (lub x y) y.
Proof. hammer_hook "Lattice" "Lattice.LPMap1.ge_lub_right".
unfold ge, lub; intros. destruct x; destruct y.
rewrite get_bot. apply L.ge_bot.
apply L.ge_refl. apply L.eq_refl.
rewrite get_bot. apply L.ge_bot.
eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
unfold get. destruct t0!p; destruct t1!p.
unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
apply L.ge_top. apply L.ge_lub_right.
apply L.ge_top.
apply L.ge_top.
apply L.ge_top.
Qed.

End LPMap.





Module LFSet (S: FSetInterface.WS) <: SEMILATTICE.

Definition t := S.t.

Definition eq (x y: t) := S.Equal x y.
Definition eq_refl: forall x, eq x x := S.eq_refl.
Definition eq_sym: forall x y, eq x y -> eq y x := S.eq_sym.
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := S.eq_trans.
Definition beq: t -> t -> bool := S.equal.
Definition beq_correct: forall x y, beq x y = true -> eq x y := S.equal_2.

Definition ge (x y: t) := S.Subset y x.
Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. hammer_hook "Lattice" "Lattice.LPMap.ge_refl".
unfold eq, ge, S.Equal, S.Subset; intros. firstorder.
Qed.
Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. hammer_hook "Lattice" "Lattice.LPMap.ge_trans".
unfold ge, S.Subset; intros. eauto.
Qed.

Definition  bot: t := S.empty.
Lemma ge_bot: forall x, ge x bot.
Proof. hammer_hook "Lattice" "Lattice.LPMap.ge_bot".
unfold ge, bot, S.Subset; intros. elim (S.empty_1 H).
Qed.

Definition lub: t -> t -> t := S.union.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. hammer_hook "Lattice" "Lattice.LPMap.ge_lub_left".
unfold lub, ge, S.Subset; intros. apply S.union_2; auto.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof. hammer_hook "Lattice" "Lattice.LPMap.ge_lub_right".
unfold lub, ge, S.Subset; intros. apply S.union_3; auto.
Qed.

End LFSet.





Module LFlat(X: EQUALITY_TYPE) <: SEMILATTICE_WITH_TOP.

Inductive t' : Type :=
| Bot: t'
| Inj: X.t -> t'
| Top: t'.

Definition t : Type := t'.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@eq_refl t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).

Definition beq (x y: t) : bool :=
match x, y with
| Bot, Bot => true
| Inj u, Inj v => if X.eq u v then true else false
| Top, Top => true
| _, _ => false
end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof. hammer_hook "Lattice" "Lattice.LPMap.beq_correct".
unfold eq; destruct x; destruct y; simpl; try congruence; intro.
destruct (X.eq t0 t1); congruence.
Qed.

Definition ge (x y: t) : Prop :=
match x, y with
| Top, _ => True
| _, Bot => True
| Inj a, Inj b => a = b
| _, _ => False
end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. hammer_hook "Lattice" "Lattice.LFSet.ge_refl".
unfold eq, ge; intros; subst y; destruct x; auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. hammer_hook "Lattice" "Lattice.LFSet.ge_trans".
unfold ge; destruct x; destruct y; try destruct z; intuition.
transitivity t1; auto.
Qed.

Definition bot: t := Bot.

Lemma ge_bot: forall x, ge x bot.
Proof. hammer_hook "Lattice" "Lattice.LFSet.ge_bot".
destruct x; simpl; auto.
Qed.

Definition top: t := Top.

Lemma ge_top: forall x, ge top x.
Proof. hammer_hook "Lattice" "Lattice.LPMap.ge_top".
destruct x; simpl; auto.
Qed.

Definition lub (x y: t) : t :=
match x, y with
| Bot, _ => y
| _, Bot => x
| Top, _ => Top
| _, Top => Top
| Inj a, Inj b => if X.eq a b then Inj a else Top
end.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. hammer_hook "Lattice" "Lattice.LFSet.ge_lub_left".
destruct x; destruct y; simpl; auto.
case (X.eq t0 t1); simpl; auto.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof. hammer_hook "Lattice" "Lattice.LFSet.ge_lub_right".
destruct x; destruct y; simpl; auto.
case (X.eq t0 t1); simpl; auto.
Qed.

End LFlat.





Module LBoolean <: SEMILATTICE_WITH_TOP.

Definition t := bool.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@eq_refl t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).

Definition beq : t -> t -> bool := eqb.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof. hammer_hook "Lattice" "Lattice.LFSet.beq_correct". exact (eqb_prop). Qed.

Definition ge (x y: t) : Prop := x = y \/ x = true.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. hammer_hook "Lattice" "Lattice.LFlat.ge_refl". unfold ge; tauto. Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. hammer_hook "Lattice" "Lattice.LFlat.ge_trans". unfold ge; intuition congruence. Qed.

Definition bot := false.

Lemma ge_bot: forall x, ge x bot.
Proof. hammer_hook "Lattice" "Lattice.LFlat.ge_bot". destruct x; compute; tauto. Qed.

Definition top := true.

Lemma ge_top: forall x, ge top x.
Proof. hammer_hook "Lattice" "Lattice.LFlat.ge_top". unfold ge, top; tauto. Qed.

Definition lub (x y: t) := x || y.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. hammer_hook "Lattice" "Lattice.LFlat.ge_lub_left". destruct x; destruct y; compute; tauto. Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof. hammer_hook "Lattice" "Lattice.LFlat.ge_lub_right". destruct x; destruct y; compute; tauto. Qed.

End LBoolean.





Module LOption(L: SEMILATTICE) <: SEMILATTICE_WITH_TOP.

Definition t: Type := option L.t.

Definition eq (x y: t) : Prop :=
match x, y with
| None, None => True
| Some x1, Some y1 => L.eq x1 y1
| _, _ => False
end.

Lemma eq_refl: forall x, eq x x.
Proof. hammer_hook "Lattice" "Lattice.LPMap.eq_refl".
unfold eq; intros; destruct x. apply L.eq_refl. auto.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. hammer_hook "Lattice" "Lattice.LPMap.eq_sym".
unfold eq; intros; destruct x; destruct y; auto. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Lattice" "Lattice.LPMap.eq_trans".
unfold eq; intros; destruct x; destruct y; destruct z; auto.
eapply L.eq_trans; eauto.
contradiction.
Qed.

Definition beq (x y: t) : bool :=
match x, y with
| None, None => true
| Some x1, Some y1 => L.beq x1 y1
| _, _ => false
end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof. hammer_hook "Lattice" "Lattice.LFlat.beq_correct".
unfold beq, eq; intros; destruct x; destruct y.
apply L.beq_correct; auto.
discriminate. discriminate. auto.
Qed.

Definition ge (x y: t) : Prop :=
match x, y with
| None, _ => True
| _, None => False
| Some x1, Some y1 => L.ge x1 y1
end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. hammer_hook "Lattice" "Lattice.LBoolean.ge_refl".
unfold eq, ge; intros; destruct x; destruct y.
apply L.ge_refl; auto.
auto. elim H. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. hammer_hook "Lattice" "Lattice.LBoolean.ge_trans".
unfold ge; intros; destruct x; destruct y; destruct z; auto.
eapply L.ge_trans; eauto. contradiction.
Qed.

Definition bot : t := Some L.bot.

Lemma ge_bot: forall x, ge x bot.
Proof. hammer_hook "Lattice" "Lattice.LBoolean.ge_bot".
unfold ge, bot; intros. destruct x; auto. apply L.ge_bot.
Qed.

Definition lub (x y: t) : t :=
match x, y with
| None, _ => None
| _, None => None
| Some x1, Some y1 => Some (L.lub x1 y1)
end.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. hammer_hook "Lattice" "Lattice.LBoolean.ge_lub_left".
unfold ge, lub; intros; destruct x; destruct y; auto. apply L.ge_lub_left.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof. hammer_hook "Lattice" "Lattice.LBoolean.ge_lub_right".
unfold ge, lub; intros; destruct x; destruct y; auto. apply L.ge_lub_right.
Qed.

Definition top : t := None.

Lemma ge_top: forall x, ge top x.
Proof. hammer_hook "Lattice" "Lattice.LBoolean.ge_top".
unfold ge, top; intros. auto.
Qed.

End LOption.
