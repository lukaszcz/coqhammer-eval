From Hammer Require Import Hammer.













Require Import FunInd Recdef FMapInterface FMapList ZArith Int FMapAVL ROmega.

Set Implicit Arguments.
Unset Strict Implicit.

Module AvlProofs (Import I:Int)(X: OrderedType).
Module Import Raw := Raw I X.
Module Import II:=MoreInt(I).
Import Raw.Proofs.
Local Open Scope pair_scope.
Local Open Scope Int_scope.

Ltac omega_max := i2z_refl; romega with Z.

Section Elt.
Variable elt : Type.
Implicit Types m r : t elt.





Inductive avl : t elt -> Prop :=
| RBLeaf : avl (Leaf _)
| RBNode : forall x e l r h,
avl l ->
avl r ->
-(2) <= height l - height r <= 2 ->
h = max (height l) (height r) + 1 ->
avl (Node l x e r h).




Hint Constructors avl.

Lemma height_non_negative : forall (s : t elt), avl s ->
height s >= 0.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.height_non_negative".  
induction s; simpl; intros; auto with zarith.
inv avl; intuition; omega_max.
Qed.

Ltac avl_nn_hyp H :=
let nz := fresh "nz" in assert (nz := height_non_negative H).

Ltac avl_nn h :=
let t := type of h in
match type of t with
| Prop => avl_nn_hyp h
| _ => match goal with H : avl h |- _ => avl_nn_hyp H end
end.



Ltac avl_nns :=
match goal with
| H:avl _ |- _ => avl_nn_hyp H; clear H; avl_nns
| _ => idtac
end.




Lemma avl_node : forall x e l r, avl l -> avl r ->
-(2) <= height l - height r <= 2 ->
avl (Node l x e r (max (height l) (height r) + 1)).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.avl_node".  
intros; auto.
Qed.
Hint Resolve avl_node.



Lemma height_0 : forall l, avl l -> height l = 0 ->
l = Leaf _.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.height_0".  
destruct 1; intuition; simpl in *.
avl_nns; simpl in *; exfalso; omega_max.
Qed.




Lemma empty_avl : avl (empty elt).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.empty_avl".  
unfold empty; auto.
Qed.




Lemma create_avl :
forall l x e r, avl l -> avl r ->  -(2) <= height l - height r <= 2 ->
avl (create l x e r).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.create_avl".  
unfold create; auto.
Qed.

Lemma create_height :
forall l x e r, avl l -> avl r ->  -(2) <= height l - height r <= 2 ->
height (create l x e r) = max (height l) (height r) + 1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.create_height".  
unfold create; intros; auto.
Qed.

Lemma bal_avl : forall l x e r, avl l -> avl r ->
-(3) <= height l - height r <= 3 -> avl (bal l x e r).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.bal_avl".  
intros l x e r; functional induction (bal l x e r); intros; clearf;
inv avl; simpl in *;
match goal with |- avl (assert_false _ _ _ _) => avl_nns
| _ => repeat apply create_avl; simpl in *; auto
end; omega_max.
Qed.

Lemma bal_height_1 : forall l x e r, avl l -> avl r ->
-(3) <= height l - height r <= 3 ->
0 <= height (bal l x e r) - max (height l) (height r) <= 1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.bal_height_1".  
intros l x e r; functional induction (bal l x e r); intros; clearf;
inv avl; avl_nns; simpl in *; omega_max.
Qed.

Lemma bal_height_2 :
forall l x e r, avl l -> avl r -> -(2) <= height l - height r <= 2 ->
height (bal l x e r) == max (height l) (height r) +1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.bal_height_2".  
intros l x e r; functional induction (bal l x e r); intros; clearf;
inv avl; avl_nns; simpl in *; omega_max.
Qed.

Ltac omega_bal := match goal with
| H:avl ?l, H':avl ?r |- context [ bal ?l ?x ?e ?r ] =>
generalize (bal_height_1 x e H H') (bal_height_2 x e H H');
omega_max
end.



Lemma add_avl_1 :  forall m x e, avl m ->
avl (add x e m) /\ 0 <= height (add x e m) - height m <= 1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.add_avl_1".  
intros m x e; functional induction (add x e m); intros; inv avl; simpl in *.
intuition; try constructor; simpl; auto; try omega_max.

destruct IHt; auto.
split.
apply bal_avl; auto; omega_max.
omega_bal.

intuition; omega_max.

destruct IHt; auto.
split.
apply bal_avl; auto; omega_max.
omega_bal.
Qed.

Lemma add_avl : forall m x e, avl m -> avl (add x e m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.add_avl".  
intros; generalize (add_avl_1 x e H); intuition.
Qed.
Hint Resolve add_avl.



Lemma remove_min_avl_1 : forall l x e r h, avl (Node l x e r h) ->
avl (remove_min l x e r)#1 /\
0 <= height (Node l x e r h) - height (remove_min l x e r)#1 <= 1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.remove_min_avl_1".  
intros l x e r; functional induction (remove_min l x e r); simpl in *; intros.
inv avl; simpl in *; split; auto.
avl_nns; omega_max.
inversion_clear H.
rewrite e0 in IHp;simpl in IHp;destruct (IHp _x); auto.
split; simpl in *.
apply bal_avl; auto; omega_max.
omega_bal.
Qed.

Lemma remove_min_avl : forall l x e r h, avl (Node l x e r h) ->
avl (remove_min l x e r)#1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.remove_min_avl".  
intros; generalize (remove_min_avl_1 H); intuition.
Qed.



Lemma merge_avl_1 : forall m1 m2, avl m1 -> avl m2 ->
-(2) <= height m1 - height m2 <= 2 ->
avl (merge m1 m2) /\
0<= height (merge m1 m2) - max (height m1) (height m2) <=1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.merge_avl_1".  
intros m1 m2; functional induction (merge m1 m2); intros;
try factornode _x _x0 _x1 _x2 _x3 as m1.
simpl; split; auto; avl_nns; omega_max.
simpl; split; auto; avl_nns; omega_max.
generalize (remove_min_avl_1 H0).
rewrite e1; destruct 1.
split.
apply bal_avl; auto.
omega_max.
omega_bal.
Qed.

Lemma merge_avl : forall m1 m2, avl m1 -> avl m2 ->
-(2) <= height m1 - height m2 <= 2 -> avl (merge m1 m2).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.merge_avl".  
intros; generalize (merge_avl_1 H H0 H1); intuition.
Qed.




Lemma remove_avl_1 : forall m x, avl m ->
avl (remove x m) /\ 0 <= height m - height (remove x m) <= 1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.remove_avl_1".  
intros m x; functional induction (remove x m); intros.
split; auto; omega_max.

inv avl.
destruct (IHt H0).
split.
apply bal_avl; auto.
omega_max.
omega_bal.

inv avl.
generalize (merge_avl_1 H0 H1 H2).
intuition omega_max.

inv avl.
destruct (IHt H1).
split.
apply bal_avl; auto.
omega_max.
omega_bal.
Qed.

Lemma remove_avl : forall m x, avl m -> avl (remove x m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.remove_avl".  
intros; generalize (remove_avl_1 x H); intuition.
Qed.
Hint Resolve remove_avl.




Lemma join_avl_1 : forall l x d r, avl l -> avl r ->
avl (join l x d r) /\
0<= height (join l x d r) - max (height l) (height r) <= 1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.join_avl_1".  
join_tac.

split; simpl; auto.
destruct (add_avl_1 x d H0).
avl_nns; omega_max.
set (l:=Node ll lx ld lr lh) in *.
split; auto.
destruct (add_avl_1 x d H).
simpl (height (Leaf elt)).
avl_nns; omega_max.

inversion_clear H.
assert (height (Node rl rx rd rr rh) = rh); auto.
set (r := Node rl rx rd rr rh) in *; clearbody r.
destruct (Hlr x d r H2 H0); clear Hrl Hlr.
set (j := join lr x d r) in *; clearbody j.
simpl.
assert (-(3) <= height ll - height j <= 3) by omega_max.
split.
apply bal_avl; auto.
omega_bal.

inversion_clear H0.
assert (height (Node ll lx ld lr lh) = lh); auto.
set (l := Node ll lx ld lr lh) in *; clearbody l.
destruct (Hrl H H1); clear Hrl Hlr.
set (j := join l x d rl) in *; clearbody j.
simpl.
assert (-(3) <= height j - height rr <= 3) by omega_max.
split.
apply bal_avl; auto.
omega_bal.

clear Hrl Hlr.
assert (height (Node ll lx ld lr lh) = lh); auto.
assert (height (Node rl rx rd rr rh) = rh); auto.
set (l := Node ll lx ld lr lh) in *; clearbody l.
set (r := Node rl rx rd rr rh) in *; clearbody r.
assert (-(2) <= height l - height r <= 2) by omega_max.
split.
apply create_avl; auto.
rewrite create_height; auto; omega_max.
Qed.

Lemma join_avl : forall l x d r, avl l -> avl r -> avl (join l x d r).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.join_avl".  
intros; destruct (join_avl_1 x d H H0); auto.
Qed.
Hint Resolve join_avl.



Lemma concat_avl : forall m1 m2, avl m1 -> avl m2 -> avl (concat m1 m2).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.concat_avl".  
intros m1 m2; functional induction (concat m1 m2); auto.
intros; apply join_avl; auto.
generalize (remove_min_avl H0); rewrite e1; simpl; auto.
Qed.
Hint Resolve concat_avl.



Lemma split_avl : forall m x, avl m ->
avl (split x m)#l /\ avl (split x m)#r.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.split_avl".  
intros m x; functional induction (split x m); simpl; auto.
rewrite e1 in IHt;simpl in IHt;inversion_clear 1; intuition.
simpl; inversion_clear 1; auto.
rewrite e1 in IHt;simpl in IHt;inversion_clear 1; intuition.
Qed.

End Elt.
Hint Constructors avl.

Section Map.
Variable elt elt' : Type.
Variable f : elt -> elt'.

Lemma map_height : forall m, height (map f m) = height m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.map_height".  
destruct m; simpl; auto.
Qed.

Lemma map_avl : forall m, avl m -> avl (map f m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.map_avl".  
induction m; simpl; auto.
inversion_clear 1; constructor; auto; do 2 rewrite map_height; auto.
Qed.

End Map.

Section Mapi.
Variable elt elt' : Type.
Variable f : key -> elt -> elt'.

Lemma mapi_height : forall m, height (mapi f m) = height m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.mapi_height".  
destruct m; simpl; auto.
Qed.

Lemma mapi_avl : forall m, avl m -> avl (mapi f m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.mapi_avl".  
induction m; simpl; auto.
inversion_clear 1; constructor; auto; do 2 rewrite mapi_height; auto.
Qed.

End Mapi.

Section Map_option.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Lemma map_option_avl : forall m, avl m -> avl (map_option f m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.map_option_avl".  
induction m; simpl; auto; intros.
inv avl; destruct (f k e); auto using join_avl, concat_avl.
Qed.

End Map_option.

Section Map2_opt.
Variable elt elt' elt'' : Type.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.
Hypothesis mapl_avl : forall m, avl m -> avl (mapl m).
Hypothesis mapr_avl : forall m', avl m' -> avl (mapr m').

Notation map2_opt := (map2_opt f mapl mapr).

Lemma map2_opt_avl : forall m1 m2, avl m1 -> avl m2 ->
avl (map2_opt m1 m2).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.map2_opt_avl".  
intros m1 m2; functional induction (map2_opt m1 m2); auto;
factornode _x0 _x1 _x2 _x3 _x4 as r2; intros;
destruct (split_avl x1 H0); rewrite e1 in *; simpl in *; inv avl;
auto using join_avl, concat_avl.
Qed.

End Map2_opt.

Section Map2.
Variable elt elt' elt'' : Type.
Variable f : option elt -> option elt' -> option elt''.

Lemma map2_avl : forall m1 m2, avl m1 -> avl m2 -> avl (map2 f m1 m2).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.AvlProofs.map2_avl".  
unfold map2; auto using map2_opt_avl, map_option_avl.
Qed.

End Map2.
End AvlProofs.



Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

Module E := X.
Module Import AvlProofs := AvlProofs I X.
Import Raw.
Import Raw.Proofs.

Record bbst (elt:Type) :=
Bbst {this :> tree elt; is_bst : bst this; is_avl: avl this}.

Definition t := bbst.
Definition key := E.t.

Section Elt.
Variable elt elt' elt'': Type.

Implicit Types m : t elt.
Implicit Types x y : key.
Implicit Types e : elt.

Definition empty : t elt := Bbst (empty_bst elt) (empty_avl elt).
Definition is_empty m : bool := is_empty m.(this).
Definition add x e m : t elt :=
Bbst (add_bst x e m.(is_bst)) (add_avl x e m.(is_avl)).
Definition remove x m : t elt :=
Bbst (remove_bst x m.(is_bst)) (remove_avl x m.(is_avl)).
Definition mem x m : bool := mem x m.(this).
Definition find x m : option elt := find x m.(this).
Definition map f m : t elt' :=
Bbst (map_bst f m.(is_bst)) (map_avl f m.(is_avl)).
Definition mapi (f:key->elt->elt') m : t elt' :=
Bbst (mapi_bst f m.(is_bst)) (mapi_avl f m.(is_avl)).
Definition map2 f m (m':t elt') : t elt'' :=
Bbst (map2_bst f m.(is_bst) m'.(is_bst)) (map2_avl f m.(is_avl) m'.(is_avl)).
Definition elements m : list (key*elt) := elements m.(this).
Definition cardinal m := cardinal m.(this).
Definition fold (A:Type) (f:key->elt->A->A) m i := fold (A:=A) f m.(this) i.
Definition equal cmp m m' : bool := equal cmp m.(this) m'.(this).

Definition MapsTo x e m : Prop := MapsTo x e m.(this).
Definition In x m : Prop := In0 x m.(this).
Definition Empty m : Prop := Empty m.(this).

Definition eq_key : (key*elt) -> (key*elt) -> Prop := @PX.eqk elt.
Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop := @PX.eqke elt.
Definition lt_key : (key*elt) -> (key*elt) -> Prop := @PX.ltk elt.

Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.MapsTo_1".   intros m; exact (@MapsTo_1 _ m.(this)). Qed.

Lemma mem_1 : forall m x, In x m -> mem x m = true.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.mem_1".  
unfold In, mem; intros m x; rewrite In_alt; simpl; apply mem_1; auto.
apply m.(is_bst).
Qed.

Lemma mem_2 : forall m x, mem x m = true -> In x m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.mem_2".  
unfold In, mem; intros m x; rewrite In_alt; simpl; apply mem_2; auto.
Qed.

Lemma empty_1 : Empty empty.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.empty_1".   exact (@empty_1 elt). Qed.

Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.is_empty_1".   intros m; exact (@is_empty_1 _ m.(this)). Qed.
Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.is_empty_2".   intros m; exact (@is_empty_2 _ m.(this)). Qed.

Lemma add_1 : forall m x y e, E.eq x y -> MapsTo y e (add x e m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.add_1".   intros m x y e; exact (@add_1 elt _ x y e). Qed.
Lemma add_2 : forall m x y e e', ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.add_2".   intros m x y e e'; exact (@add_2 elt _ x y e e'). Qed.
Lemma add_3 : forall m x y e e', ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.add_3".   intros m x y e e'; exact (@add_3 elt _ x y e e'). Qed.

Lemma remove_1 : forall m x y, E.eq x y -> ~ In y (remove x m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.remove_1".  
unfold In, remove; intros m x y; rewrite In_alt; simpl; apply remove_1; auto.
apply m.(is_bst).
Qed.
Lemma remove_2 : forall m x y e, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.remove_2".   intros m x y e; exact (@remove_2 elt _ x y e m.(is_bst)). Qed.
Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.remove_3".   intros m x y e; exact (@remove_3 elt _ x y e m.(is_bst)). Qed.


Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.find_1".   intros m x e; exact (@find_1 elt _ x e m.(is_bst)). Qed.
Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.find_2".   intros m; exact (@find_2 elt m.(this)). Qed.

Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.fold_1".   intros m; exact (@fold_1 elt m.(this) m.(is_bst)). Qed.

Lemma elements_1 : forall m x e,
MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.elements_1".  
intros; unfold elements, MapsTo, eq_key_elt; rewrite elements_mapsto; auto.
Qed.

Lemma elements_2 : forall m x e,
InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.elements_2".  
intros; unfold elements, MapsTo, eq_key_elt; rewrite <- elements_mapsto; auto.
Qed.

Lemma elements_3 : forall m, sort lt_key (elements m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.elements_3".   intros m; exact (@elements_sort elt m.(this) m.(is_bst)). Qed.

Lemma elements_3w : forall m, NoDupA eq_key (elements m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.elements_3w".   intros m; exact (@elements_nodup elt m.(this) m.(is_bst)). Qed.

Lemma cardinal_1 : forall m, cardinal m = length (elements m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.cardinal_1".   intro m; exact (@elements_cardinal elt m.(this)). Qed.

Definition Equal m m' := forall y, find y m = find y m'.
Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
(forall k, In k m <-> In k m') /\
(forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
Definition Equivb cmp := Equiv (Cmp cmp).

Lemma Equivb_Equivb : forall cmp m m',
Equivb cmp m m' <-> Raw.Proofs.Equivb cmp m m'.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.Equivb_Equivb".  
intros; unfold Equivb, Equiv, Raw.Proofs.Equivb, In; intuition.
generalize (H0 k); do 2 rewrite In_alt; intuition.
generalize (H0 k); do 2 rewrite In_alt; intuition.
generalize (H0 k); do 2 rewrite <- In_alt; intuition.
generalize (H0 k); do 2 rewrite <- In_alt; intuition.
Qed.

Lemma equal_1 : forall m m' cmp,
Equivb cmp m m' -> equal cmp m m' = true.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.equal_1".  
unfold equal; intros (m,b,a) (m',b',a') cmp; rewrite Equivb_Equivb;
intros; simpl in *; rewrite equal_Equivb; auto.
Qed.

Lemma equal_2 : forall m m' cmp,
equal cmp m m' = true -> Equivb cmp m m'.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.equal_2".  
unfold equal; intros (m,b,a) (m',b',a') cmp; rewrite Equivb_Equivb;
intros; simpl in *; rewrite <-equal_Equivb; auto.
Qed.

End Elt.

Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
MapsTo x e m -> MapsTo x (f e) (map f m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.map_1".   intros elt elt' m x e f; exact (@map_1 elt elt' f m.(this) x e). Qed.

Lemma map_2 : forall (elt elt':Type)(m:t elt)(x:key)(f:elt->elt'), In x (map f m) -> In x m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.map_2".  
intros elt elt' m x f; do 2 unfold In in *; do 2 rewrite In_alt; simpl.
apply map_2; auto.
Qed.

Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
(f:key->elt->elt'), MapsTo x e m ->
exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.mapi_1".   intros elt elt' m x e f; exact (@mapi_1 elt elt' f m.(this) x e). Qed.
Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
(f:key->elt->elt'), In x (mapi f m) -> In x m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.mapi_2".  
intros elt elt' m x f; unfold In in *; do 2 rewrite In_alt; simpl; apply mapi_2; auto.
Qed.

Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
(x:key)(f:option elt->option elt'->option elt''),
In x m \/ In x m' ->
find x (map2 f m m') = f (find x m) (find x m').
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.map2_1".  
unfold find, map2, In; intros elt elt' elt'' m m' x f.
do 2 rewrite In_alt; intros; simpl; apply map2_1; auto.
apply m.(is_bst).
apply m'.(is_bst).
Qed.

Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
(x:key)(f:option elt->option elt'->option elt''),
In x (map2 f m m') -> In x m \/ In x m'.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake.map2_2".  
unfold In, map2; intros elt elt' elt'' m m' x f.
do 3 rewrite In_alt; intros; simpl in *; eapply map2_2; eauto.
apply m.(is_bst).
apply m'.(is_bst).
Qed.

End IntMake.


Module IntMake_ord (I:Int)(X: OrderedType)(D : OrderedType) <:
Sord with Module Data := D
with Module MapS.E := X.

Module Data := D.
Module Import MapS := IntMake(I)(X).
Import AvlProofs.
Import Raw.Proofs.
Module Import MD := OrderedTypeFacts(D).
Module LO := FMapList.Make_ord(X)(D).

Definition t := MapS.t D.t.

Definition cmp e e' :=
match D.compare e e' with EQ _ => true | _ => false end.

Definition elements (m:t) :=
LO.MapS.Build_slist (Raw.Proofs.elements_sort m.(is_bst)).



Fixpoint cardinal_e (e:Raw.enumeration D.t) :=
match e with
| Raw.End _ => 0%nat
| Raw.More _ _ r e => S (Raw.cardinal r + cardinal_e e)
end.

Lemma cons_cardinal_e : forall m e,
cardinal_e (Raw.cons m e) = (Raw.cardinal m + cardinal_e e)%nat.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.cons_cardinal_e".  
induction m; simpl; intros; auto.
rewrite IHm1; simpl; rewrite <- plus_n_Sm; auto with arith.
Qed.

Definition cardinal_e_2 ee :=
(cardinal_e (fst ee) + cardinal_e (snd ee))%nat.

Local Unset Keyed Unification.

Function compare_aux (ee:Raw.enumeration D.t * Raw.enumeration D.t)
{ measure cardinal_e_2 ee } : comparison :=
match ee with
| (Raw.End _, Raw.End _) => Eq
| (Raw.End _, Raw.More _ _ _ _) => Lt
| (Raw.More _ _ _ _, Raw.End _) => Gt
| (Raw.More x1 d1 r1 e1, Raw.More x2 d2 r2 e2) =>
match X.compare x1 x2 with
| EQ _ => match D.compare d1 d2 with
| EQ _ => compare_aux (Raw.cons r1 e1, Raw.cons r2 e2)
| LT _ => Lt
| GT _ => Gt
end
| LT _ => Lt
| GT _ => Gt
end
end.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.cardinal_e_2".  
intros; unfold cardinal_e_2; simpl;
abstract (do 2 rewrite cons_cardinal_e; romega with * ).
Defined.

Definition Cmp c :=
match c with
| Eq => LO.eq_list
| Lt => LO.lt_list
| Gt => (fun l1 l2 => LO.lt_list l2 l1)
end.

Lemma cons_Cmp : forall c x1 x2 d1 d2 l1 l2,
X.eq x1 x2 -> D.eq d1 d2 ->
Cmp c l1 l2 -> Cmp c ((x1,d1)::l1) ((x2,d2)::l2).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.cons_Cmp".  
destruct c; simpl; intros; MX.elim_comp; auto.
Qed.
Hint Resolve cons_Cmp.

Lemma compare_aux_Cmp : forall e,
Cmp (compare_aux e) (flatten_e (fst e)) (flatten_e (snd e)).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.compare_aux_Cmp".  
intros e; functional induction (compare_aux e); simpl in *;
auto; intros; try clear e0; try clear e3; try MX.elim_comp; auto.
rewrite 2 cons_1 in IHc; auto.
Qed.

Lemma compare_Cmp : forall m1 m2,
Cmp (compare_aux (Raw.cons m1 (Raw.End _), Raw.cons m2 (Raw.End _)))
(Raw.elements m1) (Raw.elements m2).
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.compare_Cmp".  
intros.
assert (H1:=cons_1 m1 (Raw.End _)).
assert (H2:=cons_1 m2 (Raw.End _)).
simpl in *; rewrite app_nil_r in *; rewrite <-H1,<-H2.
apply (@compare_aux_Cmp (Raw.cons m1 (Raw.End _),
Raw.cons m2 (Raw.End _))).
Qed.

Definition eq (m1 m2 : t) := LO.eq_list (Raw.elements m1) (Raw.elements m2).
Definition lt (m1 m2 : t) := LO.lt_list (Raw.elements m1) (Raw.elements m2).

Definition compare (s s':t) : Compare lt eq s s'.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.compare".  
destruct s as (s,b,a), s' as (s',b',a').
generalize (compare_Cmp s s').
destruct compare_aux; intros; [apply EQ|apply LT|apply GT]; red; auto.
Defined.




Definition selements (m1 : t) :=
LO.MapS.Build_slist (elements_sort m1.(is_bst)).

Definition seq (m1 m2 : t) := LO.eq (selements m1) (selements m2).
Definition slt (m1 m2 : t) := LO.lt (selements m1) (selements m2).

Lemma eq_seq : forall m1 m2, eq m1 m2 <-> seq m1 m2.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.eq_seq".  
unfold eq, seq, selements, elements, LO.eq; intuition.
Qed.

Lemma lt_slt : forall m1 m2, lt m1 m2 <-> slt m1 m2.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.lt_slt".  
unfold lt, slt, selements, elements, LO.lt; intuition.
Qed.

Lemma eq_1 : forall (m m' : t), MapS.Equivb cmp m m' -> eq m m'.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.eq_1".  
intros m m'.
rewrite eq_seq; unfold seq.
rewrite Equivb_Equivb.
rewrite Equivb_elements.
auto using LO.eq_1.
Qed.

Lemma eq_2 : forall m m', eq m m' -> MapS.Equivb cmp m m'.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.eq_2".  
intros m m'.
rewrite eq_seq; unfold seq.
rewrite Equivb_Equivb.
rewrite Equivb_elements.
intros.
generalize (LO.eq_2 H).
auto.
Qed.

Lemma eq_refl : forall m : t, eq m m.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.eq_refl".  
intros; rewrite eq_seq; unfold seq; intros; apply LO.eq_refl.
Qed.

Lemma eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.eq_sym".  
intros m1 m2; rewrite 2 eq_seq; unfold seq; intros; apply LO.eq_sym; auto.
Qed.

Lemma eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.eq_trans".  
intros m1 m2 M3; rewrite 3 eq_seq; unfold seq.
intros; eapply LO.eq_trans; eauto.
Qed.

Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.lt_trans".  
intros m1 m2 m3; rewrite 3 lt_slt; unfold slt;
intros; eapply LO.lt_trans; eauto.
Qed.

Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
Proof. hammer_hook "FMapFullAVL" "FMapFullAVL.IntMake_ord.lt_not_eq".  
intros m1 m2; rewrite lt_slt, eq_seq; unfold slt, seq;
intros; apply LO.lt_not_eq; auto.
Qed.

End IntMake_ord.



Module Make (X: OrderedType) <: S with Module E := X
:=IntMake(Z_as_Int)(X).

Module Make_ord (X: OrderedType)(D: OrderedType)
<: Sord with Module Data := D
with Module MapS.E := X
:=IntMake_ord(Z_as_Int)(X)(D).

