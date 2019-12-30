From Hammer Require Import Hammer.




Set Implicit Arguments.

From QuicksortComplexity Require Import util.
Require Import Le.
Require Import Plus.
Require Import Minus.
Require Import Lt.
Require Import Arith.
Require Import Recdef.
Require Import Bool_nat.
Require Import List.
From QuicksortComplexity Require Import list_utils.
Require Import Omega.
Require Import Arith.
Require Import Bool.
Require Import EqNat.
Require Import Relations.

Section contents.

Record E: Type :=
{ Ec:> Set
; Ecmp: Ec -> Ec -> comparison
; Ecmp_sym: forall x y, Ecmp x y = CompOpp (Ecmp y x)
; Ecmp_trans: forall x y z c, Ecmp x y = c -> Ecmp y z = c -> Ecmp x z = c
; Ecmp_eq_trans_l: forall x y z c, Ecmp x y = Eq -> Ecmp y z = c -> Ecmp x z = c
}.

Context {e: E}.

Lemma Ecmp_apply_sym x y c: Ecmp e x y = CompOpp c -> Ecmp e y x = c.
Proof. hammer_hook "sort_order" "sort_order.Ecmp_apply_sym". intros. rewrite Ecmp_sym. rewrite H. destruct c; auto. Qed.

Lemma Ecmp_eq_trans_r x y z c: Ecmp e x y = c -> Ecmp e y z = Eq -> Ecmp e x z = c.
Proof with auto. hammer_hook "sort_order" "sort_order.Ecmp_eq_trans_r".
intros.
rewrite Ecmp_sym.
cset (Ecmp_sym e z y).
rewrite H0 in H1.
simpl in H1.
cset (Ecmp_sym e y x).
rewrite H in H2.
rewrite (Ecmp_eq_trans_l e z y x H1 H2).
destruct c...
Qed.

Section shorthands.

Variables (x y: e).

Definition Elt: Prop := Ecmp _ x y = Lt.
Definition Egt: Prop := Ecmp _ x y = Gt.
Definition Ele: Prop := Ecmp _ x y <> Gt.
Definition Ege: Prop := Ecmp _ x y <> Lt.

Definition Eltb: bool := match Ecmp _ x y with Lt => true | _ => false end.
Definition Egtb: bool := match Ecmp _ x y with Gt => true | _ => false end.
Definition Eleb: bool := match Ecmp _ x y with Gt => false | _ => true end.
Definition Egeb: bool := match Ecmp _ x y with Lt => false | _ => true end.

Lemma Eltb_true: Elt <-> Eltb = true.
Proof. hammer_hook "sort_order" "sort_order.Eltb_true". unfold Elt, Eltb. destruct (Ecmp e x y); intuition; discriminate. Qed.

Lemma Egtb_true: Egt <-> Egtb = true.
Proof. hammer_hook "sort_order" "sort_order.Egtb_true". unfold Egt, Egtb. destruct (Ecmp e x y); intuition; discriminate. Qed.

Lemma Eleb_true: Ele <-> Eleb = true.
Proof. hammer_hook "sort_order" "sort_order.Eleb_true". unfold Ele, Eleb. destruct (Ecmp e x y); intuition; discriminate. Qed.

Lemma Egeb_true: Ege <-> Egeb = true.
Proof. hammer_hook "sort_order" "sort_order.Egeb_true". unfold Ege, Egeb. destruct (Ecmp e x y); intuition; discriminate. Qed.

End shorthands.

Lemma Elt_irrefl x: ~ Elt x x.
Proof. hammer_hook "sort_order" "sort_order.Elt_irrefl".
intros.
unfold Elt.
intro.
cset (Ecmp_sym e x x).
rewrite H in H0.
discriminate.
Qed.

Lemma Ele_dec x y: decision (Ele x y).
Proof. hammer_hook "sort_order" "sort_order.Ele_dec".
intros.
unfold Ele.
destruct (Ecmp e x y); [left | left | right]; intro.
discriminate.
discriminate.
apply H. reflexivity.
Qed.

Lemma Ecmp_refl x: Ecmp e x x = Eq.
Proof with auto. hammer_hook "sort_order" "sort_order.Ecmp_refl".
assert (Ecmp e x x = CompOpp (Ecmp e x x)).
apply Ecmp_sym.
destruct (Ecmp e x x); try discriminate...
Qed.

Lemma Ele_le_dec x y: { Ele x y } + { Ele y x }.
Proof. hammer_hook "sort_order" "sort_order.Ele_le_dec".
unfold Ele.
rewrite Ecmp_sym.
destruct (Ecmp e y x); [left | right | left]; intro; discriminate.
Qed.

Lemma Ecmp_inv_sym x y c: Ecmp e x y <> CompOpp c -> Ecmp e y x <> c.
Proof. hammer_hook "sort_order" "sort_order.Ecmp_inv_sym".
intros.
intro.
apply H.
rewrite Ecmp_sym.
rewrite H0.
destruct c; auto.
Qed.

Lemma Ele_Ege x y: Ele x y -> Ege y x.
Proof. hammer_hook "sort_order" "sort_order.Ele_Ege". unfold Ele, Ege. intros. apply Ecmp_inv_sym. assumption. Qed.

Lemma Ege_Ele x y: Ege x y -> Ele y x.
Proof. hammer_hook "sort_order" "sort_order.Ege_Ele". unfold Ele, Ege. intros. apply Ecmp_inv_sym. assumption. Qed.

Lemma Ecmp_le_lt_trans: forall x y z, Ele x y -> Ecmp e y z = Lt -> Ecmp e x z = Lt.
Proof with auto. hammer_hook "sort_order" "sort_order.Ecmp_le_lt_trans".
intros x y z.
unfold Ele.
case_eq (Ecmp e x y); intros.
apply Ecmp_eq_trans_l with y...
apply Ecmp_trans with y...
elimtype False...
Qed.

Lemma Ecmp_lt_le_trans: forall x y z, Ecmp e x y = Lt -> Ele y z -> Ecmp e x z = Lt.
Proof with auto. hammer_hook "sort_order" "sort_order.Ecmp_lt_le_trans".
intros x y z.
unfold Ele.
case_eq (Ecmp e y z); intros.
apply Ecmp_eq_trans_r with y...
apply Ecmp_trans with y...
elimtype False...
Qed.

Lemma Ecmp_ge_gt_trans: forall x y z, Ege x y -> Ecmp e y z = Gt -> Ecmp e x z = Gt.
Proof with auto. hammer_hook "sort_order" "sort_order.Ecmp_ge_gt_trans".
intros x y z.
unfold Ege.
case_eq (Ecmp e x y); intros.
apply Ecmp_eq_trans_l with y...
elimtype False...
apply Ecmp_trans with y...
Qed.

Lemma EO: preorder _ Ele.
Proof with try assumption. hammer_hook "sort_order" "sort_order.EO".
apply Build_preorder.
unfold reflexive.
intros.
unfold Ele.
rewrite Ecmp_refl.
intro.
discriminate.
unfold transitive.
intros.
unfold Ele.
case_eq (Ecmp e x z); do 2 intro; try discriminate.
apply H0.
apply Ecmp_ge_gt_trans with x...
apply Ele_Ege...
Qed.

Lemma Ege_preorder: preorder _ Ege.
Proof with try assumption. hammer_hook "sort_order" "sort_order.Ege_preorder".
apply Build_preorder.
unfold reflexive.
intros.
unfold Ege.
rewrite Ecmp_refl.
discriminate.
unfold transitive.
intros.
unfold Ege.
case_eq (Ecmp e x z); do 2 intro; try discriminate.
apply H0.
apply Ecmp_le_lt_trans with x...
apply Ege_Ele...
Qed.

Hint Immediate Ege_preorder EO.

Lemma preorder_impl X (P Q: relation X): (forall x y, P x y <-> Q x y) -> preorder _ P -> preorder _ Q.
Proof with try firstorder. hammer_hook "sort_order" "sort_order.preorder_impl".
intros.
destruct H0.
constructor...
repeat intro.
apply -> H.
apply preord_trans with y...
Qed.

Lemma Eleb_preorder: preorder _ (fun x y => Eleb x y = true).
Proof with auto. hammer_hook "sort_order" "sort_order.Eleb_preorder".
intros. apply preorder_impl with Ele...
intros. apply Eleb_true.
Qed.

Lemma Egeb_preorder: preorder _ (fun x y => Egeb x y = true).
Proof with auto. hammer_hook "sort_order" "sort_order.Egeb_preorder".
intros. apply preorder_impl with Ege...
intros. apply Egeb_true.
Qed.

Lemma Ele_nlt x y: Ele x y -> ~ Elt y x.
Proof. hammer_hook "sort_order" "sort_order.Ele_nlt". unfold Ele, Elt. intros. rewrite Ecmp_sym. destruct (Ecmp e x y); simpl; intro; try discriminate. auto. Qed.

Lemma Enle_le x y: ~ Ele x y -> Ele y x.
Proof with intro; discriminate. hammer_hook "sort_order" "sort_order.Enle_le".
unfold Ele.
intros.
rewrite Ecmp_sym.
destruct (Ecmp e x y).
elimtype False. apply H...
elimtype False. apply H...
simpl...
Qed.

End contents.


