From Hammer Require Import Hammer.











Section Inverse_Image.

Variables A B : Type.
Variable R : B -> B -> Prop.
Variable f : A -> B.

Let Rof (x y:A) : Prop := R (f x) (f y).

Remark Acc_lemma : forall y:B, Acc R y -> forall x:A, y = f x -> Acc Rof x.
Proof. hammer_hook "Inverse_Image" "Inverse_Image.Acc_lemma".  
induction 1 as [y _ IHAcc]; intros x H.
apply Acc_intro; intros y0 H1.
apply (IHAcc (f y0)); try trivial.
rewrite H; trivial.
Qed.

Lemma Acc_inverse_image : forall x:A, Acc R (f x) -> Acc Rof x.
Proof. hammer_hook "Inverse_Image" "Inverse_Image.Acc_inverse_image".  
intros; apply (Acc_lemma (f x)); trivial.
Qed.

Theorem wf_inverse_image : well_founded R -> well_founded Rof.
Proof. hammer_hook "Inverse_Image" "Inverse_Image.wf_inverse_image".  
red; intros; apply Acc_inverse_image; auto.
Qed.

Variable F : A -> B -> Prop.
Let RoF (x y:A) : Prop :=
exists2 b : B, F x b & (forall c:B, F y c -> R b c).

Lemma Acc_inverse_rel : forall b:B, Acc R b -> forall x:A, F x b -> Acc RoF x.
Proof. hammer_hook "Inverse_Image" "Inverse_Image.Acc_inverse_rel".  
induction 1 as [x _ IHAcc]; intros x0 H2.
constructor; intros y H3.
destruct H3.
apply (IHAcc x1); auto.
Qed.


Theorem wf_inverse_rel : well_founded R -> well_founded RoF.
Proof. hammer_hook "Inverse_Image" "Inverse_Image.wf_inverse_rel".  
red; constructor; intros.
case H0; intros.
apply (Acc_inverse_rel x); auto.
Qed.

End Inverse_Image.

