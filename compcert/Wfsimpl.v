From Hammer Require Import Hammer.


















From compcert Require Import Axioms.
Require Import Init.Wf.
Require Import Wf_nat.

Set Implicit Arguments.

Section FIX.

Variables A B: Type.
Variable R: A -> A -> Prop.
Hypothesis Rwf: well_founded R.
Variable F: forall (x: A), (forall (y: A), R y x -> B) -> B.

Definition Fix (x: A) : B := Wf.Fix Rwf (fun (x: A) => B) F x.

Theorem unroll_Fix:
forall x, Fix x = F (fun (y: A) (P: R y x) => Fix y).
Proof. hammer_hook "Wfsimpl" "Wfsimpl.unroll_Fix".
unfold Fix; intros. apply Wf.Fix_eq with (P := fun (x: A) => B).
intros. assert (f = g). apply functional_extensionality_dep; intros.
apply functional_extensionality; intros. auto.
subst g; auto.
Qed.

End FIX.



Section FIXM.

Variables A B: Type.
Variable measure: A -> nat.
Variable F: forall (x: A), (forall (y: A), measure y < measure x -> B) -> B.

Definition Fixm (x: A) : B := Wf.Fix (well_founded_ltof A measure) (fun (x: A) => B) F x.

Theorem unroll_Fixm:
forall x, Fixm x = F (fun (y: A) (P: measure y < measure x) => Fixm y).
Proof. hammer_hook "Wfsimpl" "Wfsimpl.unroll_Fixm".
unfold Fixm; intros. apply Wf.Fix_eq with (P := fun (x: A) => B).
intros. assert (f = g). apply functional_extensionality_dep; intros.
apply functional_extensionality; intros. auto.
subst g; auto.
Qed.

End FIXM.


