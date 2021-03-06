From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import AST.
From compcert Require Import Maps.
From compcert Require Import Ordered.
Require FSetAVL.
From compcert Require Import Values.

Definition reg: Type := positive.

Module Reg.

Definition eq := peq.

Definition typenv := PMap.t typ.

End Reg.



Module Regmap := PMap.

Set Implicit Arguments.

Definition regmap_optget
(A: Type) (or: option reg) (dfl: A) (rs: Regmap.t A) : A :=
match or with
| None => dfl
| Some r => Regmap.get r rs
end.

Definition regmap_optset
(A: Type) (or: option reg) (v: A) (rs: Regmap.t A) : Regmap.t A :=
match or with
| None => rs
| Some r => Regmap.set r v rs
end.

Definition regmap_setres
(A: Type) (res: builtin_res reg) (v: A) (rs: Regmap.t A) : Regmap.t A :=
match res with
| BR r => Regmap.set r v rs
| _ => rs
end.

Notation "a # b" := (Regmap.get b a) (at level 1) : rtl.
Notation "a ## b" := (List.map (fun r => Regmap.get r a) b) (at level 1) : rtl.
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level) : rtl.

Open Scope rtl.



Definition regs_lessdef (rs1 rs2: Regmap.t val) : Prop :=
forall r, Val.lessdef (rs1#r) (rs2#r).

Lemma regs_lessdef_regs:
forall rs1 rs2, regs_lessdef rs1 rs2 ->
forall rl, Val.lessdef_list rs1##rl rs2##rl.
Proof. hammer_hook "Registers" "Registers.regs_lessdef_regs".
induction rl; constructor; auto.
Qed.

Lemma set_reg_lessdef:
forall r v1 v2 rs1 rs2,
Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 -> regs_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof. hammer_hook "Registers" "Registers.set_reg_lessdef".
intros; red; intros. repeat rewrite Regmap.gsspec.
destruct (peq r0 r); auto.
Qed.

Lemma set_res_lessdef:
forall res v1 v2 rs1 rs2,
Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 ->
regs_lessdef (regmap_setres res v1 rs1) (regmap_setres res v2 rs2).
Proof. hammer_hook "Registers" "Registers.set_res_lessdef".
intros. destruct res; simpl; auto. apply set_reg_lessdef; auto.
Qed.



Module Regset := FSetAVL.Make(OrderedPositive).
