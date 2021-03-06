From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import AST.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Op.
From compcert Require Import Registers.
From compcert Require Import RTL.



Definition valnum := positive.

Inductive rhs : Type :=
| Op: operation -> list valnum -> rhs
| Load: memory_chunk -> addressing -> list valnum -> rhs.

Inductive equation : Type :=
| Eq (v: valnum) (strict: bool) (r: rhs).

Definition eq_valnum: forall (x y: valnum), {x=y}+{x<>y} := peq.

Definition eq_list_valnum: forall (x y: list valnum), {x=y}+{x<>y} := list_eq_dec peq.

Definition eq_rhs (x y: rhs) : {x=y}+{x<>y}.
Proof. hammer_hook "CSEdomain" "CSEdomain.eq_rhs".
generalize chunk_eq eq_operation eq_addressing eq_valnum eq_list_valnum.
decide equality.
Defined.



Record numbering : Type := mknumbering {
num_next: valnum;
num_eqs: list equation;
num_reg: PTree.t valnum;
num_val: PMap.t (list reg)
}.

Definition empty_numbering :=
{| num_next := 1%positive;
num_eqs  := nil;
num_reg  := PTree.empty _;
num_val  := PMap.init nil |}.



Definition valnums_rhs (r: rhs): list valnum :=
match r with
| Op op vl => vl
| Load chunk addr vl => vl
end.

Definition wf_rhs (next: valnum) (r: rhs) : Prop :=
forall v, In v (valnums_rhs r) -> Plt v next.

Definition wf_equation (next: valnum) (e: equation) : Prop :=
match e with Eq l str r => Plt l next /\ wf_rhs next r end.

Record wf_numbering (n: numbering) : Prop := {
wf_num_eqs: forall e,
In e n.(num_eqs) -> wf_equation n.(num_next) e;
wf_num_reg: forall r v,
PTree.get r n.(num_reg) = Some v -> Plt v n.(num_next);
wf_num_val: forall r v,
In r (PMap.get v n.(num_val)) -> PTree.get r n.(num_reg) = Some v
}.

Hint Resolve wf_num_eqs wf_num_reg wf_num_val: cse.



Definition valuation := valnum -> val.

Inductive rhs_eval_to (valu: valuation) (ge: genv) (sp: val) (m: mem):
rhs -> val -> Prop :=
| op_eval_to: forall op vl v,
eval_operation ge sp op (map valu vl) m = Some v ->
rhs_eval_to valu ge sp m (Op op vl) v
| load_eval_to: forall chunk addr vl a v,
eval_addressing ge sp addr (map valu vl) = Some a ->
Mem.loadv chunk m a = Some v ->
rhs_eval_to valu ge sp m (Load chunk addr vl) v.

Inductive equation_holds (valu: valuation) (ge: genv) (sp: val) (m: mem):
equation -> Prop :=
| eq_holds_strict: forall l r,
rhs_eval_to valu ge sp m r (valu l) ->
equation_holds valu ge sp m (Eq l true r)
| eq_holds_lessdef: forall l r v,
rhs_eval_to valu ge sp m r v -> Val.lessdef v (valu l) ->
equation_holds valu ge sp m (Eq l false r).

Record numbering_holds (valu: valuation) (ge: genv) (sp: val)
(rs: regset) (m: mem) (n: numbering) : Prop := {
num_holds_wf:
wf_numbering n;
num_holds_eq: forall eq,
In eq n.(num_eqs) -> equation_holds valu ge sp m eq;
num_holds_reg: forall r v,
n.(num_reg)!r = Some v -> rs#r = valu v
}.

Hint Resolve num_holds_wf num_holds_eq num_holds_reg: cse.

Lemma empty_numbering_holds:
forall valu ge sp rs m,
numbering_holds valu ge sp rs m empty_numbering.
Proof. hammer_hook "CSEdomain" "CSEdomain.empty_numbering_holds".
intros; split; simpl; intros.
- split; simpl; intros.
+ contradiction.
+ rewrite PTree.gempty in H; discriminate.
+ rewrite PMap.gi in H; contradiction.
- contradiction.
- rewrite PTree.gempty in H; discriminate.
Qed.

