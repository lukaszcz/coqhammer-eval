From Hammer Require Import Hammer.


















From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import Events.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Smallstep.
From compcert Require Import Switch.





Inductive constant : Type :=
| Ointconst: int -> constant
| Ofloatconst: float -> constant
| Osingleconst: float32 -> constant
| Olongconst: int64 -> constant
| Oaddrsymbol: ident -> ptrofs -> constant
| Oaddrstack: ptrofs -> constant.

Inductive unary_operation : Type :=
| Ocast8unsigned: unary_operation
| Ocast8signed: unary_operation
| Ocast16unsigned: unary_operation
| Ocast16signed: unary_operation
| Onegint: unary_operation
| Onotint: unary_operation
| Onegf: unary_operation
| Oabsf: unary_operation
| Onegfs: unary_operation
| Oabsfs: unary_operation
| Osingleoffloat: unary_operation
| Ofloatofsingle: unary_operation
| Ointoffloat: unary_operation
| Ointuoffloat: unary_operation
| Ofloatofint: unary_operation
| Ofloatofintu: unary_operation
| Ointofsingle: unary_operation
| Ointuofsingle: unary_operation
| Osingleofint: unary_operation
| Osingleofintu: unary_operation
| Onegl: unary_operation
| Onotl: unary_operation
| Ointoflong: unary_operation
| Olongofint: unary_operation
| Olongofintu: unary_operation
| Olongoffloat: unary_operation
| Olonguoffloat: unary_operation
| Ofloatoflong: unary_operation
| Ofloatoflongu: unary_operation
| Olongofsingle: unary_operation
| Olonguofsingle: unary_operation
| Osingleoflong: unary_operation
| Osingleoflongu: unary_operation.

Inductive binary_operation : Type :=
| Oadd: binary_operation
| Osub: binary_operation
| Omul: binary_operation
| Odiv: binary_operation
| Odivu: binary_operation
| Omod: binary_operation
| Omodu: binary_operation
| Oand: binary_operation
| Oor: binary_operation
| Oxor: binary_operation
| Oshl: binary_operation
| Oshr: binary_operation
| Oshru: binary_operation
| Oaddf: binary_operation
| Osubf: binary_operation
| Omulf: binary_operation
| Odivf: binary_operation
| Oaddfs: binary_operation
| Osubfs: binary_operation
| Omulfs: binary_operation
| Odivfs: binary_operation
| Oaddl: binary_operation
| Osubl: binary_operation
| Omull: binary_operation
| Odivl: binary_operation
| Odivlu: binary_operation
| Omodl: binary_operation
| Omodlu: binary_operation
| Oandl: binary_operation
| Oorl: binary_operation
| Oxorl: binary_operation
| Oshll: binary_operation
| Oshrl: binary_operation
| Oshrlu: binary_operation
| Ocmp: comparison -> binary_operation
| Ocmpu: comparison -> binary_operation
| Ocmpf: comparison -> binary_operation
| Ocmpfs: comparison -> binary_operation
| Ocmpl: comparison -> binary_operation
| Ocmplu: comparison -> binary_operation.



Inductive expr : Type :=
| Evar : ident -> expr
| Econst : constant -> expr
| Eunop : unary_operation -> expr -> expr
| Ebinop : binary_operation -> expr -> expr -> expr
| Eload : memory_chunk -> expr -> expr.



Definition label := ident.

Inductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sstore : memory_chunk -> expr -> expr -> stmt
| Scall : option ident -> signature -> expr -> list expr -> stmt
| Stailcall: signature -> expr -> list expr -> stmt
| Sbuiltin : option ident -> external_function -> list expr -> stmt
| Sseq: stmt -> stmt -> stmt
| Sifthenelse: expr -> stmt -> stmt -> stmt
| Sloop: stmt -> stmt
| Sblock: stmt -> stmt
| Sexit: nat -> stmt
| Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt.



Record function : Type := mkfunction {
fn_sig: signature;
fn_params: list ident;
fn_vars: list ident;
fn_stackspace: Z;
fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
match fd with
| Internal f => fn_sig f
| External ef => ef_sig ef
end.





Definition genv := Genv.t fundef unit.
Definition env := PTree.t val.



Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
match il, vl with
| i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
| i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
| _, _ => PTree.empty val
end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
match il with
| nil => e
| i1 :: is => PTree.set i1 Vundef (set_locals is e)
end.

Definition set_optvar (optid: option ident) (v: val) (e: env) : env :=
match optid with
| None => e
| Some id => PTree.set id v e
end.



Inductive cont: Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont
| Kblock: cont -> cont
| Kcall: option ident -> function -> val -> env -> cont -> cont.




Inductive state: Type :=
| State:
forall (f: function)
(s: stmt)
(k: cont)
(sp: val)
(e: env)
(m: mem),
state
| Callstate:
forall (f: fundef)
(args: list val)
(k: cont)
(m: mem),
state
| Returnstate:
forall (v: val)
(k: cont)
(m: mem),
state.

Section RELSEM.

Variable ge: genv.



Definition eval_constant (sp: val) (cst: constant) : option val :=
match cst with
| Ointconst n => Some (Vint n)
| Ofloatconst n => Some (Vfloat n)
| Osingleconst n => Some (Vsingle n)
| Olongconst n => Some (Vlong n)
| Oaddrsymbol s ofs => Some (Genv.symbol_address ge s ofs)
| Oaddrstack ofs => Some (Val.offset_ptr sp ofs)
end.

Definition eval_unop (op: unary_operation) (arg: val) : option val :=
match op with
| Ocast8unsigned => Some (Val.zero_ext 8 arg)
| Ocast8signed => Some (Val.sign_ext 8 arg)
| Ocast16unsigned => Some (Val.zero_ext 16 arg)
| Ocast16signed => Some (Val.sign_ext 16 arg)
| Onegint => Some (Val.negint arg)
| Onotint => Some (Val.notint arg)
| Onegf => Some (Val.negf arg)
| Oabsf => Some (Val.absf arg)
| Onegfs => Some (Val.negfs arg)
| Oabsfs => Some (Val.absfs arg)
| Osingleoffloat => Some (Val.singleoffloat arg)
| Ofloatofsingle => Some (Val.floatofsingle arg)
| Ointoffloat => Val.intoffloat arg
| Ointuoffloat => Val.intuoffloat arg
| Ofloatofint => Val.floatofint arg
| Ofloatofintu => Val.floatofintu arg
| Ointofsingle => Val.intofsingle arg
| Ointuofsingle => Val.intuofsingle arg
| Osingleofint => Val.singleofint arg
| Osingleofintu => Val.singleofintu arg
| Onegl => Some (Val.negl arg)
| Onotl => Some (Val.notl arg)
| Ointoflong => Some (Val.loword arg)
| Olongofint => Some (Val.longofint arg)
| Olongofintu => Some (Val.longofintu arg)
| Olongoffloat => Val.longoffloat arg
| Olonguoffloat => Val.longuoffloat arg
| Ofloatoflong => Val.floatoflong arg
| Ofloatoflongu => Val.floatoflongu arg
| Olongofsingle => Val.longofsingle arg
| Olonguofsingle => Val.longuofsingle arg
| Osingleoflong => Val.singleoflong arg
| Osingleoflongu => Val.singleoflongu arg
end.

Definition eval_binop
(op: binary_operation) (arg1 arg2: val) (m: mem): option val :=
match op with
| Oadd => Some (Val.add arg1 arg2)
| Osub => Some (Val.sub arg1 arg2)
| Omul => Some (Val.mul arg1 arg2)
| Odiv => Val.divs arg1 arg2
| Odivu => Val.divu arg1 arg2
| Omod => Val.mods arg1 arg2
| Omodu => Val.modu arg1 arg2
| Oand => Some (Val.and arg1 arg2)
| Oor => Some (Val.or arg1 arg2)
| Oxor => Some (Val.xor arg1 arg2)
| Oshl => Some (Val.shl arg1 arg2)
| Oshr => Some (Val.shr arg1 arg2)
| Oshru => Some (Val.shru arg1 arg2)
| Oaddf => Some (Val.addf arg1 arg2)
| Osubf => Some (Val.subf arg1 arg2)
| Omulf => Some (Val.mulf arg1 arg2)
| Odivf => Some (Val.divf arg1 arg2)
| Oaddfs => Some (Val.addfs arg1 arg2)
| Osubfs => Some (Val.subfs arg1 arg2)
| Omulfs => Some (Val.mulfs arg1 arg2)
| Odivfs => Some (Val.divfs arg1 arg2)
| Oaddl => Some (Val.addl arg1 arg2)
| Osubl => Some (Val.subl arg1 arg2)
| Omull => Some (Val.mull arg1 arg2)
| Odivl => Val.divls arg1 arg2
| Odivlu => Val.divlu arg1 arg2
| Omodl => Val.modls arg1 arg2
| Omodlu => Val.modlu arg1 arg2
| Oandl => Some (Val.andl arg1 arg2)
| Oorl => Some (Val.orl arg1 arg2)
| Oxorl => Some (Val.xorl arg1 arg2)
| Oshll => Some (Val.shll arg1 arg2)
| Oshrl => Some (Val.shrl arg1 arg2)
| Oshrlu => Some (Val.shrlu arg1 arg2)
| Ocmp c => Some (Val.cmp c arg1 arg2)
| Ocmpu c => Some (Val.cmpu (Mem.valid_pointer m) c arg1 arg2)
| Ocmpf c => Some (Val.cmpf c arg1 arg2)
| Ocmpfs c => Some (Val.cmpfs c arg1 arg2)
| Ocmpl c => Val.cmpl c arg1 arg2
| Ocmplu c => Val.cmplu (Mem.valid_pointer m) c arg1 arg2
end.



Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
| eval_Evar: forall id v,
PTree.get id e = Some v ->
eval_expr (Evar id) v
| eval_Econst: forall cst v,
eval_constant sp cst = Some v ->
eval_expr (Econst cst) v
| eval_Eunop: forall op a1 v1 v,
eval_expr a1 v1 ->
eval_unop op v1 = Some v ->
eval_expr (Eunop op a1) v
| eval_Ebinop: forall op a1 a2 v1 v2 v,
eval_expr a1 v1 ->
eval_expr a2 v2 ->
eval_binop op v1 v2 m = Some v ->
eval_expr (Ebinop op a1 a2) v
| eval_Eload: forall chunk addr vaddr v,
eval_expr addr vaddr ->
Mem.loadv chunk m vaddr = Some v ->
eval_expr (Eload chunk addr) v.

Inductive eval_exprlist: list expr -> list val -> Prop :=
| eval_Enil:
eval_exprlist nil nil
| eval_Econs: forall a1 al v1 vl,
eval_expr a1 v1 -> eval_exprlist al vl ->
eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.



Fixpoint call_cont (k: cont) : cont :=
match k with
| Kseq s k => call_cont k
| Kblock k => call_cont k
| _ => k
end.

Definition is_call_cont (k: cont) : Prop :=
match k with
| Kstop => True
| Kcall _ _ _ _ _ => True
| _ => False
end.



Fixpoint find_label (lbl: label) (s: stmt) (k: cont)
{struct s}: option (stmt * cont) :=
match s with
| Sseq s1 s2 =>
match find_label lbl s1 (Kseq s2 k) with
| Some sk => Some sk
| None => find_label lbl s2 k
end
| Sifthenelse a s1 s2 =>
match find_label lbl s1 k with
| Some sk => Some sk
| None => find_label lbl s2 k
end
| Sloop s1 =>
find_label lbl s1 (Kseq (Sloop s1) k)
| Sblock s1 =>
find_label lbl s1 (Kblock k)
| Slabel lbl' s' =>
if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
| _ => None
end.



Inductive step: state -> trace -> state -> Prop :=

| step_skip_seq: forall f s k sp e m,
step (State f Sskip (Kseq s k) sp e m)
E0 (State f s k sp e m)
| step_skip_block: forall f k sp e m,
step (State f Sskip (Kblock k) sp e m)
E0 (State f Sskip k sp e m)
| step_skip_call: forall f k sp e m m',
is_call_cont k ->
Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
E0 (Returnstate Vundef k m')

| step_assign: forall f id a k sp e m v,
eval_expr sp e m a v ->
step (State f (Sassign id a) k sp e m)
E0 (State f Sskip k sp (PTree.set id v e) m)

| step_store: forall f chunk addr a k sp e m vaddr v m',
eval_expr sp e m addr vaddr ->
eval_expr sp e m a v ->
Mem.storev chunk m vaddr v = Some m' ->
step (State f (Sstore chunk addr a) k sp e m)
E0 (State f Sskip k sp e m')

| step_call: forall f optid sig a bl k sp e m vf vargs fd,
eval_expr sp e m a vf ->
eval_exprlist sp e m bl vargs ->
Genv.find_funct ge vf = Some fd ->
funsig fd = sig ->
step (State f (Scall optid sig a bl) k sp e m)
E0 (Callstate fd vargs (Kcall optid f sp e k) m)

| step_tailcall: forall f sig a bl k sp e m vf vargs fd m',
eval_expr (Vptr sp Ptrofs.zero) e m a vf ->
eval_exprlist (Vptr sp Ptrofs.zero) e m bl vargs ->
Genv.find_funct ge vf = Some fd ->
funsig fd = sig ->
Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
step (State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e m)
E0 (Callstate fd vargs (call_cont k) m')

| step_builtin: forall f optid ef bl k sp e m vargs t vres m',
eval_exprlist sp e m bl vargs ->
external_call ef ge vargs m t vres m' ->
step (State f (Sbuiltin optid ef bl) k sp e m)
t (State f Sskip k sp (set_optvar optid vres e) m')

| step_seq: forall f s1 s2 k sp e m,
step (State f (Sseq s1 s2) k sp e m)
E0 (State f s1 (Kseq s2 k) sp e m)

| step_ifthenelse: forall f a s1 s2 k sp e m v b,
eval_expr sp e m a v ->
Val.bool_of_val v b ->
step (State f (Sifthenelse a s1 s2) k sp e m)
E0 (State f (if b then s1 else s2) k sp e m)

| step_loop: forall f s k sp e m,
step (State f (Sloop s) k sp e m)
E0 (State f s (Kseq (Sloop s) k) sp e m)

| step_block: forall f s k sp e m,
step (State f (Sblock s) k sp e m)
E0 (State f s (Kblock k) sp e m)

| step_exit_seq: forall f n s k sp e m,
step (State f (Sexit n) (Kseq s k) sp e m)
E0 (State f (Sexit n) k sp e m)
| step_exit_block_0: forall f k sp e m,
step (State f (Sexit O) (Kblock k) sp e m)
E0 (State f Sskip k sp e m)
| step_exit_block_S: forall f n k sp e m,
step (State f (Sexit (S n)) (Kblock k) sp e m)
E0 (State f (Sexit n) k sp e m)

| step_switch: forall f islong a cases default k sp e m v n,
eval_expr sp e m a v ->
switch_argument islong v n ->
step (State f (Sswitch islong a cases default) k sp e m)
E0 (State f (Sexit (switch_target n default cases)) k sp e m)

| step_return_0: forall f k sp e m m',
Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
E0 (Returnstate Vundef (call_cont k) m')
| step_return_1: forall f a k sp e m v m',
eval_expr (Vptr sp Ptrofs.zero) e m a v ->
Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
step (State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e m)
E0 (Returnstate v (call_cont k) m')

| step_label: forall f lbl s k sp e m,
step (State f (Slabel lbl s) k sp e m)
E0 (State f s k sp e m)

| step_goto: forall f lbl k sp e m s' k',
find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
step (State f (Sgoto lbl) k sp e m)
E0 (State f s' k' sp e m)

| step_internal_function: forall f vargs k m m' sp e,
Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
step (Callstate (Internal f) vargs k m)
E0 (State f f.(fn_body) k (Vptr sp Ptrofs.zero) e m')
| step_external_function: forall ef vargs k m t vres m',
external_call ef ge vargs m t vres m' ->
step (Callstate (External ef) vargs k m)
t (Returnstate vres k m')

| step_return: forall v optid f sp e k m,
step (Returnstate v (Kcall optid f sp e k) m)
E0 (State f Sskip k sp (set_optvar optid v e) m).

End RELSEM.



Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
let ge := Genv.globalenv p in
Genv.init_mem p = Some m0 ->
Genv.find_symbol ge p.(prog_main) = Some b ->
Genv.find_funct_ptr ge b = Some f ->
funsig f = signature_main ->
initial_state p (Callstate f nil Kstop m0).



Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
final_state (Returnstate (Vint r) Kstop m) r.



Definition semantics (p: program) :=
Semantics step (initial_state p) final_state (Genv.globalenv p).



Lemma semantics_receptive:
forall (p: program), receptive (semantics p).
Proof. hammer_hook "Cminor" "Cminor.semantics_receptive".
intros. constructor; simpl; intros.

assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
intros. subst. inv H0. exists s1; auto.
inversion H; subst; auto.
exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
exists (State f Sskip k sp (set_optvar optid vres2 e) m2). econstructor; eauto.
exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
exists (Returnstate vres2 k m2). econstructor; eauto.

red; intros; inv H; simpl; try omega; eapply external_call_trace_length; eauto.
Qed.



Lemma eval_expr_determ:
forall ge sp e m a v, eval_expr ge sp e m a v ->
forall v', eval_expr ge sp e m a v' -> v' = v.
Proof. hammer_hook "Cminor" "Cminor.eval_expr_determ".
induction 1; intros v' E'; inv E'.
- congruence.
- congruence.
- assert (v0 = v1) by eauto. congruence.
- assert (v0 = v1) by eauto. assert (v3 = v2) by eauto. congruence.
- assert (vaddr0 = vaddr) by eauto. congruence.
Qed.

Lemma eval_exprlist_determ:
forall ge sp e m al vl, eval_exprlist ge sp e m al vl ->
forall vl', eval_exprlist ge sp e m al vl' -> vl' = vl.
Proof. hammer_hook "Cminor" "Cminor.eval_exprlist_determ".
induction 1; intros vl' E'; inv E'.
- auto.
- f_equal; eauto using eval_expr_determ.
Qed.

Ltac Determ :=
try congruence;
match goal with
| [ |- match_traces _ E0 E0 /\ (_ -> _) ]  =>
split; [constructor|intros _; Determ]
| [ H: is_call_cont ?k |- _ ] =>
contradiction || (clear H; Determ)
| [ H1: eval_expr _ _ _ _ ?a ?v1, H2: eval_expr _ _ _ _ ?a ?v2 |- _ ] =>
assert (v1 = v2) by (eapply eval_expr_determ; eauto);
clear H1 H2; Determ
| [ H1: eval_exprlist _ _ _ _ ?a ?v1, H2: eval_exprlist _ _ _ _ ?a ?v2 |- _ ] =>
assert (v1 = v2) by (eapply eval_exprlist_determ; eauto);
clear H1 H2; Determ
| _ => idtac
end.

Lemma semantics_determinate:
forall (p: program), determinate (semantics p).
Proof. hammer_hook "Cminor" "Cminor.semantics_determinate".
intros. constructor; set (ge := Genv.globalenv p); simpl; intros.
-
inv H; inv H0; Determ.
+ subst vargs0. exploit external_call_determ. eexact H2. eexact H13.
intros (A & B). split; intros; auto.
apply B in H; destruct H; congruence.
+ subst v0. assert (b0 = b) by (inv H2; inv H13; auto). subst b0; auto.
+ assert (n0 = n) by (inv H2; inv H14; auto). subst n0; auto.
+ exploit external_call_determ. eexact H1. eexact H7.
intros (A & B). split; intros; auto.
apply B in H; destruct H; congruence.
-
red; simpl. destruct 1; simpl; try omega;
eapply external_call_trace_length; eauto.
-
inv H; inv H0. unfold ge0, ge1 in *. congruence.
-
red; intros; red; intros. inv H; inv H0.
-
inv H; inv H0; auto.
Qed.





Inductive outcome: Type :=
| Out_normal: outcome
| Out_exit: nat -> outcome
| Out_return: option val -> outcome
| Out_tailcall_return: val -> outcome.

Definition outcome_block (out: outcome) : outcome :=
match out with
| Out_exit O => Out_normal
| Out_exit (S n) => Out_exit n
| out => out
end.

Definition outcome_result_value
(out: outcome) (retsig: option typ) (vres: val) : Prop :=
match out with
| Out_normal => vres = Vundef
| Out_return None => vres = Vundef
| Out_return (Some v) => retsig <> None /\ vres = v
| Out_tailcall_return v => vres = v
| _ => False
end.

Definition outcome_free_mem
(out: outcome) (m: mem) (sp: block) (sz: Z) (m': mem) :=
match out with
| Out_tailcall_return _ => m' = m
| _ => Mem.free m sp 0 sz = Some m'
end.

Section NATURALSEM.

Variable ge: genv.



Inductive eval_funcall:
mem -> fundef -> list val -> trace ->
mem -> val -> Prop :=
| eval_funcall_internal:
forall m f vargs m1 sp e t e2 m2 out vres m3,
Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
exec_stmt f (Vptr sp Ptrofs.zero) e m1 f.(fn_body) t e2 m2 out ->
outcome_result_value out f.(fn_sig).(sig_res) vres ->
outcome_free_mem out m2 sp f.(fn_stackspace) m3 ->
eval_funcall m (Internal f) vargs t m3 vres
| eval_funcall_external:
forall ef m args t res m',
external_call ef ge args m t res m' ->
eval_funcall m (External ef) args t m' res



with exec_stmt:
function -> val ->
env -> mem -> stmt -> trace ->
env -> mem -> outcome -> Prop :=
| exec_Sskip:
forall f sp e m,
exec_stmt f sp e m Sskip E0 e m Out_normal
| exec_Sassign:
forall f sp e m id a v,
eval_expr ge sp e m a v ->
exec_stmt f sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal
| exec_Sstore:
forall f sp e m chunk addr a vaddr v m',
eval_expr ge sp e m addr vaddr ->
eval_expr ge sp e m a v ->
Mem.storev chunk m vaddr v = Some m' ->
exec_stmt f sp e m (Sstore chunk addr a) E0 e m' Out_normal
| exec_Scall:
forall f sp e m optid sig a bl vf vargs fd t m' vres e',
eval_expr ge sp e m a vf ->
eval_exprlist ge sp e m bl vargs ->
Genv.find_funct ge vf = Some fd ->
funsig fd = sig ->
eval_funcall m fd vargs t m' vres ->
e' = set_optvar optid vres e ->
exec_stmt f sp e m (Scall optid sig a bl) t e' m' Out_normal
| exec_Sbuiltin:
forall f sp e m optid ef bl t m' vargs vres e',
eval_exprlist ge sp e m bl vargs ->
external_call ef ge vargs m t vres m' ->
e' = set_optvar optid vres e ->
exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' Out_normal
| exec_Sifthenelse:
forall f sp e m a s1 s2 v b t e' m' out,
eval_expr ge sp e m a v ->
Val.bool_of_val v b ->
exec_stmt f sp e m (if b then s1 else s2) t e' m' out ->
exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out
| exec_Sseq_continue:
forall f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out,
exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
exec_stmt f sp e1 m1 s2 t2 e2 m2 out ->
t = t1 ** t2 ->
exec_stmt f sp e m (Sseq s1 s2) t e2 m2 out
| exec_Sseq_stop:
forall f sp e m t s1 s2 e1 m1 out,
exec_stmt f sp e m s1 t e1 m1 out ->
out <> Out_normal ->
exec_stmt f sp e m (Sseq s1 s2) t e1 m1 out
| exec_Sloop_loop:
forall f sp e m s t t1 e1 m1 t2 e2 m2 out,
exec_stmt f sp e m s t1 e1 m1 Out_normal ->
exec_stmt f sp e1 m1 (Sloop s) t2 e2 m2 out ->
t = t1 ** t2 ->
exec_stmt f sp e m (Sloop s) t e2 m2 out
| exec_Sloop_stop:
forall f sp e m t s e1 m1 out,
exec_stmt f sp e m s t e1 m1 out ->
out <> Out_normal ->
exec_stmt f sp e m (Sloop s) t e1 m1 out
| exec_Sblock:
forall f sp e m s t e1 m1 out,
exec_stmt f sp e m s t e1 m1 out ->
exec_stmt f sp e m (Sblock s) t e1 m1 (outcome_block out)
| exec_Sexit:
forall f sp e m n,
exec_stmt f sp e m (Sexit n) E0 e m (Out_exit n)
| exec_Sswitch:
forall f sp e m islong a cases default v n,
eval_expr ge sp e m a v ->
switch_argument islong v n ->
exec_stmt f sp e m (Sswitch islong a cases default)
E0 e m (Out_exit (switch_target n default cases))
| exec_Sreturn_none:
forall f sp e m,
exec_stmt f sp e m (Sreturn None) E0 e m (Out_return None)
| exec_Sreturn_some:
forall f sp e m a v,
eval_expr ge sp e m a v ->
exec_stmt f sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v))
| exec_Stailcall:
forall f sp e m sig a bl vf vargs fd t m' m'' vres,
eval_expr ge (Vptr sp Ptrofs.zero) e m a vf ->
eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs ->
Genv.find_funct ge vf = Some fd ->
funsig fd = sig ->
Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
eval_funcall m' fd vargs t m'' vres ->
exec_stmt f (Vptr sp Ptrofs.zero) e m (Stailcall sig a bl) t e m'' (Out_tailcall_return vres).

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop.
Combined Scheme eval_funcall_exec_stmt_ind2
from eval_funcall_ind2, exec_stmt_ind2.



CoInductive evalinf_funcall:
mem -> fundef -> list val -> traceinf -> Prop :=
| evalinf_funcall_internal:
forall m f vargs m1 sp e t,
Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
execinf_stmt f (Vptr sp Ptrofs.zero) e m1 f.(fn_body) t ->
evalinf_funcall m (Internal f) vargs t



with execinf_stmt:
function -> val -> env -> mem -> stmt -> traceinf -> Prop :=
| execinf_Scall:
forall f sp e m optid sig a bl vf vargs fd t,
eval_expr ge sp e m a vf ->
eval_exprlist ge sp e m bl vargs ->
Genv.find_funct ge vf = Some fd ->
funsig fd = sig ->
evalinf_funcall m fd vargs t ->
execinf_stmt f sp e m (Scall optid sig a bl) t
| execinf_Sifthenelse:
forall f sp e m a s1 s2 v b t,
eval_expr ge sp e m a v ->
Val.bool_of_val v b ->
execinf_stmt f sp e m (if b then s1 else s2) t ->
execinf_stmt f sp e m (Sifthenelse a s1 s2) t
| execinf_Sseq_1:
forall f sp e m t s1 s2,
execinf_stmt f sp e m s1 t ->
execinf_stmt f sp e m (Sseq s1 s2) t
| execinf_Sseq_2:
forall f sp e m t s1 t1 e1 m1 s2 t2,
exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
execinf_stmt f sp e1 m1 s2 t2 ->
t = t1 *** t2 ->
execinf_stmt f sp e m (Sseq s1 s2) t
| execinf_Sloop_body:
forall f sp e m s t,
execinf_stmt f sp e m s t ->
execinf_stmt f sp e m (Sloop s) t
| execinf_Sloop_loop:
forall f sp e m s t t1 e1 m1 t2,
exec_stmt f sp e m s t1 e1 m1 Out_normal ->
execinf_stmt f sp e1 m1 (Sloop s) t2 ->
t = t1 *** t2 ->
execinf_stmt f sp e m (Sloop s) t
| execinf_Sblock:
forall f sp e m s t,
execinf_stmt f sp e m s t ->
execinf_stmt f sp e m (Sblock s) t
| execinf_Stailcall:
forall f sp e m sig a bl vf vargs fd m' t,
eval_expr ge (Vptr sp Ptrofs.zero) e m a vf ->
eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs ->
Genv.find_funct ge vf = Some fd ->
funsig fd = sig ->
Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
evalinf_funcall m' fd vargs t ->
execinf_stmt f (Vptr sp Ptrofs.zero) e m (Stailcall sig a bl) t.

End NATURALSEM.



Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
| bigstep_program_terminates_intro:
forall b f m0 t m r,
let ge := Genv.globalenv p in
Genv.init_mem p = Some m0 ->
Genv.find_symbol ge p.(prog_main) = Some b ->
Genv.find_funct_ptr ge b = Some f ->
funsig f = signature_main ->
eval_funcall ge m0 f nil t m (Vint r) ->
bigstep_program_terminates p t r.

Inductive bigstep_program_diverges (p: program): traceinf -> Prop :=
| bigstep_program_diverges_intro:
forall b f m0 t,
let ge := Genv.globalenv p in
Genv.init_mem p = Some m0 ->
Genv.find_symbol ge p.(prog_main) = Some b ->
Genv.find_funct_ptr ge b = Some f ->
funsig f = signature_main ->
evalinf_funcall ge m0 f nil t ->
bigstep_program_diverges p t.

Definition bigstep_semantics (p: program) :=
Bigstep_semantics (bigstep_program_terminates p) (bigstep_program_diverges p).



Section BIGSTEP_TO_TRANSITION.

Variable prog: program.
Let ge := Genv.globalenv prog.

Inductive outcome_state_match
(sp: val) (e: env) (m: mem) (f: function) (k: cont):
outcome -> state -> Prop :=
| osm_normal:
outcome_state_match sp e m f k
Out_normal
(State f Sskip k sp e m)
| osm_exit: forall n,
outcome_state_match sp e m f k
(Out_exit n)
(State f (Sexit n) k sp e m)
| osm_return_none: forall k',
call_cont k' = call_cont k ->
outcome_state_match sp e m f k
(Out_return None)
(State f (Sreturn None) k' sp e m)
| osm_return_some: forall k' a v,
call_cont k' = call_cont k ->
eval_expr ge sp e m a v ->
outcome_state_match sp e m f k
(Out_return (Some v))
(State f (Sreturn (Some a)) k' sp e m)
| osm_tail: forall v,
outcome_state_match sp e m f k
(Out_tailcall_return v)
(Returnstate v (call_cont k) m).

Remark is_call_cont_call_cont:
forall k, is_call_cont (call_cont k).
Proof. hammer_hook "Cminor" "Cminor.is_call_cont_call_cont".
induction k; simpl; auto.
Qed.

Remark call_cont_is_call_cont:
forall k, is_call_cont k -> call_cont k = k.
Proof. hammer_hook "Cminor" "Cminor.call_cont_is_call_cont".
destruct k; simpl; intros; auto || contradiction.
Qed.

Lemma eval_funcall_exec_stmt_steps:
(forall m fd args t m' res,
eval_funcall ge m fd args t m' res ->
forall k,
is_call_cont k ->
star step ge (Callstate fd args k m)
t (Returnstate res k m'))
/\(forall f sp e m s t e' m' out,
exec_stmt ge f sp e m s t e' m' out ->
forall k,
exists S,
star step ge (State f s k sp e m) t S
/\ outcome_state_match sp e' m' f k out S).
Proof. hammer_hook "Cminor" "Cminor.eval_funcall_exec_stmt_steps".
apply eval_funcall_exec_stmt_ind2; intros.


destruct (H2 k) as [S [A B]].
assert (call_cont k = k) by (apply call_cont_is_call_cont; auto).
eapply star_left. econstructor; eauto.
eapply star_trans. eexact A.
inversion B; clear B; subst out; simpl in H3; simpl; try contradiction.

subst vres. apply star_one. apply step_skip_call; auto.

subst vres. replace k with (call_cont k') by congruence.
apply star_one. apply step_return_0; auto.

destruct H3. subst vres.
replace k with (call_cont k') by congruence.
apply star_one. eapply step_return_1; eauto.

subst vres. red in H4. subst m3. rewrite H6. apply star_refl.

reflexivity. traceEq.


apply star_one. constructor; auto.


econstructor; split.
apply star_refl.
constructor.


exists (State f Sskip k sp (PTree.set id v e) m); split.
apply star_one. constructor. auto.
constructor.


econstructor; split.
apply star_one. econstructor; eauto.
constructor.


econstructor; split.
eapply star_left. econstructor; eauto.
eapply star_right. apply H4. red; auto.
constructor. reflexivity. traceEq.
subst e'. constructor.


econstructor; split.
apply star_one. econstructor; eauto.
subst e'. constructor.


destruct (H2 k) as [S [A B]].
exists S; split.
apply star_left with E0 (State f (if b then s1 else s2) k sp e m) t.
econstructor; eauto. exact A.
traceEq.
auto.


destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
destruct (H2 k) as [S2 [A2 B2]].
inv B1.
exists S2; split.
eapply star_left. constructor.
eapply star_trans. eexact A1.
eapply star_left. constructor. eexact A2.
reflexivity. reflexivity. traceEq.
auto.


destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
set (S2 :=
match out with
| Out_exit n => State f (Sexit n) k sp e1 m1
| _ => S1
end).
exists S2; split.
eapply star_left. constructor. eapply star_trans. eexact A1.
unfold S2; destruct out; try (apply star_refl).
inv B1. apply star_one. constructor.
reflexivity. traceEq.
unfold S2; inv B1; congruence || simpl; constructor; auto.


destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
destruct (H2 k) as [S2 [A2 B2]].
inv B1.
exists S2; split.
eapply star_left. constructor.
eapply star_trans. eexact A1.
eapply star_left. constructor. eexact A2.
reflexivity. reflexivity. traceEq.
auto.


destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
set (S2 :=
match out with
| Out_exit n => State f (Sexit n) k sp e1 m1
| _ => S1
end).
exists S2; split.
eapply star_left. constructor. eapply star_trans. eexact A1.
unfold S2; destruct out; try (apply star_refl).
inv B1. apply star_one. constructor.
reflexivity. traceEq.
unfold S2; inv B1; congruence || simpl; constructor; auto.


destruct (H0 (Kblock k)) as [S1 [A1 B1]].
set (S2 :=
match out with
| Out_normal => State f Sskip k sp e1 m1
| Out_exit O => State f Sskip k sp e1 m1
| Out_exit (S m) => State f (Sexit m) k sp e1 m1
| _ => S1
end).
exists S2; split.
eapply star_left. constructor. eapply star_trans. eexact A1.
unfold S2; destruct out; try (apply star_refl).
inv B1. apply star_one. constructor.
inv B1. apply star_one. destruct n; constructor.
reflexivity. traceEq.
unfold S2; inv B1; simpl; try constructor; auto.
destruct n; constructor.


econstructor; split. apply star_refl. constructor.


econstructor; split.
apply star_one. econstructor; eauto. constructor.


econstructor; split. apply star_refl. constructor; auto.


econstructor; split. apply star_refl. constructor; auto.


econstructor; split.
eapply star_left. econstructor; eauto.
apply H5. apply is_call_cont_call_cont. traceEq.
econstructor.
Qed.

Lemma eval_funcall_steps:
forall m fd args t m' res,
eval_funcall ge m fd args t m' res ->
forall k,
is_call_cont k ->
star step ge (Callstate fd args k m)
t (Returnstate res k m').
Proof. hammer_hook "Cminor" "Cminor.eval_funcall_steps". exact ((proj1 eval_funcall_exec_stmt_steps)). Qed.

Lemma exec_stmt_steps:
forall f sp e m s t e' m' out,
exec_stmt ge f sp e m s t e' m' out ->
forall k,
exists S,
star step ge (State f s k sp e m) t S
/\ outcome_state_match sp e' m' f k out S.
Proof. hammer_hook "Cminor" "Cminor.exec_stmt_steps". exact ((proj2 eval_funcall_exec_stmt_steps)). Qed.

Lemma evalinf_funcall_forever:
forall m fd args T k,
evalinf_funcall ge m fd args T ->
forever_plus step ge (Callstate fd args k m) T.
Proof. hammer_hook "Cminor" "Cminor.evalinf_funcall_forever".
cofix CIH_FUN.
assert (forall sp e m s T f k,
execinf_stmt ge f sp e m s T ->
forever_plus step ge (State f s k sp e m) T).
cofix CIH_STMT.
intros. inv H.


eapply forever_plus_intro.
apply plus_one. econstructor; eauto.
apply CIH_FUN. eauto. traceEq.


eapply forever_plus_intro with (s2 := State f (if b then s1 else s2) k sp e m).
apply plus_one. econstructor; eauto.
apply CIH_STMT. eauto. traceEq.


eapply forever_plus_intro.
apply plus_one. constructor.
apply CIH_STMT. eauto. traceEq.


destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq s2 k))
as [S [A B]]. inv B.
eapply forever_plus_intro.
eapply plus_left. constructor.
eapply star_right. eexact A. constructor.
reflexivity. reflexivity.
apply CIH_STMT. eauto. traceEq.


eapply forever_plus_intro.
apply plus_one. econstructor; eauto.
apply CIH_STMT. eauto. traceEq.


destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq (Sloop s0) k))
as [S [A B]]. inv B.
eapply forever_plus_intro.
eapply plus_left. constructor.
eapply star_right. eexact A. constructor.
reflexivity. reflexivity.
apply CIH_STMT. eauto. traceEq.


eapply forever_plus_intro.
apply plus_one. econstructor; eauto.
apply CIH_STMT. eauto. traceEq.


eapply forever_plus_intro.
apply plus_one. econstructor; eauto.
apply CIH_FUN. eauto. traceEq.


intros. inv H0.
eapply forever_plus_intro.
apply plus_one. econstructor; eauto.
apply H. eauto.
traceEq.
Qed.

Theorem bigstep_semantics_sound:
bigstep_sound (bigstep_semantics prog) (semantics prog).
Proof. hammer_hook "Cminor" "Cminor.bigstep_semantics_sound".
constructor; intros.

inv H. econstructor; econstructor.
split. econstructor; eauto.
split. apply eval_funcall_steps. eauto. red; auto.
econstructor.

inv H. econstructor.
split. econstructor; eauto.
eapply forever_plus_forever.
eapply evalinf_funcall_forever; eauto.
Qed.

End BIGSTEP_TO_TRANSITION.
