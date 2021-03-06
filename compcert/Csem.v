From Hammer Require Import Hammer.


















From compcert Require Import Coqlib.
From compcert Require Import Errors.
From compcert Require Import Maps.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import Values.
From compcert Require Import AST.
From compcert Require Import Memory.
From compcert Require Import Builtins.
From compcert Require Import Events.
From compcert Require Import Globalenvs.
From compcert Require Import Ctypes.
From compcert Require Import Cop.
From compcert Require Import Csyntax.
From compcert Require Import Smallstep.





Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.

Definition globalenv (p: program) :=
{| genv_genv := Genv.globalenv p; genv_cenv := p.(prog_comp_env) |}.



Definition env := PTree.t (block * type).

Definition empty_env: env := (PTree.empty (block * type)).


Section SEMANTICS.

Variable ge: genv.



Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) : trace -> val -> Prop :=
| deref_loc_value: forall chunk v,
access_mode ty = By_value chunk ->
type_is_volatile ty = false ->
Mem.loadv chunk m (Vptr b ofs) = Some v ->
deref_loc ty m b ofs E0 v
| deref_loc_volatile: forall chunk t v,
access_mode ty = By_value chunk -> type_is_volatile ty = true ->
volatile_load ge chunk m b ofs t v ->
deref_loc ty m b ofs t v
| deref_loc_reference:
access_mode ty = By_reference ->
deref_loc ty m b ofs E0 (Vptr b ofs)
| deref_loc_copy:
access_mode ty = By_copy ->
deref_loc ty m b ofs E0 (Vptr b ofs).



Inductive assign_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs):
val -> trace -> mem -> Prop :=
| assign_loc_value: forall v chunk m',
access_mode ty = By_value chunk ->
type_is_volatile ty = false ->
Mem.storev chunk m (Vptr b ofs) v = Some m' ->
assign_loc ty m b ofs v E0 m'
| assign_loc_volatile: forall v chunk t m',
access_mode ty = By_value chunk -> type_is_volatile ty = true ->
volatile_store ge chunk m b ofs v t m' ->
assign_loc ty m b ofs v t m'
| assign_loc_copy: forall b' ofs' bytes m',
access_mode ty = By_copy ->
(alignof_blockcopy ge ty | Ptrofs.unsigned ofs') ->
(alignof_blockcopy ge ty | Ptrofs.unsigned ofs) ->
b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
\/ Ptrofs.unsigned ofs' + sizeof ge ty <= Ptrofs.unsigned ofs
\/ Ptrofs.unsigned ofs + sizeof ge ty <= Ptrofs.unsigned ofs' ->
Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ge ty) = Some bytes ->
Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
assign_loc ty m b ofs (Vptr b' ofs') E0 m'.



Inductive alloc_variables: env -> mem ->
list (ident * type) ->
env -> mem -> Prop :=
| alloc_variables_nil:
forall e m,
alloc_variables e m nil e m
| alloc_variables_cons:
forall e m id ty vars m1 b1 m2 e2,
Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
alloc_variables e m ((id, ty) :: vars) e2 m2.



Inductive bind_parameters (e: env):
mem -> list (ident * type) -> list val ->
mem -> Prop :=
| bind_parameters_nil:
forall m,
bind_parameters e m nil nil m
| bind_parameters_cons:
forall m id ty params v1 vl b m1 m2,
PTree.get id e = Some(b, ty) ->
assign_loc ty m b Ptrofs.zero v1 E0 m1 ->
bind_parameters e m1 params vl m2 ->
bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.



Definition block_of_binding (id_b_ty: ident * (block * type)) :=
match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ge ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
List.map block_of_binding (PTree.elements e).



Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
match sl with
| LSnil => sl
| LScons None s sl' => sl
| LScons (Some i) s sl' => select_switch_default sl'
end.

Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
match sl with
| LSnil => None
| LScons None s sl' => select_switch_case n sl'
| LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
end.

Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
match select_switch_case n sl with
| Some sl' => sl'
| None => select_switch_default sl
end.



Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
match sl with
| LSnil => Sskip
| LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
end.



Inductive cast_arguments (m: mem): exprlist -> typelist -> list val -> Prop :=
| cast_args_nil:
cast_arguments m Enil Tnil nil
| cast_args_cons: forall v ty el targ1 targs v1 vl,
sem_cast v ty targ1 m = Some v1 -> cast_arguments m el targs vl ->
cast_arguments m (Econs (Eval v ty) el) (Tcons targ1 targs) (v1 :: vl).



Section EXPR.

Variable e: env.





Inductive lred: expr -> mem -> expr -> mem -> Prop :=
| red_var_local: forall x ty m b,
e!x = Some(b, ty) ->
lred (Evar x ty) m
(Eloc b Ptrofs.zero ty) m
| red_var_global: forall x ty m b,
e!x = None ->
Genv.find_symbol ge x = Some b ->
lred (Evar x ty) m
(Eloc b Ptrofs.zero ty) m
| red_deref: forall b ofs ty1 ty m,
lred (Ederef (Eval (Vptr b ofs) ty1) ty) m
(Eloc b ofs ty) m
| red_field_struct: forall b ofs id co a f ty m delta,
ge.(genv_cenv)!id = Some co ->
field_offset ge f (co_members co) = OK delta ->
lred (Efield (Eval (Vptr b ofs) (Tstruct id a)) f ty) m
(Eloc b (Ptrofs.add ofs (Ptrofs.repr delta)) ty) m
| red_field_union: forall b ofs id co a f ty m,
ge.(genv_cenv)!id = Some co ->
lred (Efield (Eval (Vptr b ofs) (Tunion id a)) f ty) m
(Eloc b ofs ty) m.



Inductive rred: expr -> mem -> trace -> expr -> mem -> Prop :=
| red_rvalof: forall b ofs ty m t v,
deref_loc ty m b ofs t v ->
rred (Evalof (Eloc b ofs ty) ty) m
t (Eval v ty) m
| red_addrof: forall b ofs ty1 ty m,
rred (Eaddrof (Eloc b ofs ty1) ty) m
E0 (Eval (Vptr b ofs) ty) m
| red_unop: forall op v1 ty1 ty m v,
sem_unary_operation op v1 ty1 m = Some v ->
rred (Eunop op (Eval v1 ty1) ty) m
E0 (Eval v ty) m
| red_binop: forall op v1 ty1 v2 ty2 ty m v,
sem_binary_operation ge op v1 ty1 v2 ty2 m = Some v ->
rred (Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty) m
E0 (Eval v ty) m
| red_cast: forall ty v1 ty1 m v,
sem_cast v1 ty1 ty m = Some v ->
rred (Ecast (Eval v1 ty1) ty) m
E0 (Eval v ty) m
| red_seqand_true: forall v1 ty1 r2 ty m,
bool_val v1 ty1 m = Some true ->
rred (Eseqand (Eval v1 ty1) r2 ty) m
E0 (Eparen r2 type_bool ty) m
| red_seqand_false: forall v1 ty1 r2 ty m,
bool_val v1 ty1 m = Some false ->
rred (Eseqand (Eval v1 ty1) r2 ty) m
E0 (Eval (Vint Int.zero) ty) m
| red_seqor_true: forall v1 ty1 r2 ty m,
bool_val v1 ty1 m = Some true ->
rred (Eseqor (Eval v1 ty1) r2 ty) m
E0 (Eval (Vint Int.one) ty) m
| red_seqor_false: forall v1 ty1 r2 ty m,
bool_val v1 ty1 m = Some false ->
rred (Eseqor (Eval v1 ty1) r2 ty) m
E0 (Eparen r2 type_bool ty) m
| red_condition: forall v1 ty1 r1 r2 ty b m,
bool_val v1 ty1 m = Some b ->
rred (Econdition (Eval v1 ty1) r1 r2 ty) m
E0 (Eparen (if b then r1 else r2) ty ty) m
| red_sizeof: forall ty1 ty m,
rred (Esizeof ty1 ty) m
E0 (Eval (Vptrofs (Ptrofs.repr (sizeof ge ty1))) ty) m
| red_alignof: forall ty1 ty m,
rred (Ealignof ty1 ty) m
E0 (Eval (Vptrofs (Ptrofs.repr (alignof ge ty1))) ty) m
| red_assign: forall b ofs ty1 v2 ty2 m v t m',
sem_cast v2 ty2 ty1 m = Some v ->
assign_loc ty1 m b ofs v t m' ->
rred (Eassign (Eloc b ofs ty1) (Eval v2 ty2) ty1) m
t (Eval v ty1) m'
| red_assignop: forall op b ofs ty1 v2 ty2 tyres m t v1,
deref_loc ty1 m b ofs t v1 ->
rred (Eassignop op (Eloc b ofs ty1) (Eval v2 ty2) tyres ty1) m
t (Eassign (Eloc b ofs ty1)
(Ebinop op (Eval v1 ty1) (Eval v2 ty2) tyres) ty1) m
| red_postincr: forall id b ofs ty m t v1 op,
deref_loc ty m b ofs t v1 ->
op = match id with Incr => Oadd | Decr => Osub end ->
rred (Epostincr id (Eloc b ofs ty) ty) m
t (Ecomma (Eassign (Eloc b ofs ty)
(Ebinop op (Eval v1 ty)
(Eval (Vint Int.one) type_int32s)
(incrdecr_type ty))
ty)
(Eval v1 ty) ty) m
| red_comma: forall v ty1 r2 ty m,
typeof r2 = ty ->
rred (Ecomma (Eval v ty1) r2 ty) m
E0 r2 m
| red_paren: forall v1 ty1 ty2 ty m v,
sem_cast v1 ty1 ty2 m = Some v ->
rred (Eparen (Eval v1 ty1) ty2 ty) m
E0 (Eval v ty) m
| red_builtin: forall ef tyargs el ty m vargs t vres m',
cast_arguments m el tyargs vargs ->
external_call ef ge vargs m t vres m' ->
rred (Ebuiltin ef tyargs el ty) m
t (Eval vres ty) m'.




Inductive callred: expr -> mem -> fundef -> list val -> type -> Prop :=
| red_call: forall vf tyf m tyargs tyres cconv el ty fd vargs,
Genv.find_funct ge vf = Some fd ->
cast_arguments m el tyargs vargs ->
type_of_fundef fd = Tfunction tyargs tyres cconv ->
classify_fun tyf = fun_case_f tyargs tyres cconv ->
callred (Ecall (Eval vf tyf) el ty) m
fd vargs ty.



Inductive kind : Type := LV | RV.

Inductive context: kind -> kind -> (expr -> expr) -> Prop :=
| ctx_top: forall k,
context k k (fun x => x)
| ctx_deref: forall k C ty,
context k RV C -> context k LV (fun x => Ederef (C x) ty)
| ctx_field: forall k C f ty,
context k RV C -> context k LV (fun x => Efield (C x) f ty)
| ctx_rvalof: forall k C ty,
context k LV C -> context k RV (fun x => Evalof (C x) ty)
| ctx_addrof: forall k C ty,
context k LV C -> context k RV (fun x => Eaddrof (C x) ty)
| ctx_unop: forall k C op ty,
context k RV C -> context k RV (fun x => Eunop op (C x) ty)
| ctx_binop_left: forall k C op e2 ty,
context k RV C -> context k RV (fun x => Ebinop op (C x) e2 ty)
| ctx_binop_right: forall k C op e1 ty,
context k RV C -> context k RV (fun x => Ebinop op e1 (C x) ty)
| ctx_cast: forall k C ty,
context k RV C -> context k RV (fun x => Ecast (C x) ty)
| ctx_seqand: forall k C r2 ty,
context k RV C -> context k RV (fun x => Eseqand (C x) r2 ty)
| ctx_seqor: forall k C r2 ty,
context k RV C -> context k RV (fun x => Eseqor (C x) r2 ty)
| ctx_condition: forall k C r2 r3 ty,
context k RV C -> context k RV (fun x => Econdition (C x) r2 r3 ty)
| ctx_assign_left: forall k C e2 ty,
context k LV C -> context k RV (fun x => Eassign (C x) e2 ty)
| ctx_assign_right: forall k C e1 ty,
context k RV C -> context k RV (fun x => Eassign e1 (C x) ty)
| ctx_assignop_left: forall k C op e2 tyres ty,
context k LV C -> context k RV (fun x => Eassignop op (C x) e2 tyres ty)
| ctx_assignop_right: forall k C op e1 tyres ty,
context k RV C -> context k RV (fun x => Eassignop op e1 (C x) tyres ty)
| ctx_postincr: forall k C id ty,
context k LV C -> context k RV (fun x => Epostincr id (C x) ty)
| ctx_call_left: forall k C el ty,
context k RV C -> context k RV (fun x => Ecall (C x) el ty)
| ctx_call_right: forall k C e1 ty,
contextlist k C -> context k RV (fun x => Ecall e1 (C x) ty)
| ctx_builtin: forall k C ef tyargs ty,
contextlist k C -> context k RV (fun x => Ebuiltin ef tyargs (C x) ty)
| ctx_comma: forall k C e2 ty,
context k RV C -> context k RV (fun x => Ecomma (C x) e2 ty)
| ctx_paren: forall k C tycast ty,
context k RV C -> context k RV (fun x => Eparen (C x) tycast ty)

with contextlist: kind -> (expr -> exprlist) -> Prop :=
| ctx_list_head: forall k C el,
context k RV C -> contextlist k (fun x => Econs (C x) el)
| ctx_list_tail: forall k C e1,
contextlist k C -> contextlist k (fun x => Econs e1 (C x)).



Inductive imm_safe: kind -> expr -> mem -> Prop :=
| imm_safe_val: forall v ty m,
imm_safe RV (Eval v ty) m
| imm_safe_loc: forall b ofs ty m,
imm_safe LV (Eloc b ofs ty) m
| imm_safe_lred: forall to C e m e' m',
lred e m e' m' ->
context LV to C ->
imm_safe to (C e) m
| imm_safe_rred: forall to C e m t e' m',
rred e m t e' m' ->
context RV to C ->
imm_safe to (C e) m
| imm_safe_callred: forall to C e m fd args ty,
callred e m fd args ty ->
context RV to C ->
imm_safe to (C e) m.

Definition not_stuck (e: expr) (m: mem) : Prop :=
forall k C e' ,
context k RV C -> e = C e' -> imm_safe k e' m.





Lemma red_selection:
forall v1 ty1 v2 ty2 v3 ty3 ty m b v2' v3',
ty <> Tvoid ->
bool_val v1 ty1 m = Some b ->
sem_cast v2 ty2 ty m = Some v2' ->
sem_cast v3 ty3 ty m = Some v3' ->
rred (Eselection (Eval v1 ty1) (Eval v2 ty2) (Eval v3 ty3) ty) m
E0 (Eval (if b then v2' else v3') ty) m.
Proof. hammer_hook "Csem" "Csem.red_selection".
intros. unfold Eselection.
set (t := typ_of_type ty).
set (sg := mksignature (AST.Tint :: t :: t :: nil) (Some t) cc_default).
assert (LK: lookup_builtin_function "__builtin_sel"%string sg = Some (BI_standard (BI_select t))).
{ unfold sg, t; destruct ty as   [ | ? ? ? | ? | [] ? | ? ? | ? ? ? | ? ? ? | ? ? | ? ? ];
simpl; unfold Tptr; destruct Archi.ptr64; reflexivity. }
set (v' := if b then v2' else v3').
assert (C: val_casted v' ty).
{ unfold v'; destruct b; eapply cast_val_is_casted; eauto. }
assert (EQ: Val.normalize v' t = v').
{ apply Val.normalize_idem. apply val_casted_has_type; auto. }
econstructor.
- constructor. rewrite cast_bool_bool_val, H0. eauto.
constructor. eauto.
constructor. eauto.
constructor.
- red. red. rewrite LK. constructor. simpl. rewrite <- EQ.
destruct b; auto.
Qed.

Lemma ctx_selection_1:
forall k C r2 r3 ty, context k RV C -> context k RV (fun x => Eselection (C x) r2 r3 ty).
Proof. hammer_hook "Csem" "Csem.ctx_selection_1".
intros. apply ctx_builtin. constructor; auto.
Qed.

Lemma ctx_selection_2:
forall k r1 C r3 ty, context k RV C -> context k RV (fun x => Eselection r1 (C x) r3 ty).
Proof. hammer_hook "Csem" "Csem.ctx_selection_2".
intros. apply ctx_builtin. constructor; constructor; auto.
Qed.

Lemma ctx_selection_3:
forall k r1 r2 C ty, context k RV C -> context k RV (fun x => Eselection r1 r2 (C x) ty).
Proof. hammer_hook "Csem" "Csem.ctx_selection_3".
intros. apply ctx_builtin. constructor; constructor; constructor; auto.
Qed.

End EXPR.





Inductive cont: Type :=
| Kstop: cont
| Kdo: cont -> cont
| Kseq: statement -> cont -> cont
| Kifthenelse: statement -> statement -> cont -> cont
| Kwhile1: expr -> statement -> cont -> cont
| Kwhile2: expr -> statement -> cont -> cont
| Kdowhile1: expr -> statement -> cont -> cont
| Kdowhile2: expr -> statement -> cont -> cont
| Kfor2: expr -> statement -> statement -> cont -> cont
| Kfor3: expr -> statement -> statement -> cont -> cont
| Kfor4: expr -> statement -> statement -> cont -> cont
| Kswitch1: labeled_statements -> cont -> cont
| Kswitch2: cont -> cont
| Kreturn: cont -> cont
| Kcall: function ->
env ->
(expr -> expr) ->
type ->
cont -> cont.



Fixpoint call_cont (k: cont) : cont :=
match k with
| Kstop => k
| Kdo k => k
| Kseq s k => call_cont k
| Kifthenelse s1 s2 k => call_cont k
| Kwhile1 e s k => call_cont k
| Kwhile2 e s k => call_cont k
| Kdowhile1 e s k => call_cont k
| Kdowhile2 e s k => call_cont k
| Kfor2 e2 e3 s k => call_cont k
| Kfor3 e2 e3 s k => call_cont k
| Kfor4 e2 e3 s k => call_cont k
| Kswitch1 ls k => call_cont k
| Kswitch2 k => call_cont k
| Kreturn k => call_cont k
| Kcall _ _ _ _ _ => k
end.

Definition is_call_cont (k: cont) : Prop :=
match k with
| Kstop => True
| Kcall _ _ _ _ _ => True
| _ => False
end.



Inductive state: Type :=
| State
(f: function)
(s: statement)
(k: cont)
(e: env)
(m: mem) : state
| ExprState
(f: function)
(r: expr)
(k: cont)
(e: env)
(m: mem) : state
| Callstate
(fd: fundef)
(args: list val)
(k: cont)
(m: mem) : state
| Returnstate
(res: val)
(k: cont)
(m: mem) : state
| Stuckstate.



Fixpoint find_label (lbl: label) (s: statement) (k: cont)
{struct s}: option (statement * cont) :=
match s with
| Ssequence s1 s2 =>
match find_label lbl s1 (Kseq s2 k) with
| Some sk => Some sk
| None => find_label lbl s2 k
end
| Sifthenelse a s1 s2 =>
match find_label lbl s1 k with
| Some sk => Some sk
| None => find_label lbl s2 k
end
| Swhile a s1 =>
find_label lbl s1 (Kwhile2 a s1 k)
| Sdowhile a s1 =>
find_label lbl s1 (Kdowhile1 a s1 k)
| Sfor a1 a2 a3 s1 =>
match find_label lbl a1 (Kseq (Sfor Sskip a2 a3 s1) k) with
| Some sk => Some sk
| None =>
match find_label lbl s1 (Kfor3 a2 a3 s1 k) with
| Some sk => Some sk
| None => find_label lbl a3 (Kfor4 a2 a3 s1 k)
end
end
| Sswitch e sl =>
find_label_ls lbl sl (Kswitch2 k)
| Slabel lbl' s' =>
if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
| _ => None
end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
{struct sl}: option (statement * cont) :=
match sl with
| LSnil => None
| LScons _ s sl' =>
match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
| Some sk => Some sk
| None => find_label_ls lbl sl' k
end
end.



Inductive estep: state -> trace -> state -> Prop :=

| step_lred: forall C f a k e m a' m',
lred e a m a' m' ->
context LV RV C ->
estep (ExprState f (C a) k e m)
E0 (ExprState f (C a') k e m')

| step_rred: forall C f a k e m t a' m',
rred a m t a' m' ->
context RV RV C ->
estep (ExprState f (C a) k e m)
t (ExprState f (C a') k e m')

| step_call: forall C f a k e m fd vargs ty,
callred a m fd vargs ty ->
context RV RV C ->
estep (ExprState f (C a) k e m)
E0 (Callstate fd vargs (Kcall f e C ty k) m)

| step_stuck: forall C f a k e m K,
context K RV C -> ~(imm_safe e K a m) ->
estep (ExprState f (C a) k e m)
E0 Stuckstate.

Inductive sstep: state -> trace -> state -> Prop :=

| step_do_1: forall f x k e m,
sstep (State f (Sdo x) k e m)
E0 (ExprState f x (Kdo k) e m)
| step_do_2: forall f v ty k e m,
sstep (ExprState f (Eval v ty) (Kdo k) e m)
E0 (State f Sskip k e m)

| step_seq:  forall f s1 s2 k e m,
sstep (State f (Ssequence s1 s2) k e m)
E0 (State f s1 (Kseq s2 k) e m)
| step_skip_seq: forall f s k e m,
sstep (State f Sskip (Kseq s k) e m)
E0 (State f s k e m)
| step_continue_seq: forall f s k e m,
sstep (State f Scontinue (Kseq s k) e m)
E0 (State f Scontinue k e m)
| step_break_seq: forall f s k e m,
sstep (State f Sbreak (Kseq s k) e m)
E0 (State f Sbreak k e m)

| step_ifthenelse_1: forall f a s1 s2 k e m,
sstep (State f (Sifthenelse a s1 s2) k e m)
E0 (ExprState f a (Kifthenelse s1 s2 k) e m)
| step_ifthenelse_2:  forall f v ty s1 s2 k e m b,
bool_val v ty m = Some b ->
sstep (ExprState f (Eval v ty) (Kifthenelse s1 s2 k) e m)
E0 (State f (if b then s1 else s2) k e m)

| step_while: forall f x s k e m,
sstep (State f (Swhile x s) k e m)
E0 (ExprState f x (Kwhile1 x s k) e m)
| step_while_false: forall f v ty x s k e m,
bool_val v ty m = Some false ->
sstep (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
E0 (State f Sskip k e m)
| step_while_true: forall f v ty x s k e m ,
bool_val v ty m = Some true ->
sstep (ExprState f (Eval v ty) (Kwhile1 x s k) e m)
E0 (State f s (Kwhile2 x s k) e m)
| step_skip_or_continue_while: forall f s0 x s k e m,
s0 = Sskip \/ s0 = Scontinue ->
sstep (State f s0 (Kwhile2 x s k) e m)
E0 (State f (Swhile x s) k e m)
| step_break_while: forall f x s k e m,
sstep (State f Sbreak (Kwhile2 x s k) e m)
E0 (State f Sskip k e m)

| step_dowhile: forall f a s k e m,
sstep (State f (Sdowhile a s) k e m)
E0 (State f s (Kdowhile1 a s k) e m)
| step_skip_or_continue_dowhile: forall f s0 x s k e m,
s0 = Sskip \/ s0 = Scontinue ->
sstep (State f s0 (Kdowhile1 x s k) e m)
E0 (ExprState f x (Kdowhile2 x s k) e m)
| step_dowhile_false: forall f v ty x s k e m,
bool_val v ty m = Some false ->
sstep (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
E0 (State f Sskip k e m)
| step_dowhile_true: forall f v ty x s k e m,
bool_val v ty m = Some true ->
sstep (ExprState f (Eval v ty) (Kdowhile2 x s k) e m)
E0 (State f (Sdowhile x s) k e m)
| step_break_dowhile: forall f a s k e m,
sstep (State f Sbreak (Kdowhile1 a s k) e m)
E0 (State f Sskip k e m)

| step_for_start: forall f a1 a2 a3 s k e m,
a1 <> Sskip ->
sstep (State f (Sfor a1 a2 a3 s) k e m)
E0 (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
| step_for: forall f a2 a3 s k e m,
sstep (State f (Sfor Sskip a2 a3 s) k e m)
E0 (ExprState f a2 (Kfor2 a2 a3 s k) e m)
| step_for_false: forall f v ty a2 a3 s k e m,
bool_val v ty m = Some false ->
sstep (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
E0 (State f Sskip k e m)
| step_for_true: forall f v ty a2 a3 s k e m,
bool_val v ty m = Some true ->
sstep (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m)
E0 (State f s (Kfor3 a2 a3 s k) e m)
| step_skip_or_continue_for3: forall f x a2 a3 s k e m,
x = Sskip \/ x = Scontinue ->
sstep (State f x (Kfor3 a2 a3 s k) e m)
E0 (State f a3 (Kfor4 a2 a3 s k) e m)
| step_break_for3: forall f a2 a3 s k e m,
sstep (State f Sbreak (Kfor3 a2 a3 s k) e m)
E0 (State f Sskip k e m)
| step_skip_for4: forall f a2 a3 s k e m,
sstep (State f Sskip (Kfor4 a2 a3 s k) e m)
E0 (State f (Sfor Sskip a2 a3 s) k e m)

| step_return_0: forall f k e m m',
Mem.free_list m (blocks_of_env e) = Some m' ->
sstep (State f (Sreturn None) k e m)
E0 (Returnstate Vundef (call_cont k) m')
| step_return_1: forall f x k e m,
sstep (State f (Sreturn (Some x)) k e m)
E0 (ExprState f x (Kreturn k) e  m)
| step_return_2:  forall f v1 ty k e m v2 m',
sem_cast v1 ty f.(fn_return) m = Some v2 ->
Mem.free_list m (blocks_of_env e) = Some m' ->
sstep (ExprState f (Eval v1 ty) (Kreturn k) e m)
E0 (Returnstate v2 (call_cont k) m')
| step_skip_call: forall f k e m m',
is_call_cont k ->
Mem.free_list m (blocks_of_env e) = Some m' ->
sstep (State f Sskip k e m)
E0 (Returnstate Vundef k m')

| step_switch: forall f x sl k e m,
sstep (State f (Sswitch x sl) k e m)
E0 (ExprState f x (Kswitch1 sl k) e m)
| step_expr_switch: forall f ty sl k e m v n,
sem_switch_arg v ty = Some n ->
sstep (ExprState f (Eval v ty) (Kswitch1 sl k) e m)
E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
| step_skip_break_switch: forall f x k e m,
x = Sskip \/ x = Sbreak ->
sstep (State f x (Kswitch2 k) e m)
E0 (State f Sskip k e m)
| step_continue_switch: forall f k e m,
sstep (State f Scontinue (Kswitch2 k) e m)
E0 (State f Scontinue k e m)

| step_label: forall f lbl s k e m,
sstep (State f (Slabel lbl s) k e m)
E0 (State f s k e m)

| step_goto: forall f lbl k e m s' k',
find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
sstep (State f (Sgoto lbl) k e m)
E0 (State f s' k' e m)

| step_internal_function: forall f vargs k m e m1 m2,
list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
bind_parameters e m1 f.(fn_params) vargs m2 ->
sstep (Callstate (Internal f) vargs k m)
E0 (State f f.(fn_body) k e m2)

| step_external_function: forall ef targs tres cc vargs k m vres t m',
external_call ef  ge vargs m t vres m' ->
sstep (Callstate (External ef targs tres cc) vargs k m)
t (Returnstate vres k m')

| step_returnstate: forall v f e C ty k m,
sstep (Returnstate v (Kcall f e C ty k) m)
E0 (ExprState f (C (Eval v ty)) k e m).

Definition step (S: state) (t: trace) (S': state) : Prop :=
estep S t S' \/ sstep S t S'.

End SEMANTICS.





Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
let ge := globalenv p in
Genv.init_mem p = Some m0 ->
Genv.find_symbol ge p.(prog_main) = Some b ->
Genv.find_funct_ptr ge b = Some f ->
type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
initial_state p (Callstate f nil Kstop m0).



Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
final_state (Returnstate (Vint r) Kstop m) r.



Definition semantics (p: program) :=
Semantics_gen step (initial_state p) final_state (globalenv p) (globalenv p).



Lemma semantics_single_events:
forall p, single_events (semantics p).
Proof. hammer_hook "Csem" "Csem.semantics_single_events".
unfold semantics; intros; red; simpl; intros.
set (ge := globalenv p) in *.
assert (DEREF: forall chunk m b ofs t v, deref_loc ge chunk m b ofs t v -> (length t <= 1)%nat).
intros. inv H0; simpl; try omega. inv H3; simpl; try omega.
assert (ASSIGN: forall chunk m b ofs t v m', assign_loc ge chunk m b ofs v t m' -> (length t <= 1)%nat).
intros. inv H0; simpl; try omega. inv H3; simpl; try omega.
destruct H.
inv H; simpl; try omega. inv H0; eauto; simpl; try omega.
eapply external_call_trace_length; eauto.
inv H; simpl; try omega. eapply external_call_trace_length; eauto.
Qed.
