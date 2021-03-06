From Hammer Require Import Hammer.


















From compcert Require Import Coqlib.
From compcert Require Import Errors.
From compcert Require Import Maps.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import Values.
From compcert Require Import AST.
From compcert Require Import Memory.
From compcert Require Import Events.
From compcert Require Import Globalenvs.
From compcert Require Import Smallstep.
From compcert Require Import Ctypes.
From compcert Require Import Cop.







Inductive expr : Type :=
| Econst_int: int -> type -> expr
| Econst_float: float -> type -> expr
| Econst_single: float32 -> type -> expr
| Econst_long: int64 -> type -> expr
| Evar: ident -> type -> expr
| Etempvar: ident -> type -> expr
| Ederef: expr -> type -> expr
| Eaddrof: expr -> type -> expr
| Eunop: unary_operation -> expr -> type -> expr
| Ebinop: binary_operation -> expr -> expr -> type -> expr
| Ecast: expr -> type -> expr
| Efield: expr -> ident -> type -> expr
| Esizeof: type -> type -> expr
| Ealignof: type -> type -> expr.



Definition typeof (e: expr) : type :=
match e with
| Econst_int _ ty => ty
| Econst_float _ ty => ty
| Econst_single _ ty => ty
| Econst_long _ ty => ty
| Evar _ ty => ty
| Etempvar _ ty => ty
| Ederef _ ty => ty
| Eaddrof _ ty => ty
| Eunop _ _ ty => ty
| Ebinop _ _ _ ty => ty
| Ecast _ ty => ty
| Efield _ _ ty => ty
| Esizeof _ ty => ty
| Ealignof _ ty => ty
end.





Definition label := ident.

Inductive statement : Type :=
| Sskip : statement
| Sassign : expr -> expr -> statement
| Sset : ident -> expr -> statement
| Scall: option ident -> expr -> list expr -> statement
| Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement
| Ssequence : statement -> statement -> statement
| Sifthenelse : expr  -> statement -> statement -> statement
| Sloop: statement -> statement -> statement
| Sbreak : statement
| Scontinue : statement
| Sreturn : option expr -> statement
| Sswitch : expr -> labeled_statements -> statement
| Slabel : label -> statement -> statement
| Sgoto : label -> statement

with labeled_statements : Type :=
| LSnil: labeled_statements
| LScons: option Z -> statement -> labeled_statements -> labeled_statements.




Definition Swhile (e: expr) (s: statement) :=
Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

Definition Sdowhile (s: statement) (e: expr) :=
Sloop s (Sifthenelse e Sskip Sbreak).

Definition Sfor (s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).





Record function : Type := mkfunction {
fn_return: type;
fn_callconv: calling_convention;
fn_params: list (ident * type);
fn_vars: list (ident * type);
fn_temps: list (ident * type);
fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
List.map (@fst ident type) vars.



Definition fundef := Ctypes.fundef function.



Definition type_of_function (f: function) : type :=
Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
match f with
| Internal fd => type_of_function fd
| External id args res cc => Tfunction args res cc
end.





Definition program := Ctypes.program function.





Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.

Definition globalenv (p: program) :=
{| genv_genv := Genv.globalenv p; genv_cenv := p.(prog_comp_env) |}.



Definition env := PTree.t (block * type).

Definition empty_env: env := (PTree.empty (block * type)).



Definition temp_env := PTree.t val.



Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) : val -> Prop :=
| deref_loc_value: forall chunk v,
access_mode ty = By_value chunk ->
Mem.loadv chunk m (Vptr b ofs) = Some v ->
deref_loc ty m b ofs v
| deref_loc_reference:
access_mode ty = By_reference ->
deref_loc ty m b ofs (Vptr b ofs)
| deref_loc_copy:
access_mode ty = By_copy ->
deref_loc ty m b ofs (Vptr b ofs).



Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs):
val -> mem -> Prop :=
| assign_loc_value: forall v chunk m',
access_mode ty = By_value chunk ->
Mem.storev chunk m (Vptr b ofs) v = Some m' ->
assign_loc ce ty m b ofs v m'
| assign_loc_copy: forall b' ofs' bytes m',
access_mode ty = By_copy ->
(sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
(sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
\/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
\/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
assign_loc ce ty m b ofs (Vptr b' ofs') m'.

Section SEMANTICS.

Variable ge: genv.



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
assign_loc ge ty m b Ptrofs.zero v1 m1 ->
bind_parameters e m1 params vl m2 ->
bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.



Fixpoint create_undef_temps (temps: list (ident * type)) : temp_env :=
match temps with
| nil => PTree.empty val
| (id, t) :: temps' => PTree.set id Vundef (create_undef_temps temps')
end.



Fixpoint bind_parameter_temps (formals: list (ident * type)) (args: list val)
(le: temp_env) : option temp_env :=
match formals, args with
| nil, nil => Some le
| (id, t) :: xl, v :: vl => bind_parameter_temps xl vl (PTree.set id v le)
| _, _ => None
end.



Definition block_of_binding (id_b_ty: ident * (block * type)) :=
match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ge ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
List.map block_of_binding (PTree.elements e).



Definition set_opttemp (optid: option ident) (v: val) (le: temp_env) :=
match optid with
| None => le
| Some id => PTree.set id v le
end.



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



Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.



Inductive eval_expr: expr -> val -> Prop :=
| eval_Econst_int:   forall i ty,
eval_expr (Econst_int i ty) (Vint i)
| eval_Econst_float:   forall f ty,
eval_expr (Econst_float f ty) (Vfloat f)
| eval_Econst_single:   forall f ty,
eval_expr (Econst_single f ty) (Vsingle f)
| eval_Econst_long:   forall i ty,
eval_expr (Econst_long i ty) (Vlong i)
| eval_Etempvar:  forall id ty v,
le!id = Some v ->
eval_expr (Etempvar id ty) v
| eval_Eaddrof: forall a ty loc ofs,
eval_lvalue a loc ofs ->
eval_expr (Eaddrof a ty) (Vptr loc ofs)
| eval_Eunop:  forall op a ty v1 v,
eval_expr a v1 ->
sem_unary_operation op v1 (typeof a) m = Some v ->
eval_expr (Eunop op a ty) v
| eval_Ebinop: forall op a1 a2 ty v1 v2 v,
eval_expr a1 v1 ->
eval_expr a2 v2 ->
sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
eval_expr (Ebinop op a1 a2 ty) v
| eval_Ecast:   forall a ty v1 v,
eval_expr a v1 ->
sem_cast v1 (typeof a) ty m = Some v ->
eval_expr (Ecast a ty) v
| eval_Esizeof: forall ty1 ty,
eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
| eval_Ealignof: forall ty1 ty,
eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
| eval_Elvalue: forall a loc ofs v,
eval_lvalue a loc ofs ->
deref_loc (typeof a) m loc ofs v ->
eval_expr a v



with eval_lvalue: expr -> block -> ptrofs -> Prop :=
| eval_Evar_local:   forall id l ty,
e!id = Some(l, ty) ->
eval_lvalue (Evar id ty) l Ptrofs.zero
| eval_Evar_global: forall id l ty,
e!id = None ->
Genv.find_symbol ge id = Some l ->
eval_lvalue (Evar id ty) l Ptrofs.zero
| eval_Ederef: forall a ty l ofs,
eval_expr a (Vptr l ofs) ->
eval_lvalue (Ederef a ty) l ofs
| eval_Efield_struct:   forall a i ty l ofs id co att delta,
eval_expr a (Vptr l ofs) ->
typeof a = Tstruct id att ->
ge.(genv_cenv)!id = Some co ->
field_offset ge i (co_members co) = OK delta ->
eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta))
| eval_Efield_union:   forall a i ty l ofs id co att,
eval_expr a (Vptr l ofs) ->
typeof a = Tunion id att ->
ge.(genv_cenv)!id = Some co ->
eval_lvalue (Efield a i ty) l ofs.

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.



Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
| eval_Enil:
eval_exprlist nil Tnil nil
| eval_Econs:   forall a bl ty tyl v1 v2 vl,
eval_expr a v1 ->
sem_cast v1 (typeof a) ty m = Some v2 ->
eval_exprlist bl tyl vl ->
eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

End EXPR.





Inductive cont: Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop1: statement -> statement -> cont -> cont
| Kloop2: statement -> statement -> cont -> cont
| Kswitch: cont -> cont
| Kcall: option ident ->
function ->
env ->
temp_env ->
cont -> cont.



Fixpoint call_cont (k: cont) : cont :=
match k with
| Kseq s k => call_cont k
| Kloop1 s1 s2 k => call_cont k
| Kloop2 s1 s2 k => call_cont k
| Kswitch k => call_cont k
| _ => k
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
(le: temp_env)
(m: mem) : state
| Callstate
(fd: fundef)
(args: list val)
(k: cont)
(m: mem) : state
| Returnstate
(res: val)
(k: cont)
(m: mem) : state.



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
| Sloop s1 s2 =>
match find_label lbl s1 (Kloop1 s1 s2 k) with
| Some sk => Some sk
| None => find_label lbl s2 (Kloop2 s1 s2 k)
end
| Sswitch e sl =>
find_label_ls lbl sl (Kswitch k)
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



Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.



Inductive step: state -> trace -> state -> Prop :=

| step_assign:   forall f a1 a2 k e le m loc ofs v2 v m',
eval_lvalue e le m a1 loc ofs ->
eval_expr e le m a2 v2 ->
sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
assign_loc ge (typeof a1) m loc ofs v m' ->
step (State f (Sassign a1 a2) k e le m)
E0 (State f Sskip k e le m')

| step_set:   forall f id a k e le m v,
eval_expr e le m a v ->
step (State f (Sset id a) k e le m)
E0 (State f Sskip k e (PTree.set id v le) m)

| step_call:   forall f optid a al k e le m tyargs tyres cconv vf vargs fd,
classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
eval_expr e le m a vf ->
eval_exprlist e le m al tyargs vargs ->
Genv.find_funct ge vf = Some fd ->
type_of_fundef fd = Tfunction tyargs tyres cconv ->
step (State f (Scall optid a al) k e le m)
E0 (Callstate fd vargs (Kcall optid f e le k) m)

| step_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
eval_exprlist e le m al tyargs vargs ->
external_call ef ge vargs m t vres m' ->
step (State f (Sbuiltin optid ef tyargs al) k e le m)
t (State f Sskip k e (set_opttemp optid vres le) m')

| step_seq:  forall f s1 s2 k e le m,
step (State f (Ssequence s1 s2) k e le m)
E0 (State f s1 (Kseq s2 k) e le m)
| step_skip_seq: forall f s k e le m,
step (State f Sskip (Kseq s k) e le m)
E0 (State f s k e le m)
| step_continue_seq: forall f s k e le m,
step (State f Scontinue (Kseq s k) e le m)
E0 (State f Scontinue k e le m)
| step_break_seq: forall f s k e le m,
step (State f Sbreak (Kseq s k) e le m)
E0 (State f Sbreak k e le m)

| step_ifthenelse:  forall f a s1 s2 k e le m v1 b,
eval_expr e le m a v1 ->
bool_val v1 (typeof a) m = Some b ->
step (State f (Sifthenelse a s1 s2) k e le m)
E0 (State f (if b then s1 else s2) k e le m)

| step_loop: forall f s1 s2 k e le m,
step (State f (Sloop s1 s2) k e le m)
E0 (State f s1 (Kloop1 s1 s2 k) e le m)
| step_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
x = Sskip \/ x = Scontinue ->
step (State f x (Kloop1 s1 s2 k) e le m)
E0 (State f s2 (Kloop2 s1 s2 k) e le m)
| step_break_loop1:  forall f s1 s2 k e le m,
step (State f Sbreak (Kloop1 s1 s2 k) e le m)
E0 (State f Sskip k e le m)
| step_skip_loop2: forall f s1 s2 k e le m,
step (State f Sskip (Kloop2 s1 s2 k) e le m)
E0 (State f (Sloop s1 s2) k e le m)
| step_break_loop2: forall f s1 s2 k e le m,
step (State f Sbreak (Kloop2 s1 s2 k) e le m)
E0 (State f Sskip k e le m)

| step_return_0: forall f k e le m m',
Mem.free_list m (blocks_of_env e) = Some m' ->
step (State f (Sreturn None) k e le m)
E0 (Returnstate Vundef (call_cont k) m')
| step_return_1: forall f a k e le m v v' m',
eval_expr e le m a v ->
sem_cast v (typeof a) f.(fn_return) m = Some v' ->
Mem.free_list m (blocks_of_env e) = Some m' ->
step (State f (Sreturn (Some a)) k e le m)
E0 (Returnstate v' (call_cont k) m')
| step_skip_call: forall f k e le m m',
is_call_cont k ->
Mem.free_list m (blocks_of_env e) = Some m' ->
step (State f Sskip k e le m)
E0 (Returnstate Vundef k m')

| step_switch: forall f a sl k e le m v n,
eval_expr e le m a v ->
sem_switch_arg v (typeof a) = Some n ->
step (State f (Sswitch a sl) k e le m)
E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
| step_skip_break_switch: forall f x k e le m,
x = Sskip \/ x = Sbreak ->
step (State f x (Kswitch k) e le m)
E0 (State f Sskip k e le m)
| step_continue_switch: forall f k e le m,
step (State f Scontinue (Kswitch k) e le m)
E0 (State f Scontinue k e le m)

| step_label: forall f lbl s k e le m,
step (State f (Slabel lbl s) k e le m)
E0 (State f s k e le m)

| step_goto: forall f lbl k e le m s' k',
find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
step (State f (Sgoto lbl) k e le m)
E0 (State f s' k' e le m)

| step_internal_function: forall f vargs k m e le m1,
function_entry f vargs m e le m1 ->
step (Callstate (Internal f) vargs k m)
E0 (State f f.(fn_body) k e le m1)

| step_external_function: forall ef targs tres cconv vargs k m vres t m',
external_call ef ge vargs m t vres m' ->
step (Callstate (External ef targs tres cconv) vargs k m)
t (Returnstate vres k m')

| step_returnstate: forall v optid f e le k m,
step (Returnstate v (Kcall optid f e le k) m)
E0 (State f Sskip k e (set_opttemp optid v le) m).





Inductive initial_state (p: program): state -> Prop :=
| initial_state_intro: forall b f m0,
let ge := Genv.globalenv p in
Genv.init_mem p = Some m0 ->
Genv.find_symbol ge p.(prog_main) = Some b ->
Genv.find_funct_ptr ge b = Some f ->
type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
initial_state p (Callstate f nil Kstop m0).



Inductive final_state: state -> int -> Prop :=
| final_state_intro: forall r m,
final_state (Returnstate (Vint r) Kstop m) r.

End SEMANTICS.



Inductive function_entry1 (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
| function_entry1_intro: forall m1,
list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
bind_parameters ge e m1 f.(fn_params) vargs m' ->
le = create_undef_temps f.(fn_temps) ->
function_entry1 ge f vargs m e le m'.

Definition step1 (ge: genv) := step ge (function_entry1 ge).



Inductive function_entry2 (ge: genv)  (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
| function_entry2_intro:
list_norepet (var_names f.(fn_vars)) ->
list_norepet (var_names f.(fn_params)) ->
list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
alloc_variables ge empty_env m f.(fn_vars) e m' ->
bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
function_entry2 ge f vargs m e le m'.

Definition step2 (ge: genv) := step ge (function_entry2 ge).



Definition semantics1 (p: program) :=
let ge := globalenv p in
Semantics_gen step1 (initial_state p) final_state ge ge.

Definition semantics2 (p: program) :=
let ge := globalenv p in
Semantics_gen step2 (initial_state p) final_state ge ge.



Lemma semantics_receptive:
forall (p: program), receptive (semantics1 p).
Proof. hammer_hook "Clight" "Clight.semantics_receptive".
intros. unfold semantics1.
set (ge := globalenv p). constructor; simpl; intros.

assert (t1 = E0 -> exists s2, step1 ge s t2 s2).
intros. subst. inv H0. exists s1; auto.
inversion H; subst; auto.

exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
econstructor; econstructor; eauto.

exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
exists (Returnstate vres2 k m2). econstructor; eauto.

red; simpl; intros. inv H; simpl; try omega.
eapply external_call_trace_length; eauto.
eapply external_call_trace_length; eauto.
Qed.
