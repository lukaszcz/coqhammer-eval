From Hammer Require Import Hammer.















From compcert Require Import Coqlib.
From compcert Require Errors.
From compcert Require Import Maps.
From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Switch.
From compcert Require Import Op.
From compcert Require Import Registers.
From compcert Require Import CminorSel.
From compcert Require Import RTL.

Local Open Scope string_scope.





Record mapping: Type := mkmapping {
map_vars: PTree.t reg;
map_letvars: list reg
}.



Record state: Type := mkstate {
st_nextreg: positive;
st_nextnode: positive;
st_code: code;
st_wf: forall (pc: positive), Plt pc st_nextnode \/ st_code!pc = None
}.



Inductive state_incr: state -> state -> Prop :=
state_incr_intro:
forall (s1 s2: state),
Ple s1.(st_nextnode) s2.(st_nextnode) ->
Ple s1.(st_nextreg) s2.(st_nextreg) ->
(forall pc,
s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc) ->
state_incr s1 s2.

Lemma state_incr_refl:
forall s, state_incr s s.
Proof. hammer_hook "RTLgen" "RTLgen.state_incr_refl".
intros. apply state_incr_intro.
apply Ple_refl. apply Ple_refl. intros; auto.
Qed.

Lemma state_incr_trans:
forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof. hammer_hook "RTLgen" "RTLgen.state_incr_trans".
intros. inv H; inv H0. apply state_incr_intro.
apply Ple_trans with (st_nextnode s2); assumption.
apply Ple_trans with (st_nextreg s2); assumption.
intros. generalize (H3 pc) (H5 pc). intuition congruence.
Qed.





Inductive res (A: Type) (s: state): Type :=
| Error: Errors.errmsg -> res A s
| OK: A -> forall (s': state), state_incr s s' -> res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret {A: Type} (x: A) : mon A :=
fun (s: state) => OK x s (state_incr_refl s).


Definition error {A: Type} (msg: Errors.errmsg) : mon A := fun (s: state) => Error msg.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
fun (s: state) =>
match f s with
| Error msg => Error msg
| OK a s' i =>
match g a s' with
| Error msg => Error msg
| OK b s'' i' => OK b s'' (state_incr_trans s s' s'' i i')
end
end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
bind f (fun xy => g (fst xy) (snd xy)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
(at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
(at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition handle_error {A: Type} (f g: mon A) : mon A :=
fun (s: state) =>
match f s with
| OK a s' i => OK a s' i
| Error _ => g s
end.





Remark init_state_wf:
forall pc, Plt pc 1%positive \/ (PTree.empty instruction)!pc = None.
Proof. hammer_hook "RTLgen" "RTLgen.init_state_wf". intros; right; apply PTree.gempty. Qed.

Definition init_state : state :=
mkstate 1%positive 1%positive (PTree.empty instruction) init_state_wf.



Remark add_instr_wf:
forall s i pc,
let n := s.(st_nextnode) in
Plt pc (Pos.succ n) \/ (PTree.set n i s.(st_code))!pc = None.
Proof. hammer_hook "RTLgen" "RTLgen.add_instr_wf".
intros. case (peq pc n); intro.
subst pc; left; apply Plt_succ.
rewrite PTree.gso; auto.
elim (st_wf s pc); intro.
left. apply Plt_trans_succ. exact H.
right; assumption.
Qed.

Remark add_instr_incr:
forall s i,
let n := s.(st_nextnode) in
state_incr s (mkstate s.(st_nextreg)
(Pos.succ n)
(PTree.set n i s.(st_code))
(add_instr_wf s i)).
Proof. hammer_hook "RTLgen" "RTLgen.add_instr_incr".
constructor; simpl.
apply Ple_succ.
apply Ple_refl.
intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto.
Qed.

Definition add_instr (i: instruction) : mon node :=
fun s =>
let n := s.(st_nextnode) in
OK n
(mkstate s.(st_nextreg) (Pos.succ n) (PTree.set n i s.(st_code))
(add_instr_wf s i))
(add_instr_incr s i).



Remark reserve_instr_wf:
forall s pc,
Plt pc (Pos.succ s.(st_nextnode)) \/ s.(st_code)!pc = None.
Proof. hammer_hook "RTLgen" "RTLgen.reserve_instr_wf".
intros. elim (st_wf s pc); intro.
left; apply Plt_trans_succ; auto.
right; auto.
Qed.

Remark reserve_instr_incr:
forall s,
let n := s.(st_nextnode) in
state_incr s (mkstate s.(st_nextreg)
(Pos.succ n)
s.(st_code)
(reserve_instr_wf s)).
Proof. hammer_hook "RTLgen" "RTLgen.reserve_instr_incr".
intros; constructor; simpl.
apply Ple_succ.
apply Ple_refl.
auto.
Qed.

Definition reserve_instr: mon node :=
fun (s: state) =>
let n := s.(st_nextnode) in
OK n
(mkstate s.(st_nextreg) (Pos.succ n) s.(st_code) (reserve_instr_wf s))
(reserve_instr_incr s).

Remark update_instr_wf:
forall s n i,
Plt n s.(st_nextnode) ->
forall pc,
Plt pc s.(st_nextnode) \/ (PTree.set n i s.(st_code))!pc = None.
Proof. hammer_hook "RTLgen" "RTLgen.update_instr_wf".
intros.
case (peq pc n); intro.
subst pc; left; assumption.
rewrite PTree.gso; auto. exact (st_wf s pc).
Qed.

Remark update_instr_incr:
forall s n i (LT: Plt n s.(st_nextnode)),
s.(st_code)!n = None ->
state_incr s
(mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set n i s.(st_code))
(update_instr_wf s n i LT)).
Proof. hammer_hook "RTLgen" "RTLgen.update_instr_incr".
intros.
constructor; simpl; intros.
apply Ple_refl.
apply Ple_refl.
rewrite PTree.gsspec. destruct (peq pc n). left; congruence. right; auto.
Qed.

Definition check_empty_node:
forall (s: state) (n: node), { s.(st_code)!n = None } + { True }.
Proof. hammer_hook "RTLgen" "RTLgen.check_empty_node".
intros. case (s.(st_code)!n); intros. right; auto. left; auto.
Defined.

Definition update_instr (n: node) (i: instruction) : mon unit :=
fun s =>
match plt n s.(st_nextnode), check_empty_node s n with
| left LT, left EMPTY =>
OK tt
(mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set n i s.(st_code))
(update_instr_wf s n i LT))
(update_instr_incr s n i LT EMPTY)
| _, _ =>
Error (Errors.msg "RTLgen.update_instr")
end.



Remark new_reg_incr:
forall s,
state_incr s (mkstate (Pos.succ s.(st_nextreg))
s.(st_nextnode) s.(st_code) s.(st_wf)).
Proof. hammer_hook "RTLgen" "RTLgen.new_reg_incr".
constructor; simpl. apply Ple_refl. apply Ple_succ. auto.
Qed.

Definition new_reg : mon reg :=
fun s =>
OK s.(st_nextreg)
(mkstate (Pos.succ s.(st_nextreg)) s.(st_nextnode) s.(st_code) s.(st_wf))
(new_reg_incr s).



Definition init_mapping : mapping :=
mkmapping (PTree.empty reg) nil.

Definition add_var (map: mapping) (name: ident) : mon (reg * mapping) :=
do r <- new_reg;
ret (r, mkmapping (PTree.set name r map.(map_vars))
map.(map_letvars)).

Fixpoint add_vars (map: mapping) (names: list ident)
{struct names} : mon (list reg * mapping) :=
match names with
| nil => ret (nil, map)
| n1 :: nl =>
do (rl, map1) <- add_vars map nl;
do (r1, map2) <- add_var map1 n1;
ret (r1 :: rl, map2)
end.

Definition find_var (map: mapping) (name: ident) : mon reg :=
match PTree.get name map.(map_vars) with
| None => error (Errors.MSG "RTLgen: unbound variable " :: Errors.CTX name :: nil)
| Some r => ret r
end.

Definition add_letvar (map: mapping) (r: reg) : mapping :=
mkmapping map.(map_vars) (r :: map.(map_letvars)).

Definition find_letvar (map: mapping) (idx: nat) : mon reg :=
match List.nth_error map.(map_letvars) idx with
| None => error (Errors.msg "RTLgen: unbound let variable")
| Some r => ret r
end.





Definition alloc_reg (map: mapping) (a: expr) : mon reg :=
match a with
| Evar id   => find_var map id
| Eletvar n => find_letvar map n
| _         => new_reg
end.



Fixpoint alloc_regs (map: mapping) (al: exprlist)
{struct al}: mon (list reg) :=
match al with
| Enil =>
ret nil
| Econs a bl =>
do r  <- alloc_reg map a;
do rl <- alloc_regs map bl;
ret (r :: rl)
end.



Definition alloc_optreg (map: mapping) (dest: option ident) : mon reg :=
match dest with
| Some id => find_var map id
| None => new_reg
end.





Definition add_move (rs rd: reg) (nd: node) : mon node :=
if Reg.eq rs rd
then ret nd
else add_instr (Iop Omove (rs::nil) rd nd).



Definition exprlist_of_expr_list (l: list expr) : exprlist :=
List.fold_right Econs Enil l.

Fixpoint convert_builtin_arg {A: Type} (a: builtin_arg expr) (rl: list A) : builtin_arg A * list A :=
match a with
| BA a =>
match rl with
| r :: rs => (BA r, rs)
| nil     => (BA_int Int.zero, nil)
end
| BA_int n => (BA_int n, rl)
| BA_long n => (BA_long n, rl)
| BA_float n => (BA_float n, rl)
| BA_single n => (BA_single n, rl)
| BA_loadstack chunk ofs => (BA_loadstack chunk ofs, rl)
| BA_addrstack ofs => (BA_addrstack ofs, rl)
| BA_loadglobal chunk id ofs => (BA_loadglobal chunk id ofs, rl)
| BA_addrglobal id ofs => (BA_addrglobal id ofs, rl)
| BA_splitlong hi lo =>
let (hi', rl1) := convert_builtin_arg hi rl in
let (lo', rl2) := convert_builtin_arg lo rl1 in
(BA_splitlong hi' lo', rl2)
| BA_addptr a1 a2 =>
let (a1', rl1) := convert_builtin_arg a1 rl in
let (a2', rl2) := convert_builtin_arg a2 rl1 in
(BA_addptr a1' a2', rl2)
end.

Fixpoint convert_builtin_args {A: Type} (al: list (builtin_arg expr)) (rl: list A) : list (builtin_arg A) :=
match al with
| nil => nil
| a1 :: al =>
let (a1', rl1) := convert_builtin_arg a1 rl in
a1' :: convert_builtin_args al rl1
end.

Definition convert_builtin_res (map: mapping) (oty: option typ) (r: builtin_res ident) : mon (builtin_res reg) :=
match r, oty with
| BR id, _ => do r <- find_var map id; ret (BR r)
| BR_none, None => ret BR_none
| BR_none, Some _ => do r <- new_reg; ret (BR r)
| _, _ => error (Errors.msg "RTLgen: bad builtin_res")
end.



Fixpoint transl_expr (map: mapping) (a: expr) (rd: reg) (nd: node)
{struct a}: mon node :=
match a with
| Evar v =>
do r <- find_var map v; add_move r rd nd
| Eop op al =>
do rl <- alloc_regs map al;
do no <- add_instr (Iop op rl rd nd);
transl_exprlist map al rl no
| Eload chunk addr al =>
do rl <- alloc_regs map al;
do no <- add_instr (Iload chunk addr rl rd nd);
transl_exprlist map al rl no
| Econdition a b c =>
do nfalse <- transl_expr map c rd nd;
do ntrue  <- transl_expr map b rd nd;
transl_condexpr map a ntrue nfalse
| Elet b c =>
do r  <- new_reg;
do nc <- transl_expr (add_letvar map r) c rd nd;
transl_expr map b r nc
| Eletvar n =>
do r <- find_letvar map n; add_move r rd nd
| Ebuiltin ef al =>
do rl <- alloc_regs map al;
do no <- add_instr (Ibuiltin ef (List.map (@BA reg) rl) (BR rd) nd);
transl_exprlist map al rl no
| Eexternal id sg al =>
do rl <- alloc_regs map al;
do no <- add_instr (Icall sg (inr id) rl rd nd);
transl_exprlist map al rl no
end



with transl_exprlist (map: mapping) (al: exprlist) (rl: list reg) (nd: node)
{struct al} : mon node :=
match al, rl with
| Enil, nil =>
ret nd
| Econs b bs, r :: rs =>
do no <- transl_exprlist map bs rs nd; transl_expr map b r no
| _, _ =>
error (Errors.msg "RTLgen.transl_exprlist")
end



with transl_condexpr (map: mapping) (a: condexpr) (ntrue nfalse: node)
{struct a} : mon node :=
match a with
| CEcond c al =>
do rl <- alloc_regs map al;
do nt <- add_instr (Icond c rl ntrue nfalse);
transl_exprlist map al rl nt
| CEcondition a b c =>
do nc <- transl_condexpr map c ntrue nfalse;
do nb <- transl_condexpr map b ntrue nfalse;
transl_condexpr map a nb nc
| CElet b c =>
do r  <- new_reg;
do nc <- transl_condexpr (add_letvar map r) c ntrue nfalse;
transl_expr map b r nc
end.



Definition transl_exit (nexits: list node) (n: nat) : mon node :=
match nth_error nexits n with
| None => error (Errors.msg "RTLgen: wrong exit")
| Some ne => ret ne
end.

Fixpoint transl_jumptable (nexits: list node) (tbl: list nat) : mon (list node) :=
match tbl with
| nil => ret nil
| t1 :: tl =>
do n1 <- transl_exit nexits t1;
do nl <- transl_jumptable nexits tl;
ret (n1 :: nl)
end.



Fixpoint transl_exitexpr (map: mapping) (a: exitexpr) (nexits: list node)
{struct a} : mon node :=
match a with
| XEexit n =>
transl_exit nexits n
| XEjumptable a tbl =>
do r <- alloc_reg map a;
do tbl' <- transl_jumptable nexits tbl;
do n1 <- add_instr (Ijumptable r tbl');
transl_expr map a r n1
| XEcondition a b c =>
do nc <- transl_exitexpr map c nexits;
do nb <- transl_exitexpr map b nexits;
transl_condexpr map a nb nc
| XElet a b =>
do r  <- new_reg;
do n1 <- transl_exitexpr (add_letvar map r) b nexits;
transl_expr map a r n1
end.



Parameter more_likely: condexpr -> stmt -> stmt -> bool.



Definition labelmap : Type := PTree.t node.

Fixpoint transl_stmt (map: mapping) (s: stmt) (nd: node)
(nexits: list node) (ngoto: labelmap) (nret: node) (rret: option reg)
{struct s} : mon node :=
match s with
| Sskip =>
ret nd
| Sassign v b =>
do r <- find_var map v;
transl_expr map b r nd
| Sstore chunk addr al b =>
do rl <- alloc_regs map al;
do r <- alloc_reg map b;
do no <- add_instr (Istore chunk addr rl r nd);
do ns <- transl_expr map b r no;
transl_exprlist map al rl ns
| Scall optid sig (inl b) cl =>
do rf <- alloc_reg map b;
do rargs <- alloc_regs map cl;
do r <- alloc_optreg map optid;
do n1 <- add_instr (Icall sig (inl _ rf) rargs r nd);
do n2 <- transl_exprlist map cl rargs n1;
transl_expr map b rf n2
| Scall optid sig (inr id) cl =>
do rargs <- alloc_regs map cl;
do r <- alloc_optreg map optid;
do n1 <- add_instr (Icall sig (inr _ id) rargs r nd);
transl_exprlist map cl rargs n1
| Stailcall sig (inl b) cl =>
do rf <- alloc_reg map b;
do rargs <- alloc_regs map cl;
do n1 <- add_instr (Itailcall sig (inl _ rf) rargs);
do n2 <- transl_exprlist map cl rargs n1;
transl_expr map b rf n2
| Stailcall sig (inr id) cl =>
do rargs <- alloc_regs map cl;
do n1 <- add_instr (Itailcall sig (inr _ id) rargs);
transl_exprlist map cl rargs n1
| Sbuiltin res ef args =>
let al := exprlist_of_expr_list (params_of_builtin_args args) in
do rargs <- alloc_regs map al;
let args' := convert_builtin_args args rargs in
do res' <- convert_builtin_res map (sig_res (ef_sig ef)) res;
do n1 <- add_instr (Ibuiltin ef args' res' nd);
transl_exprlist map al rargs n1
| Sseq s1 s2 =>
do ns <- transl_stmt map s2 nd nexits ngoto nret rret;
transl_stmt map s1 ns nexits ngoto nret rret
| Sifthenelse c strue sfalse =>
if more_likely c strue sfalse then
do nfalse <- transl_stmt map sfalse nd nexits ngoto nret rret;
do ntrue  <- transl_stmt map strue  nd nexits ngoto nret rret;
transl_condexpr map c ntrue nfalse
else
do ntrue  <- transl_stmt map strue  nd nexits ngoto nret rret;
do nfalse <- transl_stmt map sfalse nd nexits ngoto nret rret;
transl_condexpr map c ntrue nfalse
| Sloop sbody =>
do n1 <- reserve_instr;
do n2 <- transl_stmt map sbody n1 nexits ngoto nret rret;
do xx <- update_instr n1 (Inop n2);
add_instr (Inop n2)
| Sblock sbody =>
transl_stmt map sbody nd (nd :: nexits) ngoto nret rret
| Sexit n =>
transl_exit nexits n
| Sswitch a =>
transl_exitexpr map a nexits
| Sreturn opt_a =>
match opt_a, rret with
| None, _ => ret nret
| Some a, Some r => transl_expr map a r nret
| _, _ => error (Errors.msg "RTLgen: type mismatch on return")
end
| Slabel lbl s' =>
do ns <- transl_stmt map s' nd nexits ngoto nret rret;
match ngoto!lbl with
| None => error (Errors.msg "RTLgen: unbound label")
| Some n =>
do xx <-
(handle_error (update_instr n (Inop ns))
(error (Errors.MSG "Multiply-defined label " ::
Errors.CTX lbl :: nil)));
ret ns
end
| Sgoto lbl =>
match ngoto!lbl with
| None => error (Errors.MSG "Undefined defined label " ::
Errors.CTX lbl :: nil)
| Some n => ret n
end
end.



Definition alloc_label (lbl: Cminor.label) (maps: labelmap * state) : labelmap * state :=
let (map, s) := maps in
let n := s.(st_nextnode) in
(PTree.set lbl n map,
mkstate s.(st_nextreg) (Pos.succ s.(st_nextnode)) s.(st_code) (reserve_instr_wf s)).

Fixpoint reserve_labels (s: stmt) (ms: labelmap * state)
{struct s} : labelmap * state :=
match s with
| Sseq s1 s2 => reserve_labels s1 (reserve_labels s2 ms)
| Sifthenelse c s1 s2 => reserve_labels s1 (reserve_labels s2 ms)
| Sloop s1 => reserve_labels s1 ms
| Sblock s1 => reserve_labels s1 ms
| Slabel lbl s1 => alloc_label lbl (reserve_labels s1 ms)
| _ => ms
end.



Definition ret_reg (sig: signature) (rd: reg) : option reg :=
match sig.(sig_res) with
| None => None
| Some ty => Some rd
end.

Definition transl_fun (f: CminorSel.function) (ngoto: labelmap): mon (node * list reg) :=
do (rparams, map1) <- add_vars init_mapping f.(CminorSel.fn_params);
do (rvars, map2) <- add_vars map1 f.(CminorSel.fn_vars);
do rret <- new_reg;
let orret := ret_reg f.(CminorSel.fn_sig) rret in
do nret <- add_instr (Ireturn orret);
do nentry <- transl_stmt map2 f.(CminorSel.fn_body) nret nil ngoto nret orret;
ret (nentry, rparams).

Definition transl_function (f: CminorSel.function) : Errors.res RTL.function :=
let (ngoto, s0) := reserve_labels f.(fn_body) (PTree.empty node, init_state) in
match transl_fun f ngoto s0 with
| Error msg => Errors.Error msg
| OK (nentry, rparams) s i =>
Errors.OK (RTL.mkfunction
f.(CminorSel.fn_sig)
rparams
f.(CminorSel.fn_stackspace)
s.(st_code)
nentry)
end.

Definition transl_fundef := transf_partial_fundef transl_function.



Definition transl_program (p: CminorSel.program) : Errors.res RTL.program :=
transform_partial_program transl_fundef p.
