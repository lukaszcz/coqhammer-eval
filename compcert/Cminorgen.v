From Hammer Require Import Hammer.















Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Ordered.
From compcert Require Import Errors.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import AST.
From compcert Require Import Linking.
From compcert Require Import Csharpminor.
From compcert Require Import Cminor.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.







Definition compilenv := PTree.t Z.



Definition var_addr (cenv: compilenv) (id: ident): expr :=
match PTree.get id cenv with
| Some ofs => Econst (Oaddrstack (Ptrofs.repr ofs))
| None     => Econst (Oaddrsymbol id Ptrofs.zero)
end.





Definition transl_constant (cst: Csharpminor.constant): constant :=
match cst with
| Csharpminor.Ointconst n =>
Ointconst n
| Csharpminor.Ofloatconst n =>
Ofloatconst n
| Csharpminor.Osingleconst n =>
Osingleconst n
| Csharpminor.Olongconst n =>
Olongconst n
end.



Fixpoint transl_expr (cenv: compilenv) (e: Csharpminor.expr)
{struct e}: res expr :=
match e with
| Csharpminor.Evar id =>
OK (Evar id)
| Csharpminor.Eaddrof id =>
OK (var_addr cenv id)
| Csharpminor.Econst cst =>
OK (Econst (transl_constant cst))
| Csharpminor.Eunop op e1 =>
do te1  <- transl_expr cenv e1;
OK (Eunop op te1)
| Csharpminor.Ebinop op e1 e2 =>
do te1 <- transl_expr cenv e1;
do te2 <- transl_expr cenv e2;
OK (Ebinop op te1 te2)
| Csharpminor.Eload chunk e =>
do te <- transl_expr cenv e;
OK (Eload chunk te)
end.

Fixpoint transl_exprlist (cenv: compilenv) (el: list Csharpminor.expr)
{struct el}: res (list expr) :=
match el with
| nil =>
OK nil
| e1 :: e2 =>
do te1 <- transl_expr cenv e1;
do te2 <- transl_exprlist cenv e2;
OK (te1 :: te2)
end.



Definition exit_env := list bool.

Fixpoint shift_exit (e: exit_env) (n: nat) {struct e} : nat :=
match e, n with
| nil, _ => n
| false :: e', _ => S (shift_exit e' n)
| true :: e', O => O
| true :: e', S m => S (shift_exit e' m)
end.

Fixpoint switch_table (ls: lbl_stmt) (k: nat) {struct ls} : list (Z * nat) * nat :=
match ls with
| LSnil =>
(nil, k)
| LScons None _ rem =>
let (tbl, dfl) := switch_table rem (S k) in (tbl, k)
| LScons (Some ni) _ rem =>
let (tbl, dfl) := switch_table rem (S k) in ((ni, k) :: tbl, dfl)
end.

Fixpoint switch_env (ls: lbl_stmt) (e: exit_env) {struct ls}: exit_env :=
match ls with
| LSnil => e
| LScons _ _ ls' => false :: switch_env ls' e
end.



Fixpoint transl_stmt (cenv: compilenv) (xenv: exit_env) (s: Csharpminor.stmt)
{struct s}: res stmt :=
match s with
| Csharpminor.Sskip =>
OK Sskip
| Csharpminor.Sset id e =>
do te <- transl_expr cenv e;
OK (Sassign id te)
| Csharpminor.Sstore chunk e1 e2 =>
do te1 <- transl_expr cenv e1;
do te2 <- transl_expr cenv e2;
OK (Sstore chunk te1 te2)
| Csharpminor.Scall optid sig e el =>
do te <- transl_expr cenv e;
do tel <- transl_exprlist cenv el;
OK (Scall optid sig te tel)
| Csharpminor.Sbuiltin optid ef el =>
do tel <- transl_exprlist cenv el;
OK (Sbuiltin optid ef tel)
| Csharpminor.Sseq s1 s2 =>
do ts1 <- transl_stmt cenv xenv s1;
do ts2 <- transl_stmt cenv xenv s2;
OK (Sseq ts1 ts2)
| Csharpminor.Sifthenelse e s1 s2 =>
do te <- transl_expr cenv e;
do ts1 <- transl_stmt cenv xenv s1;
do ts2 <- transl_stmt cenv xenv s2;
OK (Sifthenelse te ts1 ts2)
| Csharpminor.Sloop s =>
do ts <- transl_stmt cenv xenv s;
OK (Sloop ts)
| Csharpminor.Sblock s =>
do ts <- transl_stmt cenv (true :: xenv) s;
OK (Sblock ts)
| Csharpminor.Sexit n =>
OK (Sexit (shift_exit xenv n))
| Csharpminor.Sswitch long e ls =>
let (tbl, dfl) := switch_table ls O in
do te <- transl_expr cenv e;
transl_lblstmt cenv (switch_env ls xenv) ls (Sswitch long te tbl dfl)
| Csharpminor.Sreturn None =>
OK (Sreturn None)
| Csharpminor.Sreturn (Some e) =>
do te <- transl_expr cenv e;
OK (Sreturn (Some te))
| Csharpminor.Slabel lbl s =>
do ts <- transl_stmt cenv xenv s; OK (Slabel lbl ts)
| Csharpminor.Sgoto lbl =>
OK (Sgoto lbl)
end

with transl_lblstmt (cenv: compilenv) (xenv: exit_env) (ls: Csharpminor.lbl_stmt) (body: stmt)
{struct ls}: res stmt :=
match ls with
| Csharpminor.LSnil =>
OK (Sseq (Sblock body) Sskip)
| Csharpminor.LScons _ s ls' =>
do ts <- transl_stmt cenv xenv s;
transl_lblstmt cenv (List.tail xenv) ls' (Sseq (Sblock body) ts)
end.





Definition block_alignment (sz: Z) : Z :=
if zlt sz 2 then 1
else if zlt sz 4 then 2
else if zlt sz 8 then 4 else 8.

Definition assign_variable
(cenv_stacksize: compilenv * Z) (id_sz: ident * Z) : compilenv * Z :=
let (id, sz) := id_sz in
let (cenv, stacksize) := cenv_stacksize in
let ofs := align stacksize (block_alignment sz) in
(PTree.set id ofs cenv, ofs + Z.max 0 sz).

Definition assign_variables (cenv_stacksize: compilenv * Z) (vars: list (ident * Z)) : compilenv * Z :=
List.fold_left assign_variable vars cenv_stacksize.



Module VarOrder <: TotalLeBool.
Definition t := (ident * Z)%type.
Definition leb (v1 v2: t) : bool := zle (snd v1) (snd v2).
Theorem leb_total: forall v1 v2, leb v1 v2 = true \/ leb v2 v1 = true.
Proof. hammer_hook "Cminorgen" "Cminorgen.VarOrder.leb_total".
unfold leb; intros.
assert (snd v1 <= snd v2 \/ snd v2 <= snd v1) by omega.
unfold proj_sumbool. destruct H; [left|right]; apply zle_true; auto.
Qed.
End VarOrder.

Module VarSort := Mergesort.Sort(VarOrder).

Definition build_compilenv (f: Csharpminor.function) : compilenv * Z :=
assign_variables (PTree.empty Z, 0) (VarSort.sort (Csharpminor.fn_vars f)).





Definition transl_funbody
(cenv: compilenv) (stacksize: Z) (f: Csharpminor.function): res function :=
do tbody <- transl_stmt cenv nil f.(Csharpminor.fn_body);
OK (mkfunction
(Csharpminor.fn_sig f)
(Csharpminor.fn_params f)
(Csharpminor.fn_temps f)
stacksize
tbody).

Definition transl_function (f: Csharpminor.function): res function :=
let (cenv, stacksize) := build_compilenv f in
if zle stacksize Ptrofs.max_unsigned
then transl_funbody cenv stacksize f
else Error(msg "Cminorgen: too many local variables, stack size exceeded").

Definition transl_fundef (f: Csharpminor.fundef): res fundef :=
transf_partial_fundef transl_function f.

Definition transl_program (p: Csharpminor.program) : res program :=
transform_partial_program transl_fundef p.
