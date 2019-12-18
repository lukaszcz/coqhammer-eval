From Hammer Require Import Hammer.















Require Import FSets.
From compcert Require Import FSetAVLplus.
From compcert Require Import Coqlib.
From compcert Require Import Ordered.
From compcert Require Import Maps.
From compcert Require Import Errors.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import AST.
From compcert Require Import Lattice.
From compcert Require Import Kildall.
From compcert Require Import Memdata.
From compcert Require Archi.
From compcert Require Import Op.
From compcert Require Import Registers.
From compcert Require Import RTL.
From compcert Require Import Locations.
From compcert Require Import Conventions.
From compcert Require Import RTLtyping.
From compcert Require Import LTL.







Inductive move: Type :=
| MV (src dst: loc)
| MVmakelong (src1 src2 dst: mreg)
| MVlowlong (src dst: mreg)
| MVhighlong (src dst: mreg).

Definition moves := list move.

Inductive block_shape: Type :=
| BSnop (mv: moves) (s: node)
| BSmove (src: reg) (dst: reg) (mv: moves) (s: node)
| BSmakelong (src1 src2: reg) (dst: reg) (mv: moves) (s: node)
| BSlowlong (src: reg) (dst: reg) (mv: moves) (s: node)
| BShighlong (src: reg) (dst: reg) (mv: moves) (s: node)
| BSop (op: operation) (args: list reg) (res: reg)
(mv1: moves) (args': list mreg) (res': mreg)
(mv2: moves) (s: node)
| BSopdead (op: operation) (args: list reg) (res: reg)
(mv: moves) (s: node)
| BSload (chunk: memory_chunk) (addr: addressing) (args: list reg) (dst: reg)
(mv1: moves) (args': list mreg) (dst': mreg)
(mv2: moves) (s: node)
| BSloaddead (chunk: memory_chunk) (addr: addressing) (args: list reg) (dst: reg)
(mv: moves) (s: node)
| BSload2 (addr1 addr2: addressing) (args: list reg) (dst: reg)
(mv1: moves) (args1': list mreg) (dst1': mreg)
(mv2: moves) (args2': list mreg) (dst2': mreg)
(mv3: moves) (s: node)
| BSload2_1 (addr: addressing) (args: list reg) (dst: reg)
(mv1: moves) (args': list mreg) (dst': mreg)
(mv2: moves) (s: node)
| BSload2_2 (addr addr': addressing) (args: list reg) (dst: reg)
(mv1: moves) (args': list mreg) (dst': mreg)
(mv2: moves) (s: node)
| BSstore (chunk: memory_chunk) (addr: addressing) (args: list reg) (src: reg)
(mv1: moves) (args': list mreg) (src': mreg)
(s: node)
| BSstore2 (addr1 addr2: addressing) (args: list reg) (src: reg)
(mv1: moves) (args1': list mreg) (src1': mreg)
(mv2: moves) (args2': list mreg) (src2': mreg)
(s: node)
| BScall (sg: signature) (ros: reg + ident) (args: list reg) (res: reg)
(mv1: moves) (ros': mreg + ident) (mv2: moves) (s: node)
| BStailcall (sg: signature) (ros: reg + ident) (args: list reg)
(mv1: moves) (ros': mreg + ident)
| BSbuiltin (ef: external_function)
(args: list (builtin_arg reg)) (res: builtin_res reg)
(mv1: moves) (args': list (builtin_arg loc)) (res': builtin_res mreg)
(mv2: moves) (s: node)
| BScond (cond: condition) (args: list reg)
(mv: moves) (args': list mreg) (s1 s2: node)
| BSjumptable (arg: reg)
(mv: moves) (arg': mreg) (tbl: list node)
| BSreturn (arg: option reg)
(mv: moves).



Inductive operation_kind {A: Type}: operation -> list A -> Type :=
| operation_Omove: forall arg, operation_kind Omove (arg :: nil)
| operation_Omakelong: forall arg1 arg2, operation_kind Omakelong (arg1 :: arg2 :: nil)
| operation_Olowlong: forall arg, operation_kind Olowlong (arg :: nil)
| operation_Ohighlong: forall arg, operation_kind Ohighlong (arg :: nil)
| operation_other: forall op args, operation_kind op args.

Definition classify_operation {A: Type} (op: operation) (args: list A) : operation_kind op args :=
match op, args with
| Omove, arg::nil => operation_Omove arg
| Omakelong, arg1::arg2::nil => operation_Omakelong arg1 arg2
| Olowlong, arg::nil => operation_Olowlong arg
| Ohighlong, arg::nil => operation_Ohighlong arg
| op, args => operation_other op args
end.



Fixpoint extract_moves (accu: moves) (b: bblock) {struct b} : moves * bblock :=
match b with
| Lgetstack sl ofs ty dst :: b' =>
extract_moves (MV (S sl ofs ty) (R dst) :: accu) b'
| Lsetstack src sl ofs ty :: b' =>
extract_moves (MV (R src) (S sl ofs ty) :: accu) b'
| Lop op args res :: b' =>
match is_move_operation op args with
| Some arg =>
extract_moves (MV (R arg) (R res) :: accu) b'
| None =>
(List.rev accu, b)
end
| _ =>
(List.rev accu, b)
end.

Fixpoint extract_moves_ext (accu: moves) (b: bblock) {struct b} : moves * bblock :=
match b with
| Lgetstack sl ofs ty dst :: b' =>
extract_moves_ext (MV (S sl ofs ty) (R dst) :: accu) b'
| Lsetstack src sl ofs ty :: b' =>
extract_moves_ext (MV (R src) (S sl ofs ty) :: accu) b'
| Lop op args res :: b' =>
match classify_operation op args with
| operation_Omove arg =>
extract_moves_ext (MV (R arg) (R res) :: accu) b'
| operation_Omakelong arg1 arg2 =>
extract_moves_ext (MVmakelong arg1 arg2 res :: accu) b'
| operation_Olowlong arg =>
extract_moves_ext (MVlowlong arg res :: accu) b'
| operation_Ohighlong arg =>
extract_moves_ext (MVhighlong arg res :: accu) b'
| operation_other _ _ =>
(List.rev accu, b)
end
| _ =>
(List.rev accu, b)
end.

Definition check_succ (s: node) (b: LTL.bblock) : bool :=
match b with
| Lbranch s' :: _ => peq s s'
| _ => false
end.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
(at level 200, X ident, A at level 100, B at level 200)
: option_monad_scope.

Notation "'assertion' A ; B" := (if A then B else None)
(at level 200, A at level 100, B at level 200)
: option_monad_scope.

Local Open Scope option_monad_scope.



Definition pair_Iop_block (op: operation) (args: list reg) (res: reg) (s: node) (b: LTL.bblock) :=
let (mv1, b1) := extract_moves nil b in
match b1 with
| Lop op' args' res' :: b2 =>
let (mv2, b3) := extract_moves nil b2 in
assertion (eq_operation op op');
assertion (check_succ s b3);
Some(BSop op args res mv1 args' res' mv2 s)
| _ =>
assertion (check_succ s b1);
Some(BSopdead op args res mv1 s)
end.

Definition pair_instr_block
(i: RTL.instruction) (b: LTL.bblock) : option block_shape :=
match i with
| Inop s =>
let (mv, b1) := extract_moves nil b in
assertion (check_succ s b1); Some(BSnop mv s)
| Iop op args res s =>
match classify_operation op args with
| operation_Omove arg =>
let (mv, b1) := extract_moves nil b in
assertion (check_succ s b1); Some(BSmove arg res mv s)
| operation_Omakelong arg1 arg2 =>
if Archi.splitlong then
(let (mv, b1) := extract_moves nil b in
assertion (check_succ s b1); Some(BSmakelong arg1 arg2 res mv s))
else
pair_Iop_block op args res s b
| operation_Olowlong arg =>
if Archi.splitlong then
(let (mv, b1) := extract_moves nil b in
assertion (check_succ s b1); Some(BSlowlong arg res mv s))
else
pair_Iop_block op args res s b
| operation_Ohighlong arg =>
if Archi.splitlong then
(let (mv, b1) := extract_moves nil b in
assertion (check_succ s b1); Some(BShighlong arg res mv s))
else
pair_Iop_block op args res s b
| operation_other _ _ =>
pair_Iop_block op args res s b
end
| Iload chunk addr args dst s =>
let (mv1, b1) := extract_moves nil b in
match b1 with
| Lload chunk' addr' args' dst' :: b2 =>
if chunk_eq chunk Mint64 && Archi.splitlong then
assertion (chunk_eq chunk' Mint32);
let (mv2, b3) := extract_moves nil b2 in
match b3 with
| Lload chunk'' addr'' args'' dst'' :: b4 =>
let (mv3, b5) := extract_moves nil b4 in
assertion (chunk_eq chunk'' Mint32);
assertion (eq_addressing addr addr');
assertion (option_eq eq_addressing (offset_addressing addr 4) (Some addr''));
assertion (check_succ s b5);
Some(BSload2 addr addr'' args dst mv1 args' dst' mv2 args'' dst'' mv3 s)
| _ =>
assertion (check_succ s b3);
if (eq_addressing addr addr') then
Some(BSload2_1 addr args dst mv1 args' dst' mv2 s)
else
(assertion (option_eq eq_addressing (offset_addressing addr 4) (Some addr'));
Some(BSload2_2 addr addr' args dst mv1 args' dst' mv2 s))
end
else (
let (mv2, b3) := extract_moves nil b2 in
assertion (chunk_eq chunk chunk');
assertion (eq_addressing addr addr');
assertion (check_succ s b3);
Some(BSload chunk addr args dst mv1 args' dst' mv2 s))
| _ =>
assertion (check_succ s b1);
Some(BSloaddead chunk addr args dst mv1 s)
end
| Istore chunk addr args src s =>
let (mv1, b1) := extract_moves nil b in
match b1 with
| Lstore chunk' addr' args' src' :: b2 =>
if chunk_eq chunk Mint64 && Archi.splitlong then
let (mv2, b3) := extract_moves nil b2 in
match b3 with
| Lstore chunk'' addr'' args'' src'' :: b4 =>
assertion (chunk_eq chunk' Mint32);
assertion (chunk_eq chunk'' Mint32);
assertion (eq_addressing addr addr');
assertion (option_eq eq_addressing (offset_addressing addr 4) (Some addr''));
assertion (check_succ s b4);
Some(BSstore2 addr addr'' args src mv1 args' src' mv2 args'' src'' s)
| _ => None
end
else (
assertion (chunk_eq chunk chunk');
assertion (eq_addressing addr addr');
assertion (check_succ s b2);
Some(BSstore chunk addr args src mv1 args' src' s))
| _ => None
end
| Icall sg ros args res s =>
let (mv1, b1) := extract_moves_ext nil b in
match b1 with
| Lcall sg' ros' :: b2 =>
let (mv2, b3) := extract_moves_ext nil b2 in
assertion (signature_eq sg sg');
assertion (check_succ s b3);
Some(BScall sg ros args res mv1 ros' mv2 s)
| _ => None
end
| Itailcall sg ros args =>
let (mv1, b1) := extract_moves_ext nil b in
match b1 with
| Ltailcall sg' ros' :: b2 =>
assertion (signature_eq sg sg');
Some(BStailcall sg ros args mv1 ros')
| _ => None
end
| Ibuiltin ef args res s =>
let (mv1, b1) := extract_moves nil b in
match b1 with
| Lbuiltin ef' args' res' :: b2 =>
let (mv2, b3) := extract_moves nil b2 in
assertion (external_function_eq ef ef');
assertion (check_succ s b3);
Some(BSbuiltin ef args res mv1 args' res' mv2 s)
| _ => None
end
| Icond cond args s1 s2 =>
let (mv1, b1) := extract_moves nil b in
match b1 with
| Lcond cond' args' s1' s2' :: b2 =>
assertion (eq_condition cond cond');
assertion (peq s1 s1');
assertion (peq s2 s2');
Some(BScond cond args mv1 args' s1 s2)
| _ => None
end
| Ijumptable arg tbl =>
let (mv1, b1) := extract_moves nil b in
match b1 with
| Ljumptable arg' tbl' :: b2 =>
assertion (list_eq_dec peq tbl tbl');
Some(BSjumptable arg mv1 arg' tbl)
| _ => None
end
| Ireturn arg =>
let (mv1, b1) := extract_moves_ext nil b in
match b1 with
| Lreturn :: b2 => Some(BSreturn arg mv1)
| _ => None
end
end.



Definition pair_codes (f1: RTL.function) (f2: LTL.function) : PTree.t block_shape :=
PTree.combine
(fun opti optb => do i <- opti; do b <- optb; pair_instr_block i b)
(RTL.fn_code f1) (LTL.fn_code f2).



Definition pair_entrypoints (f1: RTL.function) (f2: LTL.function) : option moves :=
do b <- (LTL.fn_code f2)!(LTL.fn_entrypoint f2);
let (mv, b1) := extract_moves_ext nil b in
assertion (check_succ (RTL.fn_entrypoint f1) b1);
Some mv.





Inductive equation_kind : Type := Full | Low | High.

Record equation := Eq {
ekind: equation_kind;
ereg: reg;
eloc: loc
}.



Module IndexedEqKind <: INDEXED_TYPE.
Definition t := equation_kind.
Definition index (x: t) :=
match x with Full => 1%positive | Low => 2%positive | High => 3%positive end.
Lemma index_inj: forall x y, index x = index y -> x = y.
Proof. hammer_hook "Allocation" "Allocation.IndexedEqKind.index_inj". destruct x; destruct y; simpl; congruence. Qed.
Definition eq (x y: t) : {x=y} + {x<>y}.
Proof. hammer_hook "Allocation" "Allocation.IndexedEqKind.eq". decide equality. Defined.
End IndexedEqKind.

Module OrderedEqKind := OrderedIndexed(IndexedEqKind).



Module OrderedEquation <: OrderedType.
Definition t := equation.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) :=
Plt (ereg x) (ereg y) \/ (ereg x = ereg y /\
(OrderedLoc.lt (eloc x) (eloc y) \/ (eloc x = eloc y /\
OrderedEqKind.lt (ekind x) (ekind y)))).
Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation.eq_refl". exact ((@eq_refl t)). Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation.eq_sym". exact ((@eq_sym t)). Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation.eq_trans". exact ((@eq_trans t)). Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation.lt_trans".
unfold lt; intros.
destruct H.
destruct H0. left; eapply Plt_trans; eauto.
destruct H0. rewrite <- H0. auto.
destruct H. rewrite H.
destruct H0. auto.
destruct H0. right; split; auto.
intuition.
left; eapply OrderedLoc.lt_trans; eauto.
left; congruence.
left; congruence.
right; split. congruence. eapply OrderedEqKind.lt_trans; eauto.
Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation.lt_not_eq".
unfold lt, eq; intros; red; intros. subst y. intuition.
eelim Plt_strict; eauto.
eelim OrderedLoc.lt_not_eq; eauto. red; auto.
eelim OrderedEqKind.lt_not_eq; eauto. red; auto.
Qed.
Definition compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation.compare".
intros.
destruct (OrderedPositive.compare (ereg x) (ereg y)).
- apply LT. red; auto.
- destruct (OrderedLoc.compare (eloc x) (eloc y)).
+ apply LT. red; auto.
+ destruct (OrderedEqKind.compare (ekind x) (ekind y)).
* apply LT. red; auto.
* apply EQ. red in e; red in e0; red in e1; red.
destruct x; destruct y; simpl in *; congruence.
* apply GT. red; auto.
+ apply GT. red; auto.
- apply GT. red; auto.
Defined.
Definition eq_dec (x y: t) : {x = y} + {x <> y}.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation.eq_dec".
intros. decide equality.
apply Loc.eq.
apply peq.
apply IndexedEqKind.eq.
Defined.
End OrderedEquation.



Module OrderedEquation' <: OrderedType.
Definition t := equation.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) :=
OrderedLoc.lt (eloc x) (eloc y) \/ (eloc x = eloc y /\
(Plt (ereg x) (ereg y) \/ (ereg x = ereg y /\
OrderedEqKind.lt (ekind x) (ekind y)))).
Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation'.eq_refl". exact ((@eq_refl t)). Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation'.eq_sym". exact ((@eq_sym t)). Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation'.eq_trans". exact ((@eq_trans t)). Qed.
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation'.lt_trans".
unfold lt; intros.
destruct H.
destruct H0. left; eapply OrderedLoc.lt_trans; eauto.
destruct H0. rewrite <- H0. auto.
destruct H. rewrite H.
destruct H0. auto.
destruct H0. right; split; auto.
intuition.
left; eapply Plt_trans; eauto.
left; congruence.
left; congruence.
right; split. congruence. eapply OrderedEqKind.lt_trans; eauto.
Qed.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation'.lt_not_eq".
unfold lt, eq; intros; red; intros. subst y. intuition.
eelim OrderedLoc.lt_not_eq; eauto. red; auto.
eelim Plt_strict; eauto.
eelim OrderedEqKind.lt_not_eq; eauto. red; auto.
Qed.
Definition compare : forall x y : t, Compare lt eq x y.
Proof. hammer_hook "Allocation" "Allocation.OrderedEquation'.compare".
intros.
destruct (OrderedLoc.compare (eloc x) (eloc y)).
- apply LT. red; auto.
- destruct (OrderedPositive.compare (ereg x) (ereg y)).
+ apply LT. red; auto.
+ destruct (OrderedEqKind.compare (ekind x) (ekind y)).
* apply LT. red; auto.
* apply EQ. red in e; red in e0; red in e1; red.
destruct x; destruct y; simpl in *; congruence.
* apply GT. red; auto.
+ apply GT. red; auto.
- apply GT. red; auto.
Defined.
Definition eq_dec: forall (x y: t), {x = y} + {x <> y} := OrderedEquation.eq_dec.
End OrderedEquation'.

Module EqSet := FSetAVLplus.Make(OrderedEquation).
Module EqSet2 := FSetAVLplus.Make(OrderedEquation').



Record eqs := mkeqs {
eqs1 :> EqSet.t;
eqs2 : EqSet2.t;
eqs_same: forall q, EqSet2.In q eqs2 <-> EqSet.In q eqs1
}.





Program Definition empty_eqs := mkeqs EqSet.empty EqSet2.empty _.
Next Obligation.
split; intros. eelim EqSet2.empty_1; eauto. eelim EqSet.empty_1; eauto.
Qed.



Program Definition add_equation (q: equation) (e: eqs) :=
mkeqs (EqSet.add q (eqs1 e)) (EqSet2.add q (eqs2 e)) _.
Next Obligation.
split; intros.
destruct (OrderedEquation'.eq_dec q q0).
apply EqSet.add_1; auto.
apply EqSet.add_2. apply (eqs_same e). apply EqSet2.add_3 with q; auto.
destruct (OrderedEquation.eq_dec q q0).
apply EqSet2.add_1; auto.
apply EqSet2.add_2. apply (eqs_same e). apply EqSet.add_3 with q; auto.
Qed.

Program Definition remove_equation (q: equation) (e: eqs) :=
mkeqs (EqSet.remove q (eqs1 e)) (EqSet2.remove q (eqs2 e)) _.
Next Obligation.
split; intros.
destruct (OrderedEquation'.eq_dec q q0).
eelim EqSet2.remove_1; eauto.
apply EqSet.remove_2; auto. apply (eqs_same e). apply EqSet2.remove_3 with q; auto.
destruct (OrderedEquation.eq_dec q q0).
eelim EqSet.remove_1; eauto.
apply EqSet2.remove_2; auto. apply (eqs_same e). apply EqSet.remove_3 with q; auto.
Qed.



Definition select_reg_l (r: reg) (q: equation) := Pos.leb r (ereg q).
Definition select_reg_h (r: reg) (q: equation) := Pos.leb (ereg q) r.

Definition reg_unconstrained (r: reg) (e: eqs) : bool :=
negb (EqSet.mem_between (select_reg_l r) (select_reg_h r) (eqs1 e)).



Definition select_loc_l (l: loc) :=
let lb := OrderedLoc.diff_low_bound l in
fun (q: equation) => match OrderedLoc.compare (eloc q) lb with LT _ => false | _ => true end.
Definition select_loc_h (l: loc) :=
let lh := OrderedLoc.diff_high_bound l in
fun (q: equation) => match OrderedLoc.compare (eloc q) lh with GT _ => false | _ => true end.

Definition loc_unconstrained (l: loc) (e: eqs) : bool :=
negb (EqSet2.mem_between (select_loc_l l) (select_loc_h l) (eqs2 e)).

Definition reg_loc_unconstrained (r: reg) (l: loc) (e: eqs) : bool :=
reg_unconstrained r e && loc_unconstrained l e.



Definition subst_reg (r1 r2: reg) (e: eqs) : eqs :=
EqSet.fold
(fun q e => add_equation (Eq (ekind q) r2 (eloc q)) (remove_equation q e))
(EqSet.elements_between (select_reg_l r1) (select_reg_h r1) (eqs1 e))
e.



Definition subst_reg_kind (r1: reg) (k1: equation_kind) (r2: reg) (k2: equation_kind) (e: eqs) : eqs :=
EqSet.fold
(fun q e =>
if IndexedEqKind.eq (ekind q) k1
then add_equation (Eq k2 r2 (eloc q)) (remove_equation q e)
else e)
(EqSet.elements_between (select_reg_l r1) (select_reg_h r1) (eqs1 e))
e.



Definition subst_loc (l1 l2: loc) (e: eqs) : option eqs :=
EqSet2.fold
(fun q opte =>
match opte with
| None => None
| Some e =>
if Loc.eq l1 (eloc q) then
Some (add_equation (Eq (ekind q) (ereg q) l2) (remove_equation q e))
else
None
end)
(EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e))
(Some e).



Definition subst_loc_part (l1: loc) (l2: loc) (k: equation_kind) (e: eqs) : option eqs :=
EqSet2.fold
(fun q opte =>
match opte with
| None => None
| Some e =>
if Loc.eq l1 (eloc q) then
if IndexedEqKind.eq (ekind q) k
then Some (add_equation (Eq Full (ereg q) l2) (remove_equation q e))
else None
else
None
end)
(EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e))
(Some e).



Definition subst_loc_pair (l1 l2 l2': loc) (e: eqs) : option eqs :=
EqSet2.fold
(fun q opte =>
match opte with
| None => None
| Some e =>
if Loc.eq l1 (eloc q) then
if IndexedEqKind.eq (ekind q) Full
then Some (add_equation (Eq High (ereg q) l2)
(add_equation (Eq Low (ereg q) l2')
(remove_equation q e)))
else None
else
None
end)
(EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e))
(Some e).



Definition sel_type (k: equation_kind) (ty: typ) : typ :=
match k with
| Full => ty
| Low | High => Tint
end.

Definition loc_type_compat (env: regenv) (l: loc) (e: eqs) : bool :=
EqSet2.for_all_between
(fun q => subtype (sel_type (ekind q) (env (ereg q))) (Loc.type l))
(select_loc_l l) (select_loc_h l) (eqs2 e).



Definition long_type_compat (env: regenv) (l: loc) (e: eqs) : bool :=
EqSet2.for_all_between
(fun q => subtype (env (ereg q)) Tlong)
(select_loc_l l) (select_loc_h l) (eqs2 e).



Fixpoint add_equations (rl: list reg) (ml: list mreg) (e: eqs) : option eqs :=
match rl, ml with
| nil, nil => Some e
| r1 :: rl, m1 :: ml => add_equations rl ml (add_equation (Eq Full r1 (R m1)) e)
| _, _ => None
end.



Function add_equations_args (rl: list reg) (tyl: list typ) (ll: list (rpair loc)) (e: eqs) : option eqs :=
match rl, tyl, ll with
| nil, nil, nil => Some e
| r1 :: rl, ty :: tyl, One l1 :: ll =>
add_equations_args rl tyl ll (add_equation (Eq Full r1 l1) e)
| r1 :: rl, Tlong :: tyl, Twolong l1 l2 :: ll =>
if Archi.ptr64 then None else
add_equations_args rl tyl ll (add_equation (Eq Low r1 l2) (add_equation (Eq High r1 l1) e))
| _, _, _ => None
end.



Function add_equations_res (r: reg) (oty: option typ) (p: rpair mreg) (e: eqs) : option eqs :=
match p, oty with
| One mr, _ =>
Some (add_equation (Eq Full r (R mr)) e)
| Twolong mr1 mr2, Some Tlong =>
if Archi.ptr64 then None else
Some (add_equation (Eq Low r (R mr2)) (add_equation (Eq High r (R mr1)) e))
| _, _ =>
None
end.



Function remove_equations_res (r: reg) (p: rpair mreg) (e: eqs) : option eqs :=
match p with
| One mr =>
Some (remove_equation (Eq Full r (R mr)) e)
| Twolong mr1 mr2 =>
if mreg_eq mr2 mr1
then None
else Some (remove_equation (Eq Low r (R mr2)) (remove_equation (Eq High r (R mr1)) e))
end.



Definition add_equation_ros (ros: reg + ident) (ros': mreg + ident) (e: eqs) : option eqs :=
match ros, ros' with
| inl r, inl mr => Some(add_equation (Eq Full r (R mr)) e)
| inr id, inr id' => assertion (ident_eq id id'); Some e
| _, _ => None
end.



Fixpoint add_equations_builtin_arg
(env: regenv) (arg: builtin_arg reg) (arg': builtin_arg loc) (e: eqs) : option eqs :=
match arg, arg' with
| BA r, BA l =>
Some (add_equation (Eq Full r l) e)
| BA r, BA_splitlong (BA lhi) (BA llo) =>
assertion (typ_eq (env r) Tlong);
assertion (Archi.splitlong);
Some (add_equation (Eq Low r llo) (add_equation (Eq High r lhi) e))
| BA_int n, BA_int n' =>
assertion (Int.eq_dec n n'); Some e
| BA_long n, BA_long n' =>
assertion (Int64.eq_dec n n'); Some e
| BA_float f, BA_float f' =>
assertion (Float.eq_dec f f'); Some e
| BA_single f, BA_single f' =>
assertion (Float32.eq_dec f f'); Some e
| BA_loadstack chunk ofs, BA_loadstack chunk' ofs' =>
assertion (chunk_eq chunk chunk');
assertion (Ptrofs.eq_dec ofs ofs');
Some e
| BA_addrstack ofs, BA_addrstack ofs' =>
assertion (Ptrofs.eq_dec ofs ofs');
Some e
| BA_loadglobal chunk id ofs, BA_loadglobal chunk' id' ofs' =>
assertion (chunk_eq chunk chunk');
assertion (ident_eq id id');
assertion (Ptrofs.eq_dec ofs ofs');
Some e
| BA_addrglobal id ofs, BA_addrglobal id' ofs' =>
assertion (ident_eq id id');
assertion (Ptrofs.eq_dec ofs ofs');
Some e
| BA_splitlong hi lo, BA_splitlong hi' lo' =>
do e1 <- add_equations_builtin_arg env hi hi' e;
add_equations_builtin_arg env lo lo' e1
| BA_addptr a1 a2, BA_addptr a1' a2' =>
do e1 <- add_equations_builtin_arg env a1 a1' e;
add_equations_builtin_arg env a2 a2' e1
| _, _ =>
None
end.

Fixpoint add_equations_builtin_args
(env: regenv) (args: list (builtin_arg reg))
(args': list (builtin_arg loc)) (e: eqs) : option eqs :=
match args, args' with
| nil, nil => Some e
| a1 :: al, a1' :: al' =>
do e1 <- add_equations_builtin_arg env a1 a1' e;
add_equations_builtin_args env al al' e1
| _, _ => None
end.



Fixpoint add_equations_debug_args
(env: regenv) (args: list (builtin_arg reg))
(args': list (builtin_arg loc)) (e: eqs) : option eqs :=
match args, args' with
| _, nil => Some e
| a1 :: al, a1' :: al' =>
match add_equations_builtin_arg env a1 a1' e with
| None => add_equations_debug_args env al args' e
| Some e1 => add_equations_debug_args env al al' e1
end
| _, _ => None
end.



Definition remove_equations_builtin_res
(env: regenv) (res: builtin_res reg) (res': builtin_res mreg) (e: eqs) : option eqs :=
match res, res' with
| BR r, BR r' => Some (remove_equation (Eq Full r (R r')) e)
| BR r, BR_splitlong (BR rhi) (BR rlo) =>
assertion (typ_eq (env r) Tlong);
if mreg_eq rhi rlo then None else
Some (remove_equation (Eq Low r (R rlo))
(remove_equation (Eq High r (R rhi)) e))
| BR_none, BR_none => Some e
| _, _ => None
end.



Fixpoint can_undef (ml: list mreg) (e: eqs) : bool :=
match ml with
| nil => true
| m1 :: ml => loc_unconstrained (R m1) e && can_undef ml e
end.

Fixpoint can_undef_except (l: loc) (ml: list mreg) (e: eqs) : bool :=
match ml with
| nil => true
| m1 :: ml =>
(Loc.eq l (R m1) || loc_unconstrained (R m1) e) && can_undef_except l ml e
end.



Definition no_caller_saves (e: eqs) : bool :=
EqSet.for_all
(fun eq =>
match eloc eq with
| R r => is_callee_save r
| S Outgoing _ _ => false
| S _ _ _ => true
end)
e.



Definition compat_left (r: reg) (l: loc) (e: eqs) : bool :=
EqSet.for_all_between
(fun q =>
match ekind q with
| Full => Loc.eq l (eloc q)
| _ => false
end)
(select_reg_l r) (select_reg_h r)
(eqs1 e).



Definition compat_left2 (r: reg) (l1 l2: loc) (e: eqs) : bool :=
EqSet.for_all_between
(fun q =>
match ekind q with
| High => Loc.eq l1 (eloc q)
| Low => Loc.eq l2 (eloc q)
| _ => false
end)
(select_reg_l r) (select_reg_h r)
(eqs1 e).



Definition ros_compatible_tailcall (ros: mreg + ident) : bool :=
match ros with
| inl r => negb (is_callee_save r)
| inr id => true
end.



Definition destroyed_by_move (src dst: loc) :=
match src, dst with
| S sl ofs ty, _ => destroyed_by_getstack sl
| _, S sl ofs ty => destroyed_by_setstack ty
| _, _ => destroyed_by_op Omove
end.

Definition well_typed_move (env: regenv) (dst: loc) (e: eqs) : bool :=
match dst with
| R r => true
| S sl ofs ty => loc_type_compat env dst e
end.



Fixpoint track_moves (env: regenv) (mv: moves) (e: eqs) : option eqs :=
match mv with
| nil => Some e
| MV src dst :: mv =>
do e1 <- track_moves env mv e;
assertion (can_undef_except dst (destroyed_by_move src dst)) e1;
assertion (well_typed_move env dst e1);
subst_loc dst src e1
| MVmakelong src1 src2 dst :: mv =>
assertion (negb Archi.ptr64);
do e1 <- track_moves env mv e;
assertion (long_type_compat env (R dst) e1);
subst_loc_pair (R dst) (R src1) (R src2) e1
| MVlowlong src dst :: mv =>
assertion (negb Archi.ptr64);
do e1 <- track_moves env mv e;
subst_loc_part (R dst) (R src) Low e1
| MVhighlong src dst :: mv =>
assertion (negb Archi.ptr64);
do e1 <- track_moves env mv e;
subst_loc_part (R dst) (R src) High e1
end.



Definition transfer_use_def (args: list reg) (res: reg) (args': list mreg) (res': mreg)
(undefs: list mreg) (e: eqs) : option eqs :=
let e1 := remove_equation (Eq Full res (R res')) e in
assertion (reg_loc_unconstrained res (R res') e1);
assertion (can_undef undefs e1);
add_equations args args' e1.

Definition kind_first_word := if Archi.big_endian then High else Low.
Definition kind_second_word := if Archi.big_endian then Low else High.



Definition transfer_aux (f: RTL.function) (env: regenv)
(shape: block_shape) (e: eqs) : option eqs :=
match shape with
| BSnop mv s =>
track_moves env mv e
| BSmove src dst mv s =>
track_moves env mv (subst_reg dst src e)
| BSmakelong src1 src2 dst mv s =>
let e1 := subst_reg_kind dst High src1 Full e in
let e2 := subst_reg_kind dst Low src2 Full e1 in
assertion (reg_unconstrained dst e2);
track_moves env mv e2
| BSlowlong src dst mv s =>
let e1 := subst_reg_kind dst Full src Low e in
assertion (reg_unconstrained dst e1);
track_moves env mv e1
| BShighlong src dst mv s =>
let e1 := subst_reg_kind dst Full src High e in
assertion (reg_unconstrained dst e1);
track_moves env mv e1
| BSop op args res mv1 args' res' mv2 s =>
do e1 <- track_moves env mv2 e;
do e2 <- transfer_use_def args res args' res' (destroyed_by_op op) e1;
track_moves env mv1 e2
| BSopdead op args res mv s =>
assertion (reg_unconstrained res e);
track_moves env mv e
| BSload chunk addr args dst mv1 args' dst' mv2 s =>
do e1 <- track_moves env mv2 e;
do e2 <- transfer_use_def args dst args' dst' (destroyed_by_load chunk addr) e1;
track_moves env mv1 e2
| BSload2 addr addr' args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s =>
do e1 <- track_moves env mv3 e;
let e2 := remove_equation (Eq kind_second_word dst (R dst2')) e1 in
assertion (loc_unconstrained (R dst2') e2);
assertion (can_undef (destroyed_by_load Mint32 addr') e2);
do e3 <- add_equations args args2' e2;
do e4 <- track_moves env mv2 e3;
let e5 := remove_equation (Eq kind_first_word dst (R dst1')) e4 in
assertion (loc_unconstrained (R dst1') e5);
assertion (can_undef (destroyed_by_load Mint32 addr) e5);
assertion (reg_unconstrained dst e5);
do e6 <- add_equations args args1' e5;
track_moves env mv1 e6
| BSload2_1 addr args dst mv1 args' dst' mv2 s =>
do e1 <- track_moves env mv2 e;
let e2 := remove_equation (Eq kind_first_word dst (R dst')) e1 in
assertion (reg_loc_unconstrained dst (R dst') e2);
assertion (can_undef (destroyed_by_load Mint32 addr) e2);
do e3 <- add_equations args args' e2;
track_moves env mv1 e3
| BSload2_2 addr addr' args dst mv1 args' dst' mv2 s =>
do e1 <- track_moves env mv2 e;
let e2 := remove_equation (Eq kind_second_word dst (R dst')) e1 in
assertion (reg_loc_unconstrained dst (R dst') e2);
assertion (can_undef (destroyed_by_load Mint32 addr') e2);
do e3 <- add_equations args args' e2;
track_moves env mv1 e3
| BSloaddead chunk addr args dst mv s =>
assertion (reg_unconstrained dst e);
track_moves env mv e
| BSstore chunk addr args src mv args' src' s =>
assertion (can_undef (destroyed_by_store chunk addr) e);
do e1 <- add_equations (src :: args) (src' :: args') e;
track_moves env mv e1
| BSstore2 addr addr' args src mv1 args1' src1' mv2 args2' src2' s =>
assertion (can_undef (destroyed_by_store Mint32 addr') e);
do e1 <- add_equations args args2'
(add_equation (Eq kind_second_word src (R src2')) e);
do e2 <- track_moves env mv2 e1;
assertion (can_undef (destroyed_by_store Mint32 addr) e2);
do e3 <- add_equations args args1'
(add_equation (Eq kind_first_word src (R src1')) e2);
track_moves env mv1 e3
| BScall sg ros args res mv1 ros' mv2 s =>
let args' := loc_arguments sg in
let res' := loc_result sg in
do e1 <- track_moves env mv2 e;
do e2 <- remove_equations_res res res' e1;
assertion (forallb (fun l => reg_loc_unconstrained res l e2)
(map R (regs_of_rpair res')));
assertion (no_caller_saves e2);
do e3 <- add_equation_ros ros ros' e2;
do e4 <- add_equations_args args (sig_args sg) args' e3;
track_moves env mv1 e4
| BStailcall sg ros args mv1 ros' =>
let args' := loc_arguments sg in
assertion (tailcall_is_possible sg);
assertion (opt_typ_eq sg.(sig_res) f.(RTL.fn_sig).(sig_res));
assertion (ros_compatible_tailcall ros');
do e1 <- add_equation_ros ros ros' empty_eqs;
do e2 <- add_equations_args args (sig_args sg) args' e1;
track_moves env mv1 e2
| BSbuiltin ef args res mv1 args' res' mv2 s =>
do e1 <- track_moves env mv2 e;
do e2 <- remove_equations_builtin_res env res res' e1;
assertion (forallb (fun r => reg_unconstrained r e2)
(params_of_builtin_res res));
assertion (forallb (fun mr => loc_unconstrained (R mr) e2)
(params_of_builtin_res res'));
assertion (can_undef (destroyed_by_builtin ef) e2);
do e3 <-
match ef with
| EF_debug _ _ _ => add_equations_debug_args env args args' e2
| _              => add_equations_builtin_args env args args' e2
end;
track_moves env mv1 e3
| BScond cond args mv args' s1 s2 =>
assertion (can_undef (destroyed_by_cond cond) e);
do e1 <- add_equations args args' e;
track_moves env mv e1
| BSjumptable arg mv arg' tbl =>
assertion (can_undef destroyed_by_jumptable e);
track_moves env mv (add_equation (Eq Full arg (R arg')) e)
| BSreturn None mv =>
track_moves env mv empty_eqs
| BSreturn (Some arg) mv =>
let arg' := loc_result (RTL.fn_sig f) in
do e1 <- add_equations_res arg (sig_res (RTL.fn_sig f)) arg' empty_eqs;
track_moves env mv e1
end.



Definition transfer (f: RTL.function) (env: regenv) (shapes: PTree.t block_shape)
(pc: node) (after: res eqs) : res eqs :=
match after with
| Error _ => after
| OK e =>
match shapes!pc with
| None => Error(MSG "At PC " :: POS pc :: MSG ": unmatched block" :: nil)
| Some shape =>
match transfer_aux f env shape e with
| None => Error(MSG "At PC " :: POS pc :: MSG ": invalid register allocation" :: nil)
| Some e' => OK e'
end
end
end.



Module LEq <: SEMILATTICE.

Definition t := res eqs.

Definition eq (x y: t) :=
match x, y with
| OK a, OK b => EqSet.Equal a b
| Error _, Error _ => True
| _, _ => False
end.

Lemma eq_refl: forall x, eq x x.
Proof. hammer_hook "Allocation" "Allocation.LEq.eq_refl".
intros; destruct x; simpl; auto. red; tauto.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. hammer_hook "Allocation" "Allocation.LEq.eq_sym".
unfold eq; intros; destruct x; destruct y; auto.
red in H; red; intros. rewrite H; tauto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "Allocation" "Allocation.LEq.eq_trans".
unfold eq; intros. destruct x; destruct y; try contradiction; destruct z; auto.
red in H; red in H0; red; intros. rewrite H. auto.
Qed.

Definition beq (x y: t) :=
match x, y with
| OK a, OK b => EqSet.equal a b
| Error _, Error _ => true
| _, _ => false
end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof. hammer_hook "Allocation" "Allocation.LEq.beq_correct".
unfold beq, eq; intros. destruct x; destruct y.
apply EqSet.equal_2. auto.
discriminate.
discriminate.
auto.
Qed.

Definition ge (x y: t) :=
match x, y with
| OK a, OK b => EqSet.Subset b a
| Error _, _ => True
| _, Error _ => False
end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. hammer_hook "Allocation" "Allocation.LEq.ge_refl".
unfold eq, ge, EqSet.Equal, EqSet.Subset; intros.
destruct x; destruct y; auto. intros; rewrite H; auto.
Qed.
Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. hammer_hook "Allocation" "Allocation.LEq.ge_trans".
unfold ge, EqSet.Subset; intros.
destruct x; auto; destruct y; try contradiction.
destruct z; eauto.
Qed.

Definition bot: t := OK empty_eqs.

Lemma ge_bot: forall x, ge x bot.
Proof. hammer_hook "Allocation" "Allocation.LEq.ge_bot".
unfold ge, bot, EqSet.Subset; simpl; intros.
destruct x; auto. intros. elim (EqSet.empty_1 H).
Qed.

Program Definition lub (x y: t) : t :=
match x, y return _ with
| OK a, OK b =>
OK (mkeqs (EqSet.union (eqs1 a) (eqs1 b))
(EqSet2.union (eqs2 a) (eqs2 b)) _)
| OK _, Error _ => y
| Error _, _ => x
end.
Next Obligation.
split; intros.
apply EqSet2.union_1 in H. destruct H; rewrite eqs_same in H.
apply EqSet.union_2; auto. apply EqSet.union_3; auto.
apply EqSet.union_1 in H. destruct H; rewrite <- eqs_same in H.
apply EqSet2.union_2; auto. apply EqSet2.union_3; auto.
Qed.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. hammer_hook "Allocation" "Allocation.LEq.ge_lub_left".
unfold lub, ge, EqSet.Subset; intros.
destruct x; destruct y; auto.
intros; apply EqSet.union_2; auto.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof. hammer_hook "Allocation" "Allocation.LEq.ge_lub_right".
unfold lub, ge, EqSet.Subset; intros.
destruct x; destruct y; auto.
intros; apply EqSet.union_3; auto.
Qed.

End LEq.



Module DS := Backward_Dataflow_Solver(LEq)(NodeSetBackward).



Definition successors_block_shape (bsh: block_shape) : list node :=
match bsh with
| BSnop mv s => s :: nil
| BSmove src dst mv s => s :: nil
| BSmakelong src1 src2 dst mv s => s :: nil
| BSlowlong src dst mv s => s :: nil
| BShighlong src dst mv s => s :: nil
| BSop op args res mv1 args' res' mv2 s => s :: nil
| BSopdead op args res mv s => s :: nil
| BSload chunk addr args dst mv1 args' dst' mv2 s => s :: nil
| BSload2 addr addr' args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s => s :: nil
| BSload2_1 addr args dst mv1 args' dst' mv2 s => s :: nil
| BSload2_2 addr addr' args dst mv1 args' dst' mv2 s => s :: nil
| BSloaddead chunk addr args dst mv s => s :: nil
| BSstore chunk addr args src mv1 args' src' s => s :: nil
| BSstore2 addr addr' args src mv1 args1' src1' mv2 args2' src2' s => s :: nil
| BScall sg ros args res mv1 ros' mv2 s => s :: nil
| BStailcall sg ros args mv1 ros' => nil
| BSbuiltin ef args res mv1 args' res' mv2 s => s :: nil
| BScond cond args mv args' s1 s2 => s1 :: s2 :: nil
| BSjumptable arg mv arg' tbl => tbl
| BSreturn optarg mv => nil
end.

Definition analyze (f: RTL.function) (env: regenv) (bsh: PTree.t block_shape) :=
DS.fixpoint_allnodes bsh successors_block_shape (transfer f env bsh).





Function compat_entry (rparams: list reg) (lparams: list (rpair loc)) (e: eqs)
{struct rparams} : bool :=
match rparams, lparams with
| nil, nil => true
| r1 :: rl,  One l1 :: ll =>
compat_left r1 l1 e && compat_entry rl ll e
| r1 :: rl, Twolong l1 l2 :: ll =>
compat_left2 r1 l1 l2 e && compat_entry rl ll e
| _, _ => false
end.



Definition check_entrypoints_aux (rtl: RTL.function) (ltl: LTL.function)
(env: regenv) (e1: eqs) : option unit :=
do mv <- pair_entrypoints rtl ltl;
do e2 <- track_moves env mv e1;
assertion (compat_entry (RTL.fn_params rtl)
(loc_parameters (RTL.fn_sig rtl)) e2);
assertion (can_undef destroyed_at_function_entry e2);
assertion (zeq (RTL.fn_stacksize rtl) (LTL.fn_stacksize ltl));
assertion (signature_eq (RTL.fn_sig rtl) (LTL.fn_sig ltl));
Some tt.

Local Close Scope option_monad_scope.
Local Open Scope error_monad_scope.

Definition check_entrypoints (rtl: RTL.function) (ltl: LTL.function)
(env: regenv) (bsh: PTree.t block_shape)
(a: PMap.t LEq.t): res unit :=
do e1 <- transfer rtl env bsh (RTL.fn_entrypoint rtl) a!!(RTL.fn_entrypoint rtl);
match check_entrypoints_aux rtl ltl env e1 with
| None => Error (msg "invalid register allocation at entry point")
| Some _ => OK tt
end.



Definition check_function (rtl: RTL.function) (ltl: LTL.function) (env: regenv): res unit :=
let bsh := pair_codes rtl ltl in
match analyze rtl env bsh with
| None => Error (msg "allocation analysis diverges")
| Some a => check_entrypoints rtl ltl env bsh a
end.



Parameter regalloc: RTL.function -> res LTL.function.



Definition transf_function (f: RTL.function) : res LTL.function :=
match type_function f with
| Error m => Error m
| OK env =>
match regalloc f with
| Error m => Error m
| OK tf => do x <- check_function f tf env; OK tf
end
end.

Definition transf_fundef (fd: RTL.fundef) : res LTL.fundef :=
AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: RTL.program) : res LTL.program :=
transform_partial_program transf_fundef p.

