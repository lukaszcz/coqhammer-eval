From Hammer Require Import Hammer.


















Require Import String.
From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Errors.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Archi.

Set Implicit Arguments.





Definition ident := positive.

Definition ident_eq := peq.



Inductive typ : Type :=
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64.

Lemma typ_eq: forall (t1 t2: typ), {t1=t2} + {t1<>t2}.
Proof. hammer_hook "AST" "AST.typ_eq". decide equality. Defined.
Global Opaque typ_eq.

Definition opt_typ_eq: forall (t1 t2: option typ), {t1=t2} + {t1<>t2}
:= option_eq typ_eq.

Definition list_typ_eq: forall (l1 l2: list typ), {l1=l2} + {l1<>l2}
:= list_eq_dec typ_eq.

Definition Tptr : typ := if Archi.ptr64 then Tlong else Tint.

Definition typesize (ty: typ) : Z :=
match ty with
| Tint => 4
| Tfloat => 8
| Tlong => 8
| Tsingle => 4
| Tany32 => 4
| Tany64 => 8
end.

Lemma typesize_pos: forall ty, typesize ty > 0.
Proof. hammer_hook "AST" "AST.typesize_pos". destruct ty; simpl; omega. Qed.

Lemma typesize_Tptr: typesize Tptr = if Archi.ptr64 then 8 else 4.
Proof. hammer_hook "AST" "AST.typesize_Tptr". unfold Tptr; destruct Archi.ptr64; auto. Qed.



Definition subtype (ty1 ty2: typ) : bool :=
match ty1, ty2 with
| Tint, Tint => true
| Tlong, Tlong => true
| Tfloat, Tfloat => true
| Tsingle, Tsingle => true
| (Tint | Tsingle | Tany32), Tany32 => true
| _, Tany64 => true
| _, _ => false
end.

Fixpoint subtype_list (tyl1 tyl2: list typ) : bool :=
match tyl1, tyl2 with
| nil, nil => true
| ty1::tys1, ty2::tys2 => subtype ty1 ty2 && subtype_list tys1 tys2
| _, _ => false
end.



Record calling_convention : Type := mkcallconv {
cc_vararg: bool;
cc_unproto: bool;
cc_structret: bool
}.

Definition cc_default :=
{| cc_vararg := false; cc_unproto := false; cc_structret := false |}.

Definition calling_convention_eq (x y: calling_convention) : {x=y} + {x<>y}.
Proof. hammer_hook "AST" "AST.calling_convention_eq".
decide equality; apply bool_dec.
Defined.
Global Opaque calling_convention_eq.

Record signature : Type := mksignature {
sig_args: list typ;
sig_res: option typ;
sig_cc: calling_convention
}.

Definition proj_sig_res (s: signature) : typ :=
match s.(sig_res) with
| None => Tint
| Some t => t
end.

Definition signature_eq: forall (s1 s2: signature), {s1=s2} + {s1<>s2}.
Proof. hammer_hook "AST" "AST.signature_eq".
generalize opt_typ_eq, list_typ_eq, calling_convention_eq; decide equality.
Defined.
Global Opaque signature_eq.

Definition signature_main :=
{| sig_args := nil; sig_res := Some Tint; sig_cc := cc_default |}.



Inductive memory_chunk : Type :=
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64.

Definition chunk_eq: forall (c1 c2: memory_chunk), {c1=c2} + {c1<>c2}.
Proof. hammer_hook "AST" "AST.chunk_eq". decide equality. Defined.
Global Opaque chunk_eq.

Definition Mptr : memory_chunk := if Archi.ptr64 then Mint64 else Mint32.



Definition type_of_chunk (c: memory_chunk) : typ :=
match c with
| Mint8signed => Tint
| Mint8unsigned => Tint
| Mint16signed => Tint
| Mint16unsigned => Tint
| Mint32 => Tint
| Mint64 => Tlong
| Mfloat32 => Tsingle
| Mfloat64 => Tfloat
| Many32 => Tany32
| Many64 => Tany64
end.

Lemma type_of_Mptr: type_of_chunk Mptr = Tptr.
Proof. hammer_hook "AST" "AST.type_of_Mptr". unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.



Definition chunk_of_type (ty: typ) :=
match ty with
| Tint => Mint32
| Tfloat => Mfloat64
| Tlong => Mint64
| Tsingle => Mfloat32
| Tany32 => Many32
| Tany64 => Many64
end.

Lemma chunk_of_Tptr: chunk_of_type Tptr = Mptr.
Proof. hammer_hook "AST" "AST.chunk_of_Tptr". unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.



Inductive init_data: Type :=
| Init_int8: int -> init_data
| Init_int16: int -> init_data
| Init_int32: int -> init_data
| Init_int64: int64 -> init_data
| Init_float32: float32 -> init_data
| Init_float64: float -> init_data
| Init_space: Z -> init_data
| Init_addrof: ident -> ptrofs -> init_data.

Definition init_data_size (i: init_data) : Z :=
match i with
| Init_int8 _ => 1
| Init_int16 _ => 2
| Init_int32 _ => 4
| Init_int64 _ => 8
| Init_float32 _ => 4
| Init_float64 _ => 8
| Init_addrof _ _ => if Archi.ptr64 then 8 else 4
| Init_space n => Z.max n 0
end.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
match il with
| nil => 0
| i :: il' => init_data_size i + init_data_list_size il'
end.

Lemma init_data_size_pos:
forall i, init_data_size i >= 0.
Proof. hammer_hook "AST" "AST.init_data_size_pos".
destruct i; simpl; try xomega. destruct Archi.ptr64; omega.
Qed.

Lemma init_data_list_size_pos:
forall il, init_data_list_size il >= 0.
Proof. hammer_hook "AST" "AST.init_data_list_size_pos".
induction il; simpl. omega. generalize (init_data_size_pos a); omega.
Qed.



Record globvar (V: Type) : Type := mkglobvar {
gvar_info: V;
gvar_init: list init_data;
gvar_readonly: bool;
gvar_volatile: bool
}.



Inductive globdef (F V: Type) : Type :=
| Gfun (f: F)
| Gvar (v: globvar V).

Arguments Gfun [F V].
Arguments Gvar [F V].

Record program (F V: Type) : Type := mkprogram {
prog_defs: list (ident * globdef F V);
prog_public: list ident;
prog_main: ident
}.

Definition prog_defs_names (F V: Type) (p: program F V) : list ident :=
List.map fst p.(prog_defs).



Definition prog_defmap (F V: Type) (p: program F V) : PTree.t (globdef F V) :=
PTree_Properties.of_list p.(prog_defs).

Section DEFMAP.

Variables F V: Type.
Variable p: program F V.

Lemma in_prog_defmap:
forall id g, (prog_defmap p)!id = Some g -> In (id, g) (prog_defs p).
Proof. hammer_hook "AST" "AST.in_prog_defmap".
apply PTree_Properties.in_of_list.
Qed.

Lemma prog_defmap_dom:
forall id, In id (prog_defs_names p) -> exists g, (prog_defmap p)!id = Some g.
Proof. hammer_hook "AST" "AST.prog_defmap_dom".
apply PTree_Properties.of_list_dom.
Qed.

Lemma prog_defmap_unique:
forall defs1 id g defs2,
prog_defs p = defs1 ++ (id, g) :: defs2 ->
~In id (map fst defs2) ->
(prog_defmap p)!id = Some g.
Proof. hammer_hook "AST" "AST.prog_defmap_unique".
unfold prog_defmap; intros. rewrite H. apply PTree_Properties.of_list_unique; auto.
Qed.

Lemma prog_defmap_norepet:
forall id g,
list_norepet (prog_defs_names p) ->
In (id, g) (prog_defs p) ->
(prog_defmap p)!id = Some g.
Proof. hammer_hook "AST" "AST.prog_defmap_norepet".
apply PTree_Properties.of_list_norepet.
Qed.

End DEFMAP.





Section TRANSF_PROGRAM.

Variable A B V: Type.
Variable transf: A -> B.

Definition transform_program_globdef (idg: ident * globdef A V) : ident * globdef B V :=
match idg with
| (id, Gfun f) => (id, Gfun (transf f))
| (id, Gvar v) => (id, Gvar v)
end.

Definition transform_program (p: program A V) : program B V :=
mkprogram
(List.map transform_program_globdef p.(prog_defs))
p.(prog_public)
p.(prog_main).

End TRANSF_PROGRAM.



Local Open Scope error_monad_scope.

Section TRANSF_PROGRAM_GEN.

Variables A B V W: Type.
Variable transf_fun: ident -> A -> res B.
Variable transf_var: ident -> V -> res W.

Definition transf_globvar (i: ident) (g: globvar V) : res (globvar W) :=
do info' <- transf_var i g.(gvar_info);
OK (mkglobvar info' g.(gvar_init) g.(gvar_readonly) g.(gvar_volatile)).

Fixpoint transf_globdefs (l: list (ident * globdef A V)) : res (list (ident * globdef B W)) :=
match l with
| nil => OK nil
| (id, Gfun f) :: l' =>
match transf_fun id f with
| Error msg => Error (MSG "In function " :: CTX id :: MSG ": " :: msg)
| OK tf =>
do tl' <- transf_globdefs l'; OK ((id, Gfun tf) :: tl')
end
| (id, Gvar v) :: l' =>
match transf_globvar id v with
| Error msg => Error (MSG "In variable " :: CTX id :: MSG ": " :: msg)
| OK tv =>
do tl' <- transf_globdefs l'; OK ((id, Gvar tv) :: tl')
end
end.

Definition transform_partial_program2 (p: program A V) : res (program B W) :=
do gl' <- transf_globdefs p.(prog_defs);
OK (mkprogram gl' p.(prog_public) p.(prog_main)).

End TRANSF_PROGRAM_GEN.



Section TRANSF_PARTIAL_PROGRAM.

Variable A B V: Type.
Variable transf_fun: A -> res B.

Definition transform_partial_program (p: program A V) : res (program B V) :=
transform_partial_program2 (fun i f => transf_fun f) (fun i v => OK v) p.

End TRANSF_PARTIAL_PROGRAM.

Lemma transform_program_partial_program:
forall (A B V: Type) (transf_fun: A -> B) (p: program A V),
transform_partial_program (fun f => OK (transf_fun f)) p = OK (transform_program transf_fun p).
Proof. hammer_hook "AST" "AST.transform_program_partial_program".
intros. unfold transform_partial_program, transform_partial_program2.
assert (EQ: forall l,
transf_globdefs (fun i f => OK (transf_fun f)) (fun i (v: V) => OK v) l =
OK (List.map (transform_program_globdef transf_fun) l)).
{ induction l as [ | [id g] l]; simpl.
- auto.
- destruct g; simpl; rewrite IHl; simpl. auto. destruct v; auto.
}
rewrite EQ; simpl. auto.
Qed.





Inductive external_function : Type :=
| EF_external (name: string) (sg: signature)

| EF_builtin (name: string) (sg: signature)

| EF_runtime (name: string) (sg: signature)

| EF_vload (chunk: memory_chunk)

| EF_vstore (chunk: memory_chunk)

| EF_malloc

| EF_free

| EF_memcpy (sz: Z) (al: Z)

| EF_annot (kind: positive) (text: string) (targs: list typ)

| EF_annot_val (kind: positive) (text: string) (targ: typ)

| EF_inline_asm (text: string) (sg: signature) (clobbers: list string)

| EF_debug (kind: positive) (text: ident) (targs: list typ).




Definition ef_sig (ef: external_function): signature :=
match ef with
| EF_external name sg => sg
| EF_builtin name sg => sg
| EF_runtime name sg => sg
| EF_vload chunk => mksignature (Tptr :: nil) (Some (type_of_chunk chunk)) cc_default
| EF_vstore chunk => mksignature (Tptr :: type_of_chunk chunk :: nil) None cc_default
| EF_malloc => mksignature (Tptr :: nil) (Some Tptr) cc_default
| EF_free => mksignature (Tptr :: nil) None cc_default
| EF_memcpy sz al => mksignature (Tptr :: Tptr :: nil) None cc_default
| EF_annot kind text targs => mksignature targs None cc_default
| EF_annot_val kind text targ => mksignature (targ :: nil) (Some targ) cc_default
| EF_inline_asm text sg clob => sg
| EF_debug kind text targs => mksignature targs None cc_default
end.



Definition ef_inline (ef: external_function) : bool :=
match ef with
| EF_external name sg => false
| EF_builtin name sg => true
| EF_runtime name sg => false
| EF_vload chunk => true
| EF_vstore chunk => true
| EF_malloc => false
| EF_free => false
| EF_memcpy sz al => true
| EF_annot kind text targs => true
| EF_annot_val kind Text rg => true
| EF_inline_asm text sg clob => true
| EF_debug kind text targs => true
end.



Definition ef_reloads (ef: external_function) : bool :=
match ef with
| EF_annot kind text targs => false
| EF_debug kind text targs => false
| _ => true
end.



Definition external_function_eq: forall (ef1 ef2: external_function), {ef1=ef2} + {ef1<>ef2}.
Proof. hammer_hook "AST" "AST.external_function_eq".
generalize ident_eq string_dec signature_eq chunk_eq typ_eq list_eq_dec zeq Int.eq_dec; intros.
decide equality.
Defined.
Global Opaque external_function_eq.



Inductive fundef (F: Type): Type :=
| Internal: F -> fundef F
| External: external_function -> fundef F.

Arguments External [F].

Section TRANSF_FUNDEF.

Variable A B: Type.
Variable transf: A -> B.

Definition transf_fundef (fd: fundef A): fundef B :=
match fd with
| Internal f => Internal (transf f)
| External ef => External ef
end.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Variable A B: Type.
Variable transf_partial: A -> res B.

Definition transf_partial_fundef (fd: fundef A): res (fundef B) :=
match fd with
| Internal f => do f' <- transf_partial f; OK (Internal f')
| External ef => OK (External ef)
end.

End TRANSF_PARTIAL_FUNDEF.



Set Contextual Implicit.



Inductive rpair (A: Type) : Type :=
| One (r: A)
| Twolong (rhi rlo: A).

Definition typ_rpair (A: Type) (typ_of: A -> typ) (p: rpair A): typ :=
match p with
| One r => typ_of r
| Twolong rhi rlo => Tlong
end.

Definition map_rpair (A B: Type) (f: A -> B) (p: rpair A): rpair B :=
match p with
| One r => One (f r)
| Twolong rhi rlo => Twolong (f rhi) (f rlo)
end.

Definition regs_of_rpair (A: Type) (p: rpair A): list A :=
match p with
| One r => r :: nil
| Twolong rhi rlo => rhi :: rlo :: nil
end.

Fixpoint regs_of_rpairs (A: Type) (l: list (rpair A)): list A :=
match l with
| nil => nil
| p :: l => regs_of_rpair p ++ regs_of_rpairs l
end.

Lemma in_regs_of_rpairs:
forall (A: Type) (x: A) p, In x (regs_of_rpair p) -> forall l, In p l -> In x (regs_of_rpairs l).
Proof. hammer_hook "AST" "AST.in_regs_of_rpairs".
induction l; simpl; intros. auto. apply in_app. destruct H0; auto. subst a. auto.
Qed.

Lemma in_regs_of_rpairs_inv:
forall (A: Type) (x: A) l, In x (regs_of_rpairs l) -> exists p, In p l /\ In x (regs_of_rpair p).
Proof. hammer_hook "AST" "AST.in_regs_of_rpairs_inv".
induction l; simpl; intros. contradiction.
rewrite in_app_iff in H; destruct H.
exists a; auto.
apply IHl in H. firstorder auto.
Qed.

Definition forall_rpair (A: Type) (P: A -> Prop) (p: rpair A): Prop :=
match p with
| One r => P r
| Twolong rhi rlo => P rhi /\ P rlo
end.



Inductive builtin_arg (A: Type) : Type :=
| BA (x: A)
| BA_int (n: int)
| BA_long (n: int64)
| BA_float (f: float)
| BA_single (f: float32)
| BA_loadstack (chunk: memory_chunk) (ofs: ptrofs)
| BA_addrstack (ofs: ptrofs)
| BA_loadglobal (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
| BA_addrglobal (id: ident) (ofs: ptrofs)
| BA_splitlong (hi lo: builtin_arg A)
| BA_addptr (a1 a2: builtin_arg A).

Inductive builtin_res (A: Type) : Type :=
| BR (x: A)
| BR_none
| BR_splitlong (hi lo: builtin_res A).

Fixpoint globals_of_builtin_arg (A: Type) (a: builtin_arg A) : list ident :=
match a with
| BA_loadglobal chunk id ofs => id :: nil
| BA_addrglobal id ofs => id :: nil
| BA_splitlong hi lo => globals_of_builtin_arg hi ++ globals_of_builtin_arg lo
| BA_addptr a1 a2 => globals_of_builtin_arg a1 ++ globals_of_builtin_arg a2
| _ => nil
end.

Definition globals_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list ident :=
List.fold_right (fun a l => globals_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_arg (A: Type) (a: builtin_arg A) : list A :=
match a with
| BA x => x :: nil
| BA_splitlong hi lo => params_of_builtin_arg hi ++ params_of_builtin_arg lo
| BA_addptr a1 a2 => params_of_builtin_arg a1 ++ params_of_builtin_arg a2
| _ => nil
end.

Definition params_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list A :=
List.fold_right (fun a l => params_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_res (A: Type) (a: builtin_res A) : list A :=
match a with
| BR x => x :: nil
| BR_none => nil
| BR_splitlong hi lo => params_of_builtin_res hi ++ params_of_builtin_res lo
end.

Fixpoint map_builtin_arg (A B: Type) (f: A -> B) (a: builtin_arg A) : builtin_arg B :=
match a with
| BA x => BA (f x)
| BA_int n => BA_int n
| BA_long n => BA_long n
| BA_float n => BA_float n
| BA_single n => BA_single n
| BA_loadstack chunk ofs => BA_loadstack chunk ofs
| BA_addrstack ofs => BA_addrstack ofs
| BA_loadglobal chunk id ofs => BA_loadglobal chunk id ofs
| BA_addrglobal id ofs => BA_addrglobal id ofs
| BA_splitlong hi lo =>
BA_splitlong (map_builtin_arg f hi) (map_builtin_arg f lo)
| BA_addptr a1 a2 =>
BA_addptr (map_builtin_arg f a1) (map_builtin_arg f a2)
end.

Fixpoint map_builtin_res (A B: Type) (f: A -> B) (a: builtin_res A) : builtin_res B :=
match a with
| BR x => BR (f x)
| BR_none => BR_none
| BR_splitlong hi lo =>
BR_splitlong (map_builtin_res f hi) (map_builtin_res f lo)
end.



Inductive builtin_arg_constraint : Type :=
| OK_default
| OK_const
| OK_addrstack
| OK_addressing
| OK_all.
