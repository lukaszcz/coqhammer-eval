From Hammer Require Import Hammer.


















From compcert Require Import Coqlib.
From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Ctypes.
From compcert Require Archi.



Inductive unary_operation : Type :=
| Onotbool : unary_operation
| Onotint : unary_operation
| Oneg : unary_operation
| Oabsfloat : unary_operation.

Inductive binary_operation : Type :=
| Oadd : binary_operation
| Osub : binary_operation
| Omul : binary_operation
| Odiv : binary_operation
| Omod : binary_operation
| Oand : binary_operation
| Oor : binary_operation
| Oxor : binary_operation
| Oshl : binary_operation
| Oshr : binary_operation
| Oeq: binary_operation
| One: binary_operation
| Olt: binary_operation
| Ogt: binary_operation
| Ole: binary_operation
| Oge: binary_operation.

Inductive incr_or_decr : Type := Incr | Decr.







Inductive classify_cast_cases : Type :=
| cast_case_pointer
| cast_case_i2i (sz2:intsize) (si2:signedness)
| cast_case_f2f
| cast_case_s2s
| cast_case_f2s
| cast_case_s2f
| cast_case_i2f (si1: signedness)
| cast_case_i2s (si1: signedness)
| cast_case_f2i (sz2:intsize) (si2:signedness)
| cast_case_s2i (sz2:intsize) (si2:signedness)
| cast_case_l2l
| cast_case_i2l (si1: signedness)
| cast_case_l2i (sz2: intsize) (si2: signedness)
| cast_case_l2f (si1: signedness)
| cast_case_l2s (si1: signedness)
| cast_case_f2l (si2:signedness)
| cast_case_s2l (si2:signedness)
| cast_case_i2bool
| cast_case_l2bool
| cast_case_f2bool
| cast_case_s2bool
| cast_case_struct (id1 id2: ident)
| cast_case_union  (id1 id2: ident)
| cast_case_void
| cast_case_default.

Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
match tto, tfrom with

| Tvoid, _ => cast_case_void

| Tint IBool _ _, Tint _ _ _ => cast_case_i2bool
| Tint IBool _ _, Tlong _ _ => cast_case_l2bool
| Tint IBool _ _, Tfloat F64 _ => cast_case_f2bool
| Tint IBool _ _, Tfloat F32 _ => cast_case_s2bool
| Tint IBool _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
if Archi.ptr64 then cast_case_l2bool else cast_case_i2bool

| Tint sz2 si2 _, Tint _ _ _ =>
if Archi.ptr64 then cast_case_i2i sz2 si2
else if intsize_eq sz2 I32 then cast_case_pointer
else cast_case_i2i sz2 si2
| Tint sz2 si2 _, Tlong _ _ => cast_case_l2i sz2 si2
| Tint sz2 si2 _, Tfloat F64 _ => cast_case_f2i sz2 si2
| Tint sz2 si2 _, Tfloat F32 _ => cast_case_s2i sz2 si2
| Tint sz2 si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
if Archi.ptr64 then cast_case_l2i sz2 si2
else if intsize_eq sz2 I32 then cast_case_pointer
else cast_case_i2i sz2 si2

| Tlong _ _, Tlong _ _ =>
if Archi.ptr64 then cast_case_pointer else cast_case_l2l
| Tlong _ _, Tint sz1 si1 _ => cast_case_i2l si1
| Tlong si2 _, Tfloat F64 _ => cast_case_f2l si2
| Tlong si2 _, Tfloat F32 _ => cast_case_s2l si2
| Tlong si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
if Archi.ptr64 then cast_case_pointer else cast_case_i2l si2

| Tfloat F64 _, Tint sz1 si1 _ => cast_case_i2f si1
| Tfloat F32 _, Tint sz1 si1 _ => cast_case_i2s si1
| Tfloat F64 _, Tlong si1 _ => cast_case_l2f si1
| Tfloat F32 _, Tlong si1 _ => cast_case_l2s si1
| Tfloat F64 _, Tfloat F64 _ => cast_case_f2f
| Tfloat F32 _, Tfloat F32 _ => cast_case_s2s
| Tfloat F64 _, Tfloat F32 _ => cast_case_s2f
| Tfloat F32 _, Tfloat F64 _ => cast_case_f2s

| Tpointer _ _, Tint _ _ _ =>
if Archi.ptr64 then cast_case_i2l Unsigned else cast_case_pointer
| Tpointer _ _, Tlong _ _ =>
if Archi.ptr64 then cast_case_pointer else cast_case_l2i I32 Unsigned
| Tpointer _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => cast_case_pointer

| Tstruct id2 _, Tstruct id1 _ => cast_case_struct id1 id2
| Tunion id2 _, Tunion id1 _ => cast_case_union id1 id2

| _, _ => cast_case_default
end.



Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
match sz, sg with
| I8, Signed => Int.sign_ext 8 i
| I8, Unsigned => Int.zero_ext 8 i
| I16, Signed => Int.sign_ext 16 i
| I16, Unsigned => Int.zero_ext 16 i
| I32, _ => i
| IBool, _ => if Int.eq i Int.zero then Int.zero else Int.one
end.

Definition cast_int_float (si: signedness) (i: int) : float :=
match si with
| Signed => Float.of_int i
| Unsigned => Float.of_intu i
end.

Definition cast_float_int (si : signedness) (f: float) : option int :=
match si with
| Signed => Float.to_int f
| Unsigned => Float.to_intu f
end.

Definition cast_int_single (si: signedness) (i: int) : float32 :=
match si with
| Signed => Float32.of_int i
| Unsigned => Float32.of_intu i
end.

Definition cast_single_int (si : signedness) (f: float32) : option int :=
match si with
| Signed => Float32.to_int f
| Unsigned => Float32.to_intu f
end.

Definition cast_int_long (si: signedness) (i: int) : int64 :=
match si with
| Signed => Int64.repr (Int.signed i)
| Unsigned => Int64.repr (Int.unsigned i)
end.

Definition cast_long_float (si: signedness) (i: int64) : float :=
match si with
| Signed => Float.of_long i
| Unsigned => Float.of_longu i
end.

Definition cast_long_single (si: signedness) (i: int64) : float32 :=
match si with
| Signed => Float32.of_long i
| Unsigned => Float32.of_longu i
end.

Definition cast_float_long (si : signedness) (f: float) : option int64 :=
match si with
| Signed => Float.to_long f
| Unsigned => Float.to_longu f
end.

Definition cast_single_long (si : signedness) (f: float32) : option int64 :=
match si with
| Signed => Float32.to_long f
| Unsigned => Float32.to_longu f
end.

Definition sem_cast (v: val) (t1 t2: type) (m: mem): option val :=
match classify_cast t1 t2 with
| cast_case_pointer =>
match v with
| Vptr _ _ => Some v
| Vint _ => if Archi.ptr64 then None else Some v
| Vlong _ => if Archi.ptr64 then Some v else None
| _ => None
end
| cast_case_i2i sz2 si2 =>
match v with
| Vint i => Some (Vint (cast_int_int sz2 si2 i))
| _ => None
end
| cast_case_f2f =>
match v with
| Vfloat f => Some (Vfloat f)
| _ => None
end
| cast_case_s2s =>
match v with
| Vsingle f => Some (Vsingle f)
| _ => None
end
| cast_case_s2f =>
match v with
| Vsingle f => Some (Vfloat (Float.of_single f))
| _ => None
end
| cast_case_f2s =>
match v with
| Vfloat f => Some (Vsingle (Float.to_single f))
| _ => None
end
| cast_case_i2f si1 =>
match v with
| Vint i => Some (Vfloat (cast_int_float si1 i))
| _ => None
end
| cast_case_i2s si1 =>
match v with
| Vint i => Some (Vsingle (cast_int_single si1 i))
| _ => None
end
| cast_case_f2i sz2 si2 =>
match v with
| Vfloat f =>
match cast_float_int si2 f with
| Some i => Some (Vint (cast_int_int sz2 si2 i))
| None => None
end
| _ => None
end
| cast_case_s2i sz2 si2 =>
match v with
| Vsingle f =>
match cast_single_int si2 f with
| Some i => Some (Vint (cast_int_int sz2 si2 i))
| None => None
end
| _ => None
end
| cast_case_i2bool =>
match v with
| Vint n =>
Some(Vint(if Int.eq n Int.zero then Int.zero else Int.one))
| Vptr b ofs =>
if Archi.ptr64 then None else
if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None
| _ => None
end
| cast_case_l2bool =>
match v with
| Vlong n =>
Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
| Vptr b ofs =>
if negb Archi.ptr64 then None else
if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None

| _ => None
end
| cast_case_f2bool =>
match v with
| Vfloat f =>
Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
| _ => None
end
| cast_case_s2bool =>
match v with
| Vsingle f =>
Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
| _ => None
end
| cast_case_l2l =>
match v with
| Vlong n => Some (Vlong n)
| _ => None
end
| cast_case_i2l si =>
match v with
| Vint n => Some(Vlong (cast_int_long si n))
| _ => None
end
| cast_case_l2i sz si =>
match v with
| Vlong n => Some(Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
| _ => None
end
| cast_case_l2f si1 =>
match v with
| Vlong i => Some (Vfloat (cast_long_float si1 i))
| _ => None
end
| cast_case_l2s si1 =>
match v with
| Vlong i => Some (Vsingle (cast_long_single si1 i))
| _ => None
end
| cast_case_f2l si2 =>
match v with
| Vfloat f =>
match cast_float_long si2 f with
| Some i => Some (Vlong i)
| None => None
end
| _ => None
end
| cast_case_s2l si2 =>
match v with
| Vsingle f =>
match cast_single_long si2 f with
| Some i => Some (Vlong i)
| None => None
end
| _ => None
end
| cast_case_struct id1 id2 =>
match v with
| Vptr b ofs =>
if ident_eq id1 id2 then Some v else None
| _ => None
end
| cast_case_union id1 id2 =>
match v with
| Vptr b ofs =>
if ident_eq id1 id2 then Some v else None
| _ => None
end
| cast_case_void =>
Some v
| cast_case_default =>
None
end.



Inductive classify_bool_cases : Type :=
| bool_case_i
| bool_case_l
| bool_case_f
| bool_case_s
| bool_default.

Definition classify_bool (ty: type) : classify_bool_cases :=
match typeconv ty with
| Tint _ _ _ => bool_case_i
| Tpointer _ _ => if Archi.ptr64 then bool_case_l else bool_case_i
| Tfloat F64 _ => bool_case_f
| Tfloat F32 _ => bool_case_s
| Tlong _ _ => bool_case_l
| _ => bool_default
end.



Definition bool_val (v: val) (t: type) (m: mem) : option bool :=
match classify_bool t with
| bool_case_i =>
match v with
| Vint n => Some (negb (Int.eq n Int.zero))
| Vptr b ofs =>
if Archi.ptr64 then None else
if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
| _ => None
end
| bool_case_l =>
match v with
| Vlong n => Some (negb (Int64.eq n Int64.zero))
| Vptr b ofs =>
if negb Archi.ptr64 then None else
if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
| _ => None
end
| bool_case_f =>
match v with
| Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
| _ => None
end
| bool_case_s =>
match v with
| Vsingle f => Some (negb (Float32.cmp Ceq f Float32.zero))
| _ => None
end
| bool_default => None
end.





Definition sem_notbool (v: val) (ty: type) (m: mem): option val :=
option_map (fun b => Val.of_bool (negb b)) (bool_val v ty m).



Inductive classify_neg_cases : Type :=
| neg_case_i(s: signedness)
| neg_case_f
| neg_case_s
| neg_case_l(s: signedness)
| neg_default.

Definition classify_neg (ty: type) : classify_neg_cases :=
match ty with
| Tint I32 Unsigned _ => neg_case_i Unsigned
| Tint _ _ _ => neg_case_i Signed
| Tfloat F64 _ => neg_case_f
| Tfloat F32 _ => neg_case_s
| Tlong si _ => neg_case_l si
| _ => neg_default
end.

Definition sem_neg (v: val) (ty: type) : option val :=
match classify_neg ty with
| neg_case_i sg =>
match v with
| Vint n => Some (Vint (Int.neg n))
| _ => None
end
| neg_case_f =>
match v with
| Vfloat f => Some (Vfloat (Float.neg f))
| _ => None
end
| neg_case_s =>
match v with
| Vsingle f => Some (Vsingle (Float32.neg f))
| _ => None
end
| neg_case_l sg =>
match v with
| Vlong n => Some (Vlong (Int64.neg n))
| _ => None
end
| neg_default => None
end.

Definition sem_absfloat (v: val) (ty: type) : option val :=
match classify_neg ty with
| neg_case_i sg =>
match v with
| Vint n => Some (Vfloat (Float.abs (cast_int_float sg n)))
| _ => None
end
| neg_case_f =>
match v with
| Vfloat f => Some (Vfloat (Float.abs f))
| _ => None
end
| neg_case_s =>
match v with
| Vsingle f => Some (Vfloat (Float.abs (Float.of_single f)))
| _ => None
end
| neg_case_l sg =>
match v with
| Vlong n => Some (Vfloat (Float.abs (cast_long_float sg n)))
| _ => None
end
| neg_default => None
end.



Inductive classify_notint_cases : Type :=
| notint_case_i(s: signedness)
| notint_case_l(s: signedness)
| notint_default.

Definition classify_notint (ty: type) : classify_notint_cases :=
match ty with
| Tint I32 Unsigned _ => notint_case_i Unsigned
| Tint _ _ _ => notint_case_i Signed
| Tlong si _ => notint_case_l si
| _ => notint_default
end.

Definition sem_notint (v: val) (ty: type): option val :=
match classify_notint ty with
| notint_case_i sg =>
match v with
| Vint n => Some (Vint (Int.not n))
| _ => None
end
| notint_case_l sg =>
match v with
| Vlong n => Some (Vlong (Int64.not n))
| _ => None
end
| notint_default => None
end.





Inductive binarith_cases: Type :=
| bin_case_i (s: signedness)
| bin_case_l (s: signedness)
| bin_case_f
| bin_case_s
| bin_default.

Definition classify_binarith (ty1: type) (ty2: type) : binarith_cases :=
match ty1, ty2 with
| Tint I32 Unsigned _, Tint _ _ _ => bin_case_i Unsigned
| Tint _ _ _, Tint I32 Unsigned _ => bin_case_i Unsigned
| Tint _ _ _, Tint _ _ _ => bin_case_i Signed
| Tlong Signed _, Tlong Signed _ => bin_case_l Signed
| Tlong _ _, Tlong _ _ => bin_case_l Unsigned
| Tlong sg _, Tint _ _ _ => bin_case_l sg
| Tint _ _ _, Tlong sg _ => bin_case_l sg
| Tfloat F32 _, Tfloat F32 _ => bin_case_s
| Tfloat _ _, Tfloat _ _ => bin_case_f
| Tfloat F64 _, (Tint _ _ _ | Tlong _ _) => bin_case_f
| (Tint _ _ _ | Tlong _ _), Tfloat F64 _ => bin_case_f
| Tfloat F32 _, (Tint _ _ _ | Tlong _ _) => bin_case_s
| (Tint _ _ _ | Tlong _ _), Tfloat F32 _ => bin_case_s
| _, _ => bin_default
end.



Definition binarith_type (c: binarith_cases) : type :=
match c with
| bin_case_i sg => Tint I32 sg noattr
| bin_case_l sg => Tlong sg noattr
| bin_case_f    => Tfloat F64 noattr
| bin_case_s    => Tfloat F32 noattr
| bin_default   => Tvoid
end.

Definition sem_binarith
(sem_int: signedness -> int -> int -> option val)
(sem_long: signedness -> int64 -> int64 -> option val)
(sem_float: float -> float -> option val)
(sem_single: float32 -> float32 -> option val)
(v1: val) (t1: type) (v2: val) (t2: type) (m: mem): option val :=
let c := classify_binarith t1 t2 in
let t := binarith_type c in
match sem_cast v1 t1 t m with
| None => None
| Some v1' =>
match sem_cast v2 t2 t m with
| None => None
| Some v2' =>
match c with
| bin_case_i sg =>
match v1', v2' with
| Vint n1, Vint n2 => sem_int sg n1 n2
| _,  _ => None
end
| bin_case_f =>
match v1', v2' with
| Vfloat n1, Vfloat n2 => sem_float n1 n2
| _,  _ => None
end
| bin_case_s =>
match v1', v2' with
| Vsingle n1, Vsingle n2 => sem_single n1 n2
| _,  _ => None
end
| bin_case_l sg =>
match v1', v2' with
| Vlong n1, Vlong n2 => sem_long sg n1 n2
| _,  _ => None
end
| bin_default => None
end end end.



Inductive classify_add_cases : Type :=
| add_case_pi (ty: type) (si: signedness)
| add_case_pl (ty: type)
| add_case_ip (si: signedness) (ty: type)
| add_case_lp (ty: type)
| add_default.

Definition classify_add (ty1: type) (ty2: type) :=
match typeconv ty1, typeconv ty2 with
| Tpointer ty _, Tint _ si _ => add_case_pi ty si
| Tpointer ty _, Tlong _ _ => add_case_pl ty
| Tint _ si _, Tpointer ty _ => add_case_ip si ty
| Tlong _ _, Tpointer ty _ => add_case_lp ty
| _, _ => add_default
end.

Definition ptrofs_of_int (si: signedness) (n: int) : ptrofs :=
match si with
| Signed => Ptrofs.of_ints n
| Unsigned => Ptrofs.of_intu n
end.

Definition sem_add_ptr_int (cenv: composite_env) (ty: type) (si: signedness) (v1 v2: val): option val :=
match v1, v2 with
| Vptr b1 ofs1, Vint n2 =>
let n2 := ptrofs_of_int si n2 in
Some (Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
| Vint n1, Vint n2 =>
if Archi.ptr64 then None else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
| Vlong n1, Vint n2 =>
let n2 := cast_int_long si n2 in
if Archi.ptr64 then Some (Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
| _,  _ => None
end.

Definition sem_add_ptr_long (cenv: composite_env) (ty: type) (v1 v2: val): option val :=
match v1, v2 with
| Vptr b1 ofs1, Vlong n2 =>
let n2 := Ptrofs.of_int64 n2 in
Some (Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
| Vint n1, Vlong n2 =>
let n2 := Int.repr (Int64.unsigned n2) in
if Archi.ptr64 then None else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
| Vlong n1, Vlong n2 =>
if Archi.ptr64 then Some (Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
| _,  _ => None
end.

Definition sem_add (cenv: composite_env) (v1:val) (t1:type) (v2: val) (t2:type) (m: mem): option val :=
match classify_add t1 t2 with
| add_case_pi ty si =>
sem_add_ptr_int cenv ty si v1 v2
| add_case_pl ty =>
sem_add_ptr_long cenv ty v1 v2
| add_case_ip si ty =>
sem_add_ptr_int cenv ty si v2 v1
| add_case_lp ty =>
sem_add_ptr_long cenv ty v2 v1
| add_default =>
sem_binarith
(fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
(fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
(fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
(fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
v1 t1 v2 t2 m
end.



Inductive classify_sub_cases : Type :=
| sub_case_pi (ty: type) (si: signedness)
| sub_case_pp (ty: type)
| sub_case_pl (ty: type)
| sub_default.

Definition classify_sub (ty1: type) (ty2: type) :=
match typeconv ty1, typeconv ty2 with
| Tpointer ty _, Tint _ si _ => sub_case_pi ty si
| Tpointer ty _ , Tpointer _ _ => sub_case_pp ty
| Tpointer ty _, Tlong _ _ => sub_case_pl ty
| _, _ => sub_default
end.

Definition sem_sub (cenv: composite_env) (v1:val) (t1:type) (v2: val) (t2:type) (m:mem): option val :=
match classify_sub t1 t2 with
| sub_case_pi ty si =>
match v1, v2 with
| Vptr b1 ofs1, Vint n2 =>
let n2 := ptrofs_of_int si n2 in
Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
| Vint n1, Vint n2 =>
if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
| Vlong n1, Vint n2 =>
let n2 := cast_int_long si n2 in
if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
| _,  _ => None
end
| sub_case_pl ty =>
match v1, v2 with
| Vptr b1 ofs1, Vlong n2 =>
let n2 := Ptrofs.of_int64 n2 in
Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
| Vint n1, Vlong n2 =>
let n2 := Int.repr (Int64.unsigned n2) in
if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
| Vlong n1, Vlong n2 =>
if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
| _,  _ => None
end
| sub_case_pp ty =>
match v1,v2 with
| Vptr b1 ofs1, Vptr b2 ofs2 =>
if eq_block b1 b2 then
let sz := sizeof cenv ty in
if zlt 0 sz && zle sz Ptrofs.max_signed
then Some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
else None
else None
| _, _ => None
end
| sub_default =>
sem_binarith
(fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
(fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
(fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
(fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
v1 t1 v2 t2 m
end.



Definition sem_mul (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
sem_binarith
(fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
(fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
(fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
(fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
v1 t1 v2 t2 m.

Definition sem_div (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
sem_binarith
(fun sg n1 n2 =>
match sg with
| Signed =>
if Int.eq n2 Int.zero
|| Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
then None else Some(Vint(Int.divs n1 n2))
| Unsigned =>
if Int.eq n2 Int.zero
then None else Some(Vint(Int.divu n1 n2))
end)
(fun sg n1 n2 =>
match sg with
| Signed =>
if Int64.eq n2 Int64.zero
|| Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
then None else Some(Vlong(Int64.divs n1 n2))
| Unsigned =>
if Int64.eq n2 Int64.zero
then None else Some(Vlong(Int64.divu n1 n2))
end)
(fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
(fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
v1 t1 v2 t2 m.

Definition sem_mod (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
sem_binarith
(fun sg n1 n2 =>
match sg with
| Signed =>
if Int.eq n2 Int.zero
|| Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
then None else Some(Vint(Int.mods n1 n2))
| Unsigned =>
if Int.eq n2 Int.zero
then None else Some(Vint(Int.modu n1 n2))
end)
(fun sg n1 n2 =>
match sg with
| Signed =>
if Int64.eq n2 Int64.zero
|| Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
then None else Some(Vlong(Int64.mods n1 n2))
| Unsigned =>
if Int64.eq n2 Int64.zero
then None else Some(Vlong(Int64.modu n1 n2))
end)
(fun n1 n2 => None)
(fun n1 n2 => None)
v1 t1 v2 t2 m.

Definition sem_and (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
sem_binarith
(fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
(fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
(fun n1 n2 => None)
(fun n1 n2 => None)
v1 t1 v2 t2 m.

Definition sem_or (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
sem_binarith
(fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
(fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
(fun n1 n2 => None)
(fun n1 n2 => None)
v1 t1 v2 t2 m.

Definition sem_xor (v1:val) (t1:type) (v2: val) (t2:type) (m:mem) : option val :=
sem_binarith
(fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
(fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
(fun n1 n2 => None)
(fun n1 n2 => None)
v1 t1 v2 t2 m.





Inductive classify_shift_cases : Type:=
| shift_case_ii(s: signedness)
| shift_case_ll(s: signedness)
| shift_case_il(s: signedness)
| shift_case_li(s: signedness)
| shift_default.

Definition classify_shift (ty1: type) (ty2: type) :=
match typeconv ty1, typeconv ty2 with
| Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
| Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
| Tint I32 Unsigned _, Tlong _ _ => shift_case_il Unsigned
| Tint _ _ _, Tlong _ _ => shift_case_il Signed
| Tlong s _, Tint _ _ _ => shift_case_li s
| Tlong s _, Tlong _ _ => shift_case_ll s
| _,_  => shift_default
end.

Definition sem_shift
(sem_int: signedness -> int -> int -> int)
(sem_long: signedness -> int64 -> int64 -> int64)
(v1: val) (t1: type) (v2: val) (t2: type) : option val :=
match classify_shift t1 t2 with
| shift_case_ii sg =>
match v1, v2 with
| Vint n1, Vint n2 =>
if Int.ltu n2 Int.iwordsize
then Some(Vint(sem_int sg n1 n2)) else None
| _, _ => None
end
| shift_case_il sg =>
match v1, v2 with
| Vint n1, Vlong n2 =>
if Int64.ltu n2 (Int64.repr 32)
then Some(Vint(sem_int sg n1 (Int64.loword n2))) else None
| _, _ => None
end
| shift_case_li sg =>
match v1, v2 with
| Vlong n1, Vint n2 =>
if Int.ltu n2 Int64.iwordsize'
then Some(Vlong(sem_long sg n1 (Int64.repr (Int.unsigned n2)))) else None
| _, _ => None
end
| shift_case_ll sg =>
match v1, v2 with
| Vlong n1, Vlong n2 =>
if Int64.ltu n2 Int64.iwordsize
then Some(Vlong(sem_long sg n1 n2)) else None
| _, _ => None
end
| shift_default => None
end.

Definition sem_shl (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
sem_shift
(fun sg n1 n2 => Int.shl n1 n2)
(fun sg n1 n2 => Int64.shl n1 n2)
v1 t1 v2 t2.

Definition sem_shr (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
sem_shift
(fun sg n1 n2 => match sg with Signed => Int.shr n1 n2 | Unsigned => Int.shru n1 n2 end)
(fun sg n1 n2 => match sg with Signed => Int64.shr n1 n2 | Unsigned => Int64.shru n1 n2 end)
v1 t1 v2 t2.



Inductive classify_cmp_cases : Type :=
| cmp_case_pp
| cmp_case_pi (si: signedness)
| cmp_case_ip (si: signedness)
| cmp_case_pl
| cmp_case_lp
| cmp_default.

Definition classify_cmp (ty1: type) (ty2: type) :=
match typeconv ty1, typeconv ty2 with
| Tpointer _ _ , Tpointer _ _ => cmp_case_pp
| Tpointer _ _ , Tint _ si _ => cmp_case_pi si
| Tint _ si _, Tpointer _ _ => cmp_case_ip si
| Tpointer _ _ , Tlong _ _ => cmp_case_pl
| Tlong _ _ , Tpointer _ _ => cmp_case_lp
| _, _ => cmp_default
end.

Definition cmp_ptr (m: mem) (c: comparison) (v1 v2: val): option val :=
option_map Val.of_bool
(if Archi.ptr64
then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2).

Definition sem_cmp (c:comparison)
(v1: val) (t1: type) (v2: val) (t2: type)
(m: mem): option val :=
match classify_cmp t1 t2 with
| cmp_case_pp =>
cmp_ptr m c v1 v2
| cmp_case_pi si =>
match v2 with
| Vint n2 =>
let v2' := Vptrofs (ptrofs_of_int si n2) in
cmp_ptr m c v1 v2'
| Vptr b ofs =>
if Archi.ptr64 then None else cmp_ptr m c v1 v2
| _ =>
None
end
| cmp_case_ip si =>
match v1 with
| Vint n1 =>
let v1' := Vptrofs (ptrofs_of_int si n1) in
cmp_ptr m c v1' v2
| Vptr b ofs =>
if Archi.ptr64 then None else cmp_ptr m c v1 v2
| _ =>
None
end
| cmp_case_pl =>
match v2 with
| Vlong n2 =>
let v2' := Vptrofs (Ptrofs.of_int64 n2) in
cmp_ptr m c v1 v2'
| Vptr b ofs =>
if Archi.ptr64 then cmp_ptr m c v1 v2 else None
| _ =>
None
end
| cmp_case_lp =>
match v1 with
| Vlong n1 =>
let v1' := Vptrofs (Ptrofs.of_int64 n1) in
cmp_ptr m c v1' v2
| Vptr b ofs =>
if Archi.ptr64 then cmp_ptr m c v1 v2 else None
| _ =>
None
end
| cmp_default =>
sem_binarith
(fun sg n1 n2 =>
Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
(fun sg n1 n2 =>
Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
(fun n1 n2 =>
Some(Val.of_bool(Float.cmp c n1 n2)))
(fun n1 n2 =>
Some(Val.of_bool(Float32.cmp c n1 n2)))
v1 t1 v2 t2 m
end.



Inductive classify_fun_cases : Type :=
| fun_case_f (targs: typelist) (tres: type) (cc: calling_convention)
| fun_default.

Definition classify_fun (ty: type) :=
match ty with
| Tfunction args res cc => fun_case_f args res cc
| Tpointer (Tfunction args res cc) _ => fun_case_f args res cc
| _ => fun_default
end.



Inductive classify_switch_cases : Type :=
| switch_case_i
| switch_case_l
| switch_default.

Definition classify_switch (ty: type) :=
match ty with
| Tint _ _ _ => switch_case_i
| Tlong _ _ => switch_case_l
| _ => switch_default
end.

Definition sem_switch_arg (v: val) (ty: type): option Z :=
match classify_switch ty with
| switch_case_i =>
match v with Vint n => Some(Int.unsigned n) | _ => None end
| switch_case_l =>
match v with Vlong n => Some(Int64.unsigned n) | _ => None end
| switch_default =>
None
end.



Definition sem_unary_operation
(op: unary_operation) (v: val) (ty: type) (m: mem): option val :=
match op with
| Onotbool => sem_notbool v ty m
| Onotint => sem_notint v ty
| Oneg => sem_neg v ty
| Oabsfloat => sem_absfloat v ty
end.

Definition sem_binary_operation
(cenv: composite_env)
(op: binary_operation)
(v1: val) (t1: type) (v2: val) (t2:type)
(m: mem): option val :=
match op with
| Oadd => sem_add cenv v1 t1 v2 t2 m
| Osub => sem_sub cenv v1 t1 v2 t2 m
| Omul => sem_mul v1 t1 v2 t2 m
| Omod => sem_mod v1 t1 v2 t2 m
| Odiv => sem_div v1 t1 v2 t2 m
| Oand => sem_and v1 t1 v2 t2 m
| Oor  => sem_or v1 t1 v2 t2 m
| Oxor  => sem_xor v1 t1 v2 t2 m
| Oshl => sem_shl v1 t1 v2 t2
| Oshr  => sem_shr v1 t1 v2 t2
| Oeq => sem_cmp Ceq v1 t1 v2 t2 m
| One => sem_cmp Cne v1 t1 v2 t2 m
| Olt => sem_cmp Clt v1 t1 v2 t2 m
| Ogt => sem_cmp Cgt v1 t1 v2 t2 m
| Ole => sem_cmp Cle v1 t1 v2 t2 m
| Oge => sem_cmp Cge v1 t1 v2 t2 m
end.

Definition sem_incrdecr (cenv: composite_env) (id: incr_or_decr) (v: val) (ty: type) (m: mem) :=
match id with
| Incr => sem_add cenv v ty (Vint Int.one) type_int32s m
| Decr => sem_sub cenv v ty (Vint Int.one) type_int32s m
end.

Definition incrdecr_type (ty: type) :=
match typeconv ty with
| Tpointer ty a => Tpointer ty a
| Tint sz sg a => Tint sz sg noattr
| Tlong sg a => Tlong sg noattr
| Tfloat sz a => Tfloat sz noattr
| _ => Tvoid
end.



Section GENERIC_INJECTION.

Variable f: meminj.
Variables m m': mem.

Hypothesis valid_pointer_inj:
forall b1 ofs b2 delta,
f b1 = Some(b2, delta) ->
Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
forall b1 ofs b2 delta,
f b1 = Some(b2, delta) ->
Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
forall b1 ofs b2 delta,
f b1 = Some(b2, delta) ->
Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_pointers_inj:
forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
b1 <> b2 ->
Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
f b1 = Some (b1', delta1) ->
f b2 = Some (b2', delta2) ->
b1' <> b2' \/
Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Remark val_inject_vtrue: forall f, Val.inject f Vtrue Vtrue.
Proof. hammer_hook "Cop" "Cop.val_inject_vtrue". unfold Vtrue; auto. Qed.

Remark val_inject_vfalse: forall f, Val.inject f Vfalse Vfalse.
Proof. hammer_hook "Cop" "Cop.val_inject_vfalse". unfold Vfalse; auto. Qed.

Remark val_inject_of_bool: forall f b, Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof. hammer_hook "Cop" "Cop.val_inject_of_bool". intros. unfold Val.of_bool. destruct b; [apply val_inject_vtrue|apply val_inject_vfalse].
Qed.

Remark val_inject_vptrofs: forall n, Val.inject f (Vptrofs n) (Vptrofs n).
Proof. hammer_hook "Cop" "Cop.val_inject_vptrofs". intros. unfold Vptrofs. destruct Archi.ptr64; auto. Qed.

Local Hint Resolve val_inject_vtrue val_inject_vfalse val_inject_of_bool val_inject_vptrofs : core.

Ltac TrivialInject :=
match goal with
| [ H: None = Some _ |- _ ] => discriminate
| [ H: Some _ = Some _ |- _ ] => inv H; TrivialInject
| [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x; TrivialInject
| [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; TrivialInject
| [ |- exists v', Some ?v = Some v' /\ _ ] => exists v; split; auto
| _ => idtac
end.

Lemma sem_cast_inj:
forall v1 ty1 ty v tv1,
sem_cast v1 ty1 ty m = Some v ->
Val.inject f v1 tv1 ->
exists tv, sem_cast tv1 ty1 ty m'= Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_cast_inj".
unfold sem_cast; intros; destruct (classify_cast ty1 ty); inv H0; TrivialInject.
- econstructor; eauto.
- erewrite weak_valid_pointer_inj by eauto. TrivialInject.
- erewrite weak_valid_pointer_inj by eauto. TrivialInject.
- destruct (ident_eq id1 id2); TrivialInject. econstructor; eauto.
- destruct (ident_eq id1 id2); TrivialInject. econstructor; eauto.
- econstructor; eauto.
Qed.

Lemma bool_val_inj:
forall v ty b tv,
bool_val v ty m = Some b ->
Val.inject f v tv ->
bool_val tv ty m' = Some b.
Proof. hammer_hook "Cop" "Cop.bool_val_inj".
unfold bool_val; intros.
destruct (classify_bool ty); inv H0; try congruence.
destruct Archi.ptr64; try discriminate.
destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1)) eqn:VP; inv H.
erewrite weak_valid_pointer_inj by eauto. auto.
destruct Archi.ptr64; try discriminate.
destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1)) eqn:VP; inv H.
erewrite weak_valid_pointer_inj by eauto. auto.
Qed.

Lemma sem_unary_operation_inj:
forall op v1 ty v tv1,
sem_unary_operation op v1 ty m = Some v ->
Val.inject f v1 tv1 ->
exists tv, sem_unary_operation op tv1 ty m' = Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_unary_operation_inj".
unfold sem_unary_operation; intros. destruct op.
-
unfold sem_notbool in *. destruct (bool_val v1 ty m) as [b|] eqn:BV; simpl in H; inv H.
erewrite bool_val_inj by eauto. simpl. TrivialInject.
-
unfold sem_notint in *; destruct (classify_notint ty); inv H0; inv H; TrivialInject.
-
unfold sem_neg in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
-
unfold sem_absfloat in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
Qed.

Definition optval_self_injects (ov: option val) : Prop :=
match ov with
| Some (Vptr b ofs) => False
| _ => True
end.

Remark sem_binarith_inject:
forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 v v1' v2',
sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m = Some v ->
Val.inject f v1 v1' -> Val.inject f v2 v2' ->
(forall sg n1 n2, optval_self_injects (sem_int sg n1 n2)) ->
(forall sg n1 n2, optval_self_injects (sem_long sg n1 n2)) ->
(forall n1 n2, optval_self_injects (sem_float n1 n2)) ->
(forall n1 n2, optval_self_injects (sem_single n1 n2)) ->
exists v', sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 m' = Some v' /\ Val.inject f v v'.
Proof. hammer_hook "Cop" "Cop.sem_binarith_inject".
intros.
assert (SELF: forall ov v, ov = Some v -> optval_self_injects ov -> Val.inject f v v).
{
intros. subst ov; simpl in H7. destruct v0; contradiction || constructor.
}
unfold sem_binarith in *.
set (c := classify_binarith t1 t2) in *.
set (t := binarith_type c) in *.
destruct (sem_cast v1 t1 t m) as [w1|] eqn:C1; try discriminate.
destruct (sem_cast v2 t2 t m) as [w2|] eqn:C2; try discriminate.
exploit (sem_cast_inj v1); eauto. intros (w1' & C1' & INJ1).
exploit (sem_cast_inj v2); eauto. intros (w2' & C2' & INJ2).
rewrite C1'; rewrite C2'.
destruct c; inv INJ1; inv INJ2; discriminate || eauto.
Qed.

Remark sem_shift_inject:
forall sem_int sem_long v1 t1 v2 t2 v v1' v2',
sem_shift sem_int sem_long v1 t1 v2 t2 = Some v ->
Val.inject f v1 v1' -> Val.inject f v2 v2' ->
exists v', sem_shift sem_int sem_long v1' t1 v2' t2 = Some v' /\ Val.inject f v v'.
Proof. hammer_hook "Cop" "Cop.sem_shift_inject".
intros. exists v.
unfold sem_shift in *; destruct (classify_shift t1 t2); inv H0; inv H1; try discriminate.
destruct (Int.ltu i0 Int.iwordsize); inv H; auto.
destruct (Int64.ltu i0 Int64.iwordsize); inv H; auto.
destruct (Int64.ltu i0 (Int64.repr 32)); inv H; auto.
destruct (Int.ltu i0 Int64.iwordsize'); inv H; auto.
Qed.

Remark sem_cmp_ptr_inj:
forall c v1 v2 v tv1 tv2,
cmp_ptr m c v1 v2 = Some v ->
Val.inject f v1 tv1 ->
Val.inject f v2 tv2 ->
exists tv, cmp_ptr m' c tv1 tv2 = Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_cmp_ptr_inj".
unfold cmp_ptr; intros.
remember (if Archi.ptr64
then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as ob.
destruct ob as [b|]; simpl in H; inv H.
exists (Val.of_bool b); split; auto.
destruct Archi.ptr64.
erewrite Val.cmplu_bool_inject by eauto. auto.
erewrite Val.cmpu_bool_inject by eauto. auto.
Qed.

Remark sem_cmp_inj:
forall cmp v1 tv1 ty1 v2 tv2 ty2 v,
sem_cmp cmp v1 ty1 v2 ty2 m = Some v ->
Val.inject f v1 tv1 ->
Val.inject f v2 tv2 ->
exists tv, sem_cmp cmp tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_cmp_inj".
intros.
unfold sem_cmp in *; destruct (classify_cmp ty1 ty2).
-
eapply sem_cmp_ptr_inj; eauto.
-
inversion H1; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
-
inversion H0; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
-
inversion H1; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
-
inversion H0; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
-
assert (SELF: forall b, optval_self_injects (Some (Val.of_bool b))).
{
destruct b; exact I.
}
eapply sem_binarith_inject; eauto.
Qed.

Lemma sem_binary_operation_inj:
forall cenv op v1 ty1 v2 ty2 v tv1 tv2,
sem_binary_operation cenv op v1 ty1 v2 ty2 m = Some v ->
Val.inject f v1 tv1 -> Val.inject f v2 tv2 ->
exists tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_binary_operation_inj".
unfold sem_binary_operation; intros; destruct op.
-
assert (A: forall cenv ty si v1' v2' tv1' tv2',
Val.inject f v1' tv1' -> Val.inject f v2' tv2' ->
sem_add_ptr_int cenv ty si v1' v2' = Some v ->
exists tv, sem_add_ptr_int cenv ty si tv1' tv2' = Some tv /\ Val.inject f v tv).
{ intros. unfold sem_add_ptr_int in *; inv H2; inv H3; TrivialInject.
econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. }
assert (B: forall cenv ty v1' v2' tv1' tv2',
Val.inject f v1' tv1' -> Val.inject f v2' tv2' ->
sem_add_ptr_long cenv ty v1' v2' = Some v ->
exists tv, sem_add_ptr_long cenv ty tv1' tv2' = Some tv /\ Val.inject f v tv).
{ intros. unfold sem_add_ptr_long in *; inv H2; inv H3; TrivialInject.
econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. }
unfold sem_add in *; destruct (classify_add ty1 ty2); eauto.
+ eapply sem_binarith_inject; eauto; intros; exact I.
-
unfold sem_sub in *; destruct (classify_sub ty1 ty2).
+ inv H0; inv H1; TrivialInject.
econstructor. eauto. rewrite Ptrofs.sub_add_l. auto.
+ inv H0; inv H1; TrivialInject.
destruct (eq_block b1 b0); try discriminate. subst b1.
rewrite H0 in H2; inv H2. rewrite dec_eq_true.
destruct (zlt 0 (sizeof cenv ty) && zle (sizeof cenv ty) Ptrofs.max_signed); inv H.
rewrite Ptrofs.sub_shifted. TrivialInject.
+ inv H0; inv H1; TrivialInject.
econstructor. eauto. rewrite Ptrofs.sub_add_l. auto.
+ eapply sem_binarith_inject; eauto; intros; exact I.
-
eapply sem_binarith_inject; eauto; intros; exact I.
-
eapply sem_binarith_inject; eauto; intros.
destruct sg.
destruct (Int.eq n2 Int.zero
|| Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
destruct (Int.eq n2 Int.zero); exact I.
destruct sg.
destruct (Int64.eq n2 Int64.zero
|| Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
destruct (Int64.eq n2 Int64.zero); exact I.
exact I.
exact I.
-
eapply sem_binarith_inject; eauto; intros.
destruct sg.
destruct (Int.eq n2 Int.zero
|| Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
destruct (Int.eq n2 Int.zero); exact I.
destruct sg.
destruct (Int64.eq n2 Int64.zero
|| Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
destruct (Int64.eq n2 Int64.zero); exact I.
exact I.
exact I.
-
eapply sem_binarith_inject; eauto; intros; exact I.
-
eapply sem_binarith_inject; eauto; intros; exact I.
-
eapply sem_binarith_inject; eauto; intros; exact I.
-
eapply sem_shift_inject; eauto.
-
eapply sem_shift_inject; eauto.

- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
Qed.

End GENERIC_INJECTION.

Lemma sem_cast_inject:
forall f v1 ty1 ty m v tv1 tm,
sem_cast v1 ty1 ty m = Some v ->
Val.inject f v1 tv1 ->
Mem.inject f m tm ->
exists tv, sem_cast tv1 ty1 ty tm = Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_cast_inject".
intros. eapply sem_cast_inj; eauto.
intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

Lemma sem_unary_operation_inject:
forall f m m' op v1 ty1 v tv1,
sem_unary_operation op v1 ty1 m = Some v ->
Val.inject f v1 tv1 ->
Mem.inject f m m' ->
exists tv, sem_unary_operation op tv1 ty1 m' = Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_unary_operation_inject".
intros. eapply sem_unary_operation_inj; eauto.
intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

Lemma sem_binary_operation_inject:
forall f m m' cenv op v1 ty1 v2 ty2 v tv1 tv2,
sem_binary_operation cenv op v1 ty1 v2 ty2 m = Some v ->
Val.inject f v1 tv1 -> Val.inject f v2 tv2 ->
Mem.inject f m m' ->
exists tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof. hammer_hook "Cop" "Cop.sem_binary_operation_inject".
intros. eapply sem_binary_operation_inj; eauto.
intros; eapply Mem.valid_pointer_inject_val; eauto.
intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
intros; eapply Mem.different_pointers_inject; eauto.
Qed.

Lemma bool_val_inject:
forall f m m' v ty b tv,
bool_val v ty m = Some b ->
Val.inject f v tv ->
Mem.inject f m m' ->
bool_val tv ty m' = Some b.
Proof. hammer_hook "Cop" "Cop.bool_val_inject".
intros. eapply bool_val_inj; eauto.
intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.







Lemma cast_bool_bool_val:
forall v t m,
sem_cast v t (Tint IBool Signed noattr) m =
match bool_val v t m with None => None | Some b => Some(Val.of_bool b) end.
intros.
assert (A: classify_bool t =
match t with
| Tint _ _ _ => bool_case_i
| Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ => if Archi.ptr64 then bool_case_l else bool_case_i
| Tfloat F64 _ => bool_case_f
| Tfloat F32 _ => bool_case_s
| Tlong _ _ => bool_case_l
| _ => bool_default
end).
{
unfold classify_bool; destruct t; simpl; auto. destruct i; auto.
}
unfold bool_val. rewrite A.
unfold sem_cast, classify_cast; remember Archi.ptr64 as ptr64; destruct t; simpl; auto; destruct v; auto.
destruct (Int.eq i0 Int.zero); auto.
destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)); auto.
destruct (Int64.eq i Int64.zero); auto.
destruct (negb ptr64); auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
destruct f; auto.
destruct f; auto.
destruct f; auto.
destruct f; auto.
destruct (Float.cmp Ceq f0 Float.zero); auto.
destruct f; auto.
destruct (Float32.cmp Ceq f0 Float32.zero); auto.
destruct f; auto.
destruct ptr64; auto.
destruct (Int.eq i Int.zero); auto.
destruct ptr64; auto.
destruct ptr64; auto.
destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
destruct ptr64; auto.
destruct ptr64; auto.
destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
destruct ptr64; auto.
destruct ptr64; auto. destruct (Int.eq i Int.zero); auto.
destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
destruct ptr64; auto.
destruct ptr64; auto.
destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
destruct ptr64; auto.
destruct ptr64; auto. destruct (Int.eq i Int.zero); auto.
destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
destruct ptr64; auto.
destruct ptr64; auto.
destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
Qed.



Lemma notbool_bool_val:
forall v t m,
sem_notbool v t m =
match bool_val v t m with None => None | Some b => Some(Val.of_bool (negb b)) end.
Proof. hammer_hook "Cop" "Cop.notbool_bool_val".
intros. unfold sem_notbool. destruct (bool_val v t m) as [[] | ]; reflexivity.
Qed.



Section VAL_CASTED.

Inductive val_casted: val -> type -> Prop :=
| val_casted_int: forall sz si attr n,
cast_int_int sz si n = n ->
val_casted (Vint n) (Tint sz si attr)
| val_casted_float: forall attr n,
val_casted (Vfloat n) (Tfloat F64 attr)
| val_casted_single: forall attr n,
val_casted (Vsingle n) (Tfloat F32 attr)
| val_casted_long: forall si attr n,
val_casted (Vlong n) (Tlong si attr)
| val_casted_ptr_ptr: forall b ofs ty attr,
val_casted (Vptr b ofs) (Tpointer ty attr)
| val_casted_int_ptr: forall n ty attr,
Archi.ptr64 = false -> val_casted (Vint n) (Tpointer ty attr)
| val_casted_ptr_int: forall b ofs si attr,
Archi.ptr64 = false -> val_casted (Vptr b ofs) (Tint I32 si attr)
| val_casted_long_ptr: forall n ty attr,
Archi.ptr64 = true -> val_casted (Vlong n) (Tpointer ty attr)
| val_casted_ptr_long: forall b ofs si attr,
Archi.ptr64 = true -> val_casted (Vptr b ofs) (Tlong si attr)
| val_casted_struct: forall id attr b ofs,
val_casted (Vptr b ofs) (Tstruct id attr)
| val_casted_union: forall id attr b ofs,
val_casted (Vptr b ofs) (Tunion id attr)
| val_casted_void: forall v,
val_casted v Tvoid.

Local Hint Constructors val_casted : core.

Remark cast_int_int_idem:
forall sz sg i, cast_int_int sz sg (cast_int_int sz sg i) = cast_int_int sz sg i.
Proof. hammer_hook "Cop" "Cop.cast_int_int_idem".
intros. destruct sz; simpl; auto.
destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
destruct (Int.eq i Int.zero); auto.
Qed.

Ltac DestructCases :=
match goal with
| [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
| [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
| [H: Some _ = Some _ |- _ ] => inv H; DestructCases
| [H: None = Some _ |- _ ] => discriminate H
| [H: @eq intsize _ _ |- _ ] => discriminate H || (clear H; DestructCases)
| [ |- val_casted (Vint (if ?x then Int.zero else Int.one)) _ ] =>
try (constructor; destruct x; reflexivity)
| [ |- val_casted (Vint _) (Tint ?sz ?sg _) ] =>
try (constructor; apply (cast_int_int_idem sz sg))
| _ => idtac
end.

Lemma cast_val_is_casted:
forall v ty ty' v' m, sem_cast v ty ty' m = Some v' -> val_casted v' ty'.
Proof. hammer_hook "Cop" "Cop.cast_val_is_casted".
unfold sem_cast; intros.
destruct ty, ty'; simpl in H; DestructCases; constructor; auto.
Qed.

End VAL_CASTED.



Lemma cast_val_casted:
forall v ty m, val_casted v ty -> sem_cast v ty ty m = Some v.
Proof. hammer_hook "Cop" "Cop.cast_val_casted".
intros. unfold sem_cast; inversion H; clear H; subst v ty; simpl.
- destruct Archi.ptr64; [ | destruct (intsize_eq sz I32)].
+ destruct sz; f_equal; f_equal; assumption.
+ subst sz; auto.
+ destruct sz; f_equal; f_equal; assumption.
- auto.
- auto.
- destruct Archi.ptr64; auto.
- auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite dec_eq_true; auto.
- rewrite dec_eq_true; auto.
- auto.
Qed.

Lemma cast_idempotent:
forall v ty ty' v' m, sem_cast v ty ty' m = Some v' -> sem_cast v' ty' ty' m = Some v'.
Proof. hammer_hook "Cop" "Cop.cast_idempotent".
intros. apply cast_val_casted. eapply cast_val_is_casted; eauto.
Qed.



Lemma val_casted_has_type:
forall v ty, val_casted v ty -> ty <> Tvoid -> Val.has_type v (typ_of_type ty).
Proof. hammer_hook "Cop" "Cop.val_casted_has_type".
intros. inv H; simpl typ_of_type.
- exact I.
- exact I.
- exact I.
- exact I.
- apply Val.Vptr_has_type.
- red; unfold Tptr; rewrite H1; auto.
- red; unfold Tptr; rewrite H1; auto.
- red; unfold Tptr; rewrite H1; auto.
- red; unfold Tptr; rewrite H1; auto.
- apply Val.Vptr_has_type.
- apply Val.Vptr_has_type.
- congruence.
Qed.



Module ArithConv.



Inductive int_type : Type :=
| _Bool
| Char | SChar | UChar
| Short | UShort
| Int | UInt
| Long | ULong
| Longlong | ULonglong.

Inductive arith_type : Type :=
| I (it: int_type)
| Float
| Double
| Longdouble.

Definition eq_int_type: forall (x y: int_type), {x=y} + {x<>y}.
Proof. hammer_hook "Cop" "Cop.ArithConv.eq_int_type". decide equality. Defined.

Definition is_unsigned (t: int_type) : bool :=
match t with
| _Bool => true
| Char => false
| SChar => false
| UChar => true
| Short => false
| UShort => true
| Int => false
| UInt => true
| Long => false
| ULong => true
| Longlong => false
| ULonglong => true
end.

Definition unsigned_type (t: int_type) : int_type :=
match t with
| Char => UChar
| SChar => UChar
| Short => UShort
| Int => UInt
| Long => ULong
| Longlong => ULonglong
| _ => t
end.

Definition int_sizeof (t: int_type) : Z :=
match t with
| _Bool | Char | SChar | UChar => 1
| Short | UShort => 2
| Int | UInt | Long | ULong => 4
| Longlong | ULonglong => 8
end.



Definition rank (t: int_type) : Z :=
match t with
| _Bool => 1
| Char | SChar | UChar => 2
| Short | UShort => 3
| Int | UInt => 4
| Long | ULong => 5
| Longlong | ULonglong => 6
end.



Definition integer_promotion (t: int_type) : int_type :=
if zlt (rank t) (rank Int) then Int else t.



Definition usual_arithmetic_conversion (t1 t2: arith_type) : arith_type :=
match t1, t2 with

| Longdouble, _ | _, Longdouble => Longdouble

| Double, _ | _, Double => Double

| Float, _ | _, Float => Float

| I i1, I i2 =>
let j1 := integer_promotion i1 in
let j2 := integer_promotion i2 in

if eq_int_type j1 j2 then I j1 else
match is_unsigned j1, is_unsigned j2 with

| true, true | false, false =>
if zlt (rank j1) (rank j2) then I j2 else I j1
| true, false =>

if zle (rank j2) (rank j1) then I j1 else

if zlt (int_sizeof j1) (int_sizeof j2) then I j2 else

I (unsigned_type j2)
| false, true =>

if zle (rank j1) (rank j2) then I j2 else
if zlt (int_sizeof j2) (int_sizeof j1) then I j1 else
I (unsigned_type j1)
end
end.



Definition proj_type (t: arith_type) : type :=
match t with
| I _Bool => Tint IBool Unsigned noattr
| I Char => Tint I8 Unsigned noattr
| I SChar => Tint I8 Signed noattr
| I UChar => Tint I8 Unsigned noattr
| I Short => Tint I16 Signed noattr
| I UShort => Tint I16 Unsigned noattr
| I Int => Tint I32 Signed noattr
| I UInt => Tint I32 Unsigned noattr
| I Long => Tint I32 Signed noattr
| I ULong => Tint I32 Unsigned noattr
| I Longlong => Tlong Signed noattr
| I ULonglong => Tlong Unsigned noattr
| Float => Tfloat F32 noattr
| Double => Tfloat F64 noattr
| Longdouble => Tfloat F64 noattr
end.



Lemma typeconv_integer_promotion:
forall i, typeconv (proj_type (I i)) = proj_type (I (integer_promotion i)).
Proof. hammer_hook "Cop" "Cop.ArithConv.typeconv_integer_promotion".
destruct i; reflexivity.
Qed.



Lemma classify_binarith_arithmetic_conversion:
forall t1 t2,
binarith_type (classify_binarith (proj_type t1) (proj_type t2)) =
proj_type (usual_arithmetic_conversion t1 t2).
Proof. hammer_hook "Cop" "Cop.ArithConv.classify_binarith_arithmetic_conversion".
destruct t1; destruct t2; try reflexivity.
- destruct it; destruct it0; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
Qed.

End ArithConv.





