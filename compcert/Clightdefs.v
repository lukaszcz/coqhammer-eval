From Hammer Require Import Hammer.


















From Coq Require Import String List ZArith.
From compcert Require Import Integers Floats Maps Errors AST Ctypes Cop Clight.

Definition tvoid := Tvoid.
Definition tschar := Tint I8 Signed noattr.
Definition tuchar := Tint I8 Unsigned noattr.
Definition tshort := Tint I16 Signed noattr.
Definition tushort := Tint I16 Unsigned noattr.
Definition tint := Tint I32 Signed noattr.
Definition tuint := Tint I32 Unsigned noattr.
Definition tbool := Tint IBool Unsigned noattr.
Definition tlong := Tlong Signed noattr.
Definition tulong := Tlong Unsigned noattr.
Definition tfloat := Tfloat F32 noattr.
Definition tdouble := Tfloat F64 noattr.
Definition tptr (t: type) := Tpointer t noattr.
Definition tarray (t: type) (sz: Z) := Tarray t sz noattr.

Definition volatile_attr := {| attr_volatile := true; attr_alignas := None |}.

Definition tattr (a: attr) (ty: type) :=
match ty with
| Tvoid => Tvoid
| Tint sz si _ => Tint sz si a
| Tlong si _ => Tlong si a
| Tfloat sz _ => Tfloat sz a
| Tpointer elt _ => Tpointer elt a
| Tarray elt sz _ => Tarray elt sz a
| Tfunction args res cc => Tfunction args res cc
| Tstruct id _ => Tstruct id a
| Tunion id  _ => Tunion id a
end.

Definition tvolatile (ty: type) := tattr volatile_attr ty.

Definition talignas (n: N) (ty: type) :=
tattr {| attr_volatile := false; attr_alignas := Some n |} ty.

Definition tvolatile_alignas (n: N) (ty: type) :=
tattr {| attr_volatile := true; attr_alignas := Some n |} ty.

Definition wf_composites (types: list composite_definition) : Prop :=
match build_composite_env types with OK _ => True | Error _ => False end.

Definition build_composite_env' (types: list composite_definition)
(WF: wf_composites types)
: { ce | build_composite_env types  = OK ce }.
Proof. hammer_hook "Clightdefs" "Clightdefs.build_composite_env'".
revert WF. unfold wf_composites. case (build_composite_env types); intros.
- exists c; reflexivity.
- contradiction.
Defined.

Definition mkprogram (types: list composite_definition)
(defs: list (ident * globdef fundef type))
(public: list ident)
(main: ident)
(WF: wf_composites types) : Clight.program :=
let (ce, EQ) := build_composite_env' types WF in
{| prog_defs := defs;
prog_public := public;
prog_main := main;
prog_types := types;
prog_comp_env := ce;
prog_comp_env_eq := EQ |}.